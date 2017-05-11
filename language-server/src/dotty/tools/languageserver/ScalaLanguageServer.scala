package dotty.tools
package languageserver

import java.net.URI
import java.nio.file._
import java.util.function._
import java.util.concurrent.CompletableFuture

import com.fasterxml.jackson.databind.ObjectMapper

import org.eclipse.lsp4j
import org.eclipse.lsp4j.jsonrpc.{CancelChecker, CompletableFutures}
import org.eclipse.lsp4j.jsonrpc.messages.{Either => JEither}
import org.eclipse.lsp4j._
import org.eclipse.lsp4j.services._

import java.util.{List => jList}
import java.util.ArrayList

import dotty.tools.dotc._
import dotty.tools.dotc.interactive._
import dotty.tools.dotc.util._
import dotty.tools.dotc.core.Contexts._
import dotty.tools.dotc.core.SymDenotations._
import dotty.tools.dotc.core._
import dotty.tools.dotc.core.Types._
import dotty.tools.dotc.core.tasty._
import dotty.tools.dotc.{ Main => DottyMain }
import dotty.tools.dotc.interfaces
import dotty.tools.dotc.reporting._
import dotty.tools.dotc.reporting.diagnostic._

import scala.collection._
import scala.collection.JavaConverters._

import scala.util.control.NonFatal

import dotty.tools.FatalError
import dotty.tools.io._
import scala.io.Codec
import dotty.tools.dotc.util.SourceFile
import java.io._

import Flags._, Symbols._, Names._, NameOps._
import core.Decorators._

import ast.Trees._

import dotty.tools.sbtplugin.config.IDEConfig

class ScalaLanguageServer extends LanguageServer with LanguageClientAware { thisServer =>
  import ast.tpd._

  import ScalaLanguageServer._
  import InteractiveDriver._

  var rewrites: dotty.tools.dotc.rewrite.Rewrites = _

  val drivers = new mutable.HashMap[IDEConfig, InteractiveDriver]

  var classPath: String = _
  var target: String = _

  var client: LanguageClient = _

  def findDriver(uri: URI): InteractiveDriver = {
    val matchingConfigs = drivers.keys.filter(config => config.sources.exists(sourceDir => uri.getRawPath.startsWith(sourceDir.getAbsolutePath.toString))).toList
    matchingConfigs match {
      case List(config) =>
        drivers(config)
      case _ =>
        assert(false, s"${uri.getRawPath} matched ${matchingConfigs}, all configs: ${drivers.keys.map(_.sources.toList.map(_.getAbsolutePath))}")
        ???
    }
  }

  def sourcePosition(driver: InteractiveDriver, uri: URI, pos: lsp4j.Position): SourcePosition = {
    val source = driver.openFiles(uri) // might throw exception
    val p = Positions.Position(source.lineToOffset(pos.getLine) + pos.getCharacter)
    new SourcePosition(source, p)
  }

  def diagnostic(cont: MessageContainer): Option[lsp4j.Diagnostic] =
    if (!cont.pos.exists)
      None
    else {
      def severity(level: Int): DiagnosticSeverity = level match {
        case interfaces.Diagnostic.INFO => DiagnosticSeverity.Information
        case interfaces.Diagnostic.WARNING => DiagnosticSeverity.Warning
        case interfaces.Diagnostic.ERROR => DiagnosticSeverity.Error
      }

      val di = new lsp4j.Diagnostic
      di.setSeverity(severity(cont.level))
      if (cont.pos.exists) di.setRange(ScalaLanguageServer.range(cont.pos))
      di.setCode("0")
      di.setMessage(cont.message)

      Some(di)
    }

  override def connect(client: LanguageClient): Unit = {
    this.client = client
  }

  override def exit(): Unit = {
    System.exit(0)
  }
  override def shutdown(): CompletableFuture[Object] = {
    CompletableFuture.completedFuture(new Object)
  }

  def computeAsync[R](fun: CancelChecker => R): CompletableFuture[R] =
    CompletableFutures.computeAsync({(cancelToken: CancelChecker) =>
      // We do not support any concurrent use of the compiler currently.
      thisServer.synchronized {
        cancelToken.checkCanceled()
        try {
          fun(cancelToken)
        } catch {
          case NonFatal(ex) =>
            ex.printStackTrace
            throw ex
        }
      }
    })

  override def initialize(params: InitializeParams): CompletableFuture[InitializeResult] = computeAsync { cancelToken =>

    // Get rid of it after https://github.com/emacs-lsp/lsp-mode/issues/84 is fixed.
    val rootUri = Option(params.getRootUri).getOrElse("file://" + params.getRootPath)

    val configs: List[IDEConfig] = (new ObjectMapper).readValue(new JFile(new URI(rootUri + "/.dotty-ide.json")), classOf[Array[IDEConfig]]).toList

    val defaultFlags = List(/*"-Yplain-printer","-Yprintpos"*/)
    for (config <- configs) {
      drivers.put(config, new InteractiveDriver(defaultFlags ++ config.scalacArgs.toList ++ List("-classpath", (config.target +: config.depCp).mkString(":"))))
    }


    val c = new ServerCapabilities
    c.setTextDocumentSync(TextDocumentSyncKind.Full)
    c.setDocumentHighlightProvider(true)
    c.setDocumentSymbolProvider(true)
    c.setDefinitionProvider(true)
    c.setRenameProvider(true)
    c.setHoverProvider(true)
    c.setWorkspaceSymbolProvider(true)
    c.setReferencesProvider(true)
    c.setCompletionProvider(new CompletionOptions(
      /* resolveProvider = */ false,
      /* triggerCharacters = */ List(".").asJava))

    new InitializeResult(c)
  }

  override def getTextDocumentService(): TextDocumentService = new TextDocumentService {
    override def codeAction(params: CodeActionParams): CompletableFuture[jList[_ <: Command]] = null
    override def codeLens(params: CodeLensParams): CompletableFuture[jList[_ <: CodeLens]] = null
    // FIXME: share code with messages.NotAMember
    override def completion(params: TextDocumentPositionParams) = computeAsync { cancelToken =>
      val uri = new URI(params.getTextDocument.getUri)
      val driver = findDriver(uri)
      implicit val ctx = driver.ctx

      val trees = driver.trees
      val spos = sourcePosition(driver, uri, params.getPosition)
      val decls = Interactive.completions(trees, spos)

      val items = decls.map({ decl =>
        val item = new CompletionItem
        item.setLabel(decl.name.show.toString)
        item.setDetail(decl.info.widenTermRefExpr.show.toString)
        item.setKind(completionItemKind(decl))
        item
      })

      JEither.forRight(new CompletionList(/*isIncomplete = */ false, items.asJava))
    }
    override def definition(params: TextDocumentPositionParams) = computeAsync { cancelToken =>
      val uri = new URI(params.getTextDocument.getUri)
      val driver = findDriver(uri)
      implicit val ctx = driver.ctx

      val trees = driver.trees
      val spos = sourcePosition(driver, uri, params.getPosition)
      val sym = Interactive.enclosingSymbol(trees, spos)
      val defs = Interactive.definitions(trees, sym, namePosition = true, allowApproximation = true)
      defs.map(location).asJava
    }
    override def didChange(params: DidChangeTextDocumentParams): Unit = thisServer.synchronized {
      val document = params.getTextDocument
      val uri = URI.create(document.getUri)
      val driver = findDriver(uri)

      val path = Paths.get(uri)
      val change = params.getContentChanges.get(0)
      assert(change.getRange == null, "TextDocumentSyncKind.Incremental support is not implemented")
      val text = change.getText

      val diags = driver.run(uri, text)


      client.publishDiagnostics(new PublishDiagnosticsParams(
        document.getUri,
        diags.flatMap(diagnostic).asJava))
    }
    override def didClose(params: DidCloseTextDocumentParams): Unit = thisServer.synchronized {
      val document = params.getTextDocument
      val uri = URI.create(document.getUri)

      findDriver(uri).close(uri)
    }
    override def didOpen(params: DidOpenTextDocumentParams): Unit = thisServer.synchronized {
      val document = params.getTextDocument
      val uri = URI.create(document.getUri)
      val driver = findDriver(uri)
      val path = Paths.get(uri)
      val text = params.getTextDocument.getText

      val diags = driver.run(uri, text)

      client.publishDiagnostics(new PublishDiagnosticsParams(
        document.getUri,
        diags.flatMap(diagnostic).asJava))
    }
    override def didSave(params: DidSaveTextDocumentParams): Unit = /*thisServer.synchronized*/ {}
    override def documentHighlight(params: TextDocumentPositionParams): CompletableFuture[jList[_ <: DocumentHighlight]] = computeAsync { cancelToken =>
      val document = params.getTextDocument
      val uri = URI.create(document.getUri)
      val driver = findDriver(uri)

      implicit val ctx = driver.ctx

      val uriTrees = driver.trees.filter(tree => toUri(tree.source) == uri)

      val pos = sourcePosition(driver, new URI(params.getTextDocument.getUri), params.getPosition)

      val trees = driver.trees
      val sym = Interactive.enclosingSymbol(trees, pos) 
      val refs = Interactive.references(trees, sym)

      refs.map(ref => new DocumentHighlight(range(ref), DocumentHighlightKind.Read)).asJava
    }
    override def documentSymbol(params: DocumentSymbolParams): CompletableFuture[jList[_ <: SymbolInformation]] = computeAsync { cancelToken =>
      val document = params.getTextDocument
      val uri = URI.create(document.getUri)
      val driver = findDriver(uri)

      implicit val ctx = driver.ctx

      val uriTrees = driver.trees.filter(tree => toUri(tree.source) == uri)

      val syms = Interactive.allDefinitions(uriTrees)
      syms.map({case (sym, spos) => symbolInfo(sym, spos)}).asJava
    }
    override def hover(params: TextDocumentPositionParams): CompletableFuture[Hover] = computeAsync { cancelToken =>
      val uri = new URI(params.getTextDocument.getUri)
      val driver = findDriver(uri)

      implicit val ctx = driver.ctx

      val pos = sourcePosition(driver, uri, params.getPosition)
      val tp = Interactive.enclosingType(driver.trees, pos)

      val str = tp.widenTermRefExpr.show.toString

      new Hover(List(JEither.forLeft[String, MarkedString](str)).asJava, null)
    }

    override def formatting(params: DocumentFormattingParams): CompletableFuture[jList[_ <: TextEdit]] = null
    override def rangeFormatting(params: DocumentRangeFormattingParams): CompletableFuture[jList[_ <: TextEdit]] = null
    override def onTypeFormatting(params: DocumentOnTypeFormattingParams): CompletableFuture[jList[_ <: TextEdit]] = null

    override def references(params: ReferenceParams): CompletableFuture[jList[_ <: Location]] = computeAsync { cancelToken =>
      val uri = new URI(params.getTextDocument.getUri)
      val driver = findDriver(uri)
      implicit val ctx = driver.ctx

      val pos = sourcePosition(driver, uri, params.getPosition)

      val trees = driver.trees
      val sym = Interactive.enclosingSymbol(trees, pos) 
      val refs = Interactive.references(trees, sym, params.getContext.isIncludeDeclaration)(driver.ctx)

      refs.map(location).asJava
    }
    override def rename(params: RenameParams): CompletableFuture[WorkspaceEdit] = computeAsync { cancelToken =>
      val uri = new URI(params.getTextDocument.getUri)
      val driver = findDriver(uri)
      implicit val ctx = driver.ctx

      val trees = driver.trees
      val pos = sourcePosition(driver, uri, params.getPosition)


      val sym = Interactive.enclosingSymbol(trees, pos)
      val linkedSym = sym.linkedClass

      val newName = params.getNewName

      val poss = Interactive.references(trees, sym) ++ Interactive.references(trees, linkedSym)

      val changes = poss.groupBy(pos => toUri(pos.source).toString).mapValues(_.map(pos => new TextEdit(nameRange(pos, sym.name), newName)).asJava)

      new WorkspaceEdit(changes.asJava)
    }
    override def resolveCodeLens(params: CodeLens): CompletableFuture[CodeLens] = null
    override def resolveCompletionItem(params: CompletionItem): CompletableFuture[CompletionItem] = null
    override def signatureHelp(params: TextDocumentPositionParams): CompletableFuture[SignatureHelp] = null
  }

  override def getWorkspaceService(): WorkspaceService = new WorkspaceService {
    override def didChangeConfiguration(params: DidChangeConfigurationParams): Unit = /*thisServer.synchronized*/ {}
    override def didChangeWatchedFiles(params: DidChangeWatchedFilesParams): Unit = /*thisServer.synchronized*/ {}
    override def symbol(params: WorkspaceSymbolParams): CompletableFuture[jList[_ <: SymbolInformation]] = computeAsync { cancelToken =>
      val query = params.getQuery

      drivers.values.flatMap(driver => {
        implicit val ctx = driver.ctx

        val syms = Interactive.allDefinitions(driver.trees, filter = query)
        syms.map({case (sym, spos) => symbolInfo(sym, spos)})
      }).toList.asJava
    }
  }
}

object ScalaLanguageServer {
  import ast.tpd._
  import InteractiveDriver._

  def nameRange(p: SourcePosition, name: Name): Range = {
    val nameLength = name.stripModuleClassSuffix.toString.length
    val (beginName, endName) =
      if (p.pos.isSynthetic)
        (p.pos.end - nameLength, p.pos.end)
      else
        (p.pos.point, p.pos.point + nameLength)

    new Range(
      new Position(p.source.offsetToLine(beginName), p.source.column(beginName)),
      new Position(p.source.offsetToLine(endName), p.source.column(endName))
    )
  }

  def range(p: SourcePosition): Range =
    new Range(
      new Position(p.startLine, p.startColumn),
      new Position(p.endLine, p.endColumn)
    )

  def location(p: SourcePosition) =
    new Location(toUri(p.source).toString, range(p))

  def symbolKind(sym: Symbol)(implicit ctx: Context) =
    if (sym.is(Package))
      SymbolKind.Package
    else if (sym.isConstructor)
      SymbolKind.Constructor
    else if (sym.isClass)
      SymbolKind.Class
    else if (sym.is(Mutable))
      SymbolKind.Variable
    else if (sym.is(Method))
      SymbolKind.Method
    else
      SymbolKind.Field

  def completionItemKind(sym: Symbol)(implicit ctx: Context) =
    if (sym.is(Package))
      CompletionItemKind.Module // No CompletionItemKind.Package
    else if (sym.isConstructor)
      CompletionItemKind.Constructor
    else if (sym.isClass)
      CompletionItemKind.Class
    else if (sym.is(Mutable))
      CompletionItemKind.Variable
    else if (sym.is(Method))
      CompletionItemKind.Method
    else
      CompletionItemKind.Field

  def symbolInfo(sym: Symbol, spos: SourcePosition)(implicit ctx: Context) = {
    val s = new SymbolInformation
    s.setName(sym.name.show.toString)
    s.setKind(symbolKind(sym))
    s.setLocation(location(spos))
    if (sym.owner.exists && !sym.owner.isEmptyPackage)
      s.setContainerName(sym.owner.name.show.toString)
    s
  }
}
