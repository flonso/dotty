package dotty.tools
package dotc
package interactive

import java.net.URI
import java.nio.file._
import java.util.function._
import java.util.concurrent.CompletableFuture

import java.util.{List => jList}
import java.util.ArrayList

import dotty.tools.dotc._
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
import dotty.tools.dotc.classpath.ClassPathEntries

import scala.collection._
import scala.collection.JavaConverters._

import dotty.tools.FatalError
import dotty.tools.io._
import scala.io.Codec
import dotty.tools.dotc.util.SourceFile
import java.io._

import Flags._, Symbols._, Names._, NameOps._
import core.Decorators._

import ast.Trees._

case class SourceTree(source: SourceFile, tree: ast.tpd.Tree)

/** A Driver subclass designed to be used from IDEs */
class InteractiveDriver(settings: List[String], val compiler: Compiler) extends Driver {
  import ast.tpd._
  import InteractiveDriver._

  override protected def newCompiler(implicit ctx: Context): Compiler = ???
  override def sourcesRequired = false

  private val myInitCtx: Context = {
    val rootCtx = initCtx.fresh.addMode(Mode.ReadPositions)
    rootCtx.setSetting(rootCtx.settings.YretainTrees, true)
    setup(settings.toArray, rootCtx)._2
  }

  private var myCtx: Context = myInitCtx

  implicit def ctx: Context = myCtx

  private val openClasses = new mutable.LinkedHashMap[URI, List[String]]

  private val myOpenFiles = new mutable.LinkedHashMap[URI, SourceFile]

  def openFiles: Map[URI, SourceFile] = myOpenFiles


  private def tree(className: String): Option[SourceTree] = {
    if (className == "scala.annotation.internal.SourceFile")
      None // FIXME: No SourceFile annotation on SourceFile itself
    else {
      val clsd = ctx.base.staticRef(className.toTypeName)
      clsd match {
        case clsd: ClassDenotation =>
          clsd.info // force denotation
          if (!clsd.isAbsent) {
            val tree = clsd.symbol.tree
            if (tree != null) {
              val sourceFile = new SourceFile(clsd.symbol.sourceFile, Codec.UTF8)
              Some(SourceTree(sourceFile, tree))
            } else None
          } else None
        case _ =>
          sys.error(s"class not found: $className")
      }
    }
  }

  // FIXME: wrong when classpath changes
  private lazy val tastyClasses = {
    def classNames(cp: ClassPath, packageName: String): List[String] = {
      val ClassPathEntries(pkgs, classReps) = cp.list(packageName)

      classReps
        .filter((classRep: ClassRepresentation) => classRep.binary match {
          case None =>
            true
          case Some(binFile) =>
            val prefix =
              if (binFile.name.endsWith("$.class"))
                binFile.name.stripSuffix("$.class")
              else if (binFile.name.endsWith(".class"))
                binFile.name.stripSuffix(".class")
              else
                null
            prefix != null && {
              val tastyFile = prefix + ".tasty"
              binFile match {
                case ze: FileZipArchive#Entry =>
                  val Some(archive: FileZipArchive) = ze.underlyingSource
                  val dir = archive.allDirs(ZipArchive.dirName(ze.path))
                  dir.entries.contains(tastyFile)
                case pf: PlainFile =>
                  val tastyPath = pf.givenPath.parent / tastyFile
                  tastyPath.exists
              }
            }
        })
        .map(classRep => (packageName ++ (if (packageName != "") "." else "") ++ classRep.name)).toList ++
        pkgs.flatMap(pkg => classNames(cp, pkg.name))
    }

    classNames(ctx.platform.classPath, "")
  }

  def trees: List[SourceTree] = {
    val sourceClasses = openClasses.values.flatten.toList
    val otherClasses = tastyClasses.filter(tastyClass =>
      !sourceClasses.exists(sourceClass =>
        tastyClass.toTypeName.stripModuleClassSuffix.toString == sourceClass.toTypeName.stripModuleClassSuffix.toString))

    (sourceClasses ++ otherClasses).flatMap(tree)
  }

  private def topLevelClassNames(tree: Tree): List[String] = {
    val names = new mutable.ListBuffer[String]
    object extract extends TreeTraverser {
      override def traverse(tree: Tree)(implicit ctx: Context): Unit = tree match {
        case t: PackageDef =>
          traverseChildren(t)
        case t @ TypeDef(_, tmpl : Template) =>
          names += t.symbol.fullName.toString
        case _ =>
      }
    }
    extract.traverse(tree)
    names.toList
  }

  private def newReporter: Reporter =
    new StoreReporter(null) with UniqueMessagePositions with HideNonSensicalMessages

  def run(uri: URI, sourceCode: String): List[MessageContainer] = {
    try {
      val reporter = newReporter
      val run = compiler.newRun(myInitCtx.fresh.setReporter(reporter))
      myCtx = run.runContext

      val virtualFile = new VirtualFile(uri.toString, Paths.get(uri).toString)
      val writer = new BufferedWriter(new OutputStreamWriter(virtualFile.output, "UTF-8"))
      writer.write(sourceCode)
      writer.close()
      val sourceFile = new SourceFile(virtualFile, Codec.UTF8)
      myOpenFiles(uri) = sourceFile

      val basePath = "/home/florian/Desktop/EPFL/Master/sav/project/stainless/"
      val stainlessLibraryFiles = List(
                          basePath + """./frontends/library/stainless/math/package.scala""",
                          basePath + """./frontends/library/stainless/proof/package.scala""",
                          basePath + """./frontends/library/stainless/proof/Internal.scala""",
                          basePath + """./frontends/library/stainless/io/FileOutputStream.scala""",
                          basePath + """./frontends/library/stainless/io/package.scala""",
                          basePath + """./frontends/library/stainless/io/StdIn.scala""",
                          basePath + """./frontends/library/stainless/io/FileInputStream.scala""",
                          basePath + """./frontends/library/stainless/io/StdOut.scala""",
                          basePath + """./frontends/library/stainless/annotation/isabelle.scala""",
                          basePath + """./frontends/library/stainless/annotation/package.scala""",
                          basePath + """./frontends/library/stainless/collection/List.scala""",
                          basePath + """./frontends/library/stainless/lang/Bag.scala""",
                          basePath + """./frontends/library/stainless/lang/StrOps.scala""",
                          basePath + """./frontends/library/stainless/lang/Map.scala""",
                          basePath + """./frontends/library/stainless/lang/Set.scala""",
                          basePath + """./frontends/library/stainless/lang/package.scala""",
                          basePath + """./frontends/library/stainless/lang/StaticChecks.scala""",
                          basePath + """./frontends/library/stainless/lang/Either.scala""",
                          basePath + """./frontends/library/stainless/lang/Option.scala""",
                          basePath + """./frontends/library/stainless/lang/Real.scala""",
                          basePath + """./frontends/library/stainless/lang/Rational.scala""",
                          basePath + """./frontends/library/stainless/lang/synthesis/Oracle.scala""",
                          basePath + """./frontends/library/stainless/lang/synthesis/package.scala""",
                          basePath + """./frontends/library/stainless/util/Random.scala"""
  ).map(x => new SourceFile(dotty.tools.io.AbstractFile.getFile(x), Codec.UTF8))
      run.compileSources( stainlessLibraryFiles ++ List(sourceFile))
      run.printSummary()
      val t = run.units.head.tpdTree
      openClasses(uri) = topLevelClassNames(t)

      reporter.removeBufferedMessages
    }
    catch {
      case ex: FatalError  =>
        ctx.error(ex.getMessage) // signals that we should fail compilation.
        close(uri)
        Nil
    }
  }

  def close(uri: URI): Unit = {
    myOpenFiles.remove(uri)
    openClasses.remove(uri)
  }
}

object InteractiveDriver {
  def toUri(source: SourceFile) = Paths.get(source.file.path).toUri
}

