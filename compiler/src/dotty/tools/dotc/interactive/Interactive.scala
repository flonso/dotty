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

import Positions._

import ast.{NavigateAST, untpd, tpd}

/** High-level API to get information out of typed trees, designed to be used by IDEs.
 *
 *  @see `InteractiveDriver` to get typed trees from code.
 */
object Interactive {
  import ast.tpd._

  /** Filter for names that should appear when looking for completions. */
  private[this] object completionsFilter extends NameFilter {
    def apply(pre: Type, name: Name)(implicit ctx: Context): Boolean =
      !name.isConstructorName
  }

  /** The reverse path to the node that closest encloses position `spos`,
   *  or `Nil` if no such path exists. If a non-empty path is returned it starts with
   *  the tree closest enclosing `pos` and ends with an element of `trees`.
   */
  def pathTo(trees: List[SourceTree], spos: SourcePosition)(implicit ctx: Context): List[Tree] =
    trees.find({ case SourceTree(source, t) =>
      source == spos.source && t.pos.contains(spos.pos)
    }).toList.flatMap(stree => {
      // FIXME: We shouldn't need a cast. Change NavigateAST.pathTo to return a List of Tree?
      val path = NavigateAST.pathTo(spos.pos, stree.tree).asInstanceOf[List[untpd.Tree]]

      path.dropWhile(!_.hasType).asInstanceOf[List[tpd.Tree]]
    })

  /** The type of the closest enclosing tree containing position `spos`. */
  def enclosingType(trees: List[SourceTree], spos: SourcePosition)(implicit ctx: Context): Type = {
    val path = pathTo(trees, spos)
    path.headOption.fold(NoType: Type)(_.tpe)
  }

  /** The symbol of the closest enclosing tree containing position `spos`.
   *
   *  If that symbol is a class local dummy, return the class symbol instead.
   */
  def enclosingSymbol(trees: List[SourceTree], spos: SourcePosition)(implicit ctx: Context): Symbol = {
    val path = pathTo(trees, spos)
    path.headOption.fold(NoSymbol: Symbol)(tree => nonLocalDummy(tree.symbol))
  }

  /** If `sym` is a local dummy, the corresponding class symbol, otherwise `sym` */
  def nonLocalDummy(sym: Symbol)(implicit ctx: Context): Symbol = if (sym.isLocalDummy) {
    println("##dummy in: " + sym.owner)
    assert(false)
    sym.owner
  } else sym

  /** The first tree in the path that is a definition. */
  def enclosingDefinitionInPath(path: List[Tree])(implicit ctx: Context): Tree =
    path.find(_.isInstanceOf[DefTree]).getOrElse(EmptyTree)

  /** Possible completions at position `spos` */
  def completions(trees: List[SourceTree], spos: SourcePosition)(implicit ctx: Context): List[Symbol] = {
    val path = pathTo(trees, spos)
    val boundary = enclosingDefinitionInPath(path).symbol

    path.take(1).flatMap {
      case Select(qual, _) =>
        // When completing "`a.foo`, return the members of `a`
        completions(qual.tpe, boundary)
      case _ =>
        // FIXME: Get all decls in current scope
        boundary.enclosingClass match {
          case csym: ClassSymbol =>
            val classRef = csym.classInfo.typeRef
            completions(classRef, boundary)
          case _ =>
            Nil
        }
    }
  }

  /** Possible completions of members of `prefix` which are legal when called from `boundary` */
  def completions(prefix: Type, boundary: Symbol)(implicit ctx: Context): List[Symbol] = {
    val boundaryCtx = ctx.withOwner(boundary)
    prefix.memberDenots(completionsFilter, (name, buf) =>
      buf ++= prefix.member(name).altsWith(_.symbol.isAccessibleFrom(prefix)(boundaryCtx))
    ).map(_.symbol).toList
  }

  private[this] def positionedAccumulator[T](trees: List[SourceTree], maybeAdd: (NameTree, SourcePosition, mutable.ListBuffer[T]) => Unit, namePosition: Boolean)
      (implicit ctx: Context): List[T] = {
    val buf = new mutable.ListBuffer[T]

    trees foreach { case SourceTree(sourceFile, tree) =>
      (new TreeTraverser {
        override def traverse(tree: Tree)(implicit ctx: Context) = {
          tree match {
            case tree: NameTree
                if tree.symbol.exists && !tree.symbol.is(Synthetic) && tree.pos.exists && tree.pos.start != tree.pos.end =>
              maybeAdd(tree, new SourcePosition(sourceFile, displayedPos(tree, namePosition)), buf)
            case _ =>
          }
          traverseChildren(tree)
        }
      }).traverse(tree)
    }

    buf.toList
  }

  def definitions(trees: List[SourceTree], sym: Symbol, namePosition: Boolean = true,
    allowApproximation: Boolean = false)(implicit ctx: Context): List[SourcePosition] = {
    val poss = new mutable.ListBuffer[SourcePosition]

    if (!sym.exists)
      Nil
    else {
      // Type annotation not needed when compiling with dotty
      val res = positionedAccumulator[SourcePosition](trees,
        (tree, spos, buf) =>
          if (tree.isInstanceOf[MemberDef] && matchingSymbol(tree, sym))
            buf += spos,
        namePosition)
      if (res.isEmpty && allowApproximation) {
        definitions(trees, nonLocalDummy(sym.owner), namePosition, allowApproximation).take(1)
      } else res
    }
  }

  def allDefinitions(trees: List[SourceTree], filter: String = "", namePosition: Boolean = true)(implicit ctx: Context): List[(Symbol, SourcePosition)] =
    positionedAccumulator[(Symbol, SourcePosition)](trees,
      (tree, spos, buf) =>
        if (tree.isInstanceOf[MemberDef] && tree.name.show.toString.contains(filter))
          buf += ((tree.symbol, spos)),
      namePosition)

  /** Find all references to `sym` or to a symbol overriding `sym`
   *  @param includeDeclaration  If true, include the declaration of `sym` itself
   */
  def references(trees: List[SourceTree], sym: Symbol, includeDeclaration: Boolean = true, namePosition: Boolean = true)
    (implicit ctx: Context): List[SourcePosition] = {
    if (!sym.exists)
      Nil
    else
      positionedAccumulator[SourcePosition](trees,
        (tree, spos, buf) =>
          if ((includeDeclaration || !(tree.isInstanceOf[MemberDef] && (tree.symbol eq sym))) && matchingSymbol(tree, sym))
            buf += spos,
        namePosition)
  }

  def allReferences(trees: List[SourceTree], filter: String = "", namePosition: Boolean = true)
      (implicit ctx: Context): List[(Symbol, SourcePosition)] = {
      positionedAccumulator[(Symbol, SourcePosition)](trees,
        (tree, spos, buf) =>
        if (tree.name.show.toString.contains(filter))
          buf += ((tree.symbol, spos)),
        namePosition)
  }

  /** Does `tree` refer to symbol `sym` or to a symbol that overrides `sym` ? */
  private[this] def matchingSymbol(tree: Tree, sym: Symbol)(implicit ctx: Context): Boolean =
    (sym eq tree.symbol) || tree.symbol.allOverriddenSymbols.contains(sym)

  /** Return the position to be displayed. If `namePosition` is true, this is the position of
   *  the name inside `tree`, otherwise it's the position of `tree` itself.
   */
  private[this] def displayedPos(tree: NameTree, namePosition: Boolean)(implicit ctx: Context): Position = {
    val treePos = tree.pos
    val nameLength = tree.name.stripModuleClassSuffix.show.toString.length
    if (namePosition) {
      // FIXME: This is incorrect in some cases, like with backquoted identifiers,
      //        see https://github.com/lampepfl/dotty/pull/1634#issuecomment-257079436
      // FIXME: Merge with NameTree#namePos ?
      val (start, end) =
        if (!treePos.isSynthetic)
          (treePos.point, treePos.point + nameLength)
        else
          // If we don't have a point, we need to find it
          (treePos.end - nameLength, treePos.end)
      Position(start, end, start)
    } else
      treePos
  }
}
