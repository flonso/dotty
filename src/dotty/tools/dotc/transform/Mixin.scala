package dotty.tools.dotc
package transform

import core._
import TreeTransforms._
import Contexts.Context
import Flags._
import SymUtils._
import Symbols._
import SymDenotations._
import Types._
import Decorators._
import DenotTransformers._
import StdNames._
import NameOps._
import ast.Trees._
import util.Positions._
import collection.mutable

// todo: interface
/** This phase performs the following transformations:
 *
 *  1. (done in `traitDefs`) Map every concrete trait field
 *
 *       <mods> val x: T = expr
 *
 *   to the pair of definitions:
 *
 *       <mods> val x: T
 *       protected def initial$x: T = { stats; expr }
 *
 *   where `stats` comprises all statements between either the start of the trait
 *   or the previous field definition which are not definitions (i.e. are executed for
 *   their side effects).
 *
 *   2. (done in `traitDefs`) Make every concrete trait setter
 *
 *      <mods> def x_=(y: T) = ()
 *
 *     deferred by maping it to
 *
 *      <mods> def x_=(y: T)
 *
 *   3. For a non-trait class C:
 *
 *        For every trait M directly implemented by the class (see SymUtils.mixin), in
 *        reverse linearization order, add the following definitions to C:
 *
 *          3.1 (done in `traitInits`) For every concrete trait field `<mods> val x: T` in M,
 *              in order of textual occurrence:
 *
 *                <mods> val x: T = super[M].initial$x
 *
 *          3.2 (done in `constrCall`) The call:
 *
 *                super[M].<init>
 *
 *          3.3 (done in `setters`) For every concrete setter `<mods> def x_=(y: T)` in M:
 *
 *                <mods> def x_=(y: T) = ()
 *
 *          3.4 (done in `superAccessors`) For every superAccessor
 *              `<mods> def super$f[Ts](ps1)...(psN): U` in M:
 *
 *                <mods> def super$f[Ts](ps1)...(psN): U = super[S].f[Ts](ps1)...(psN)
 *
 *              where `S` is the superclass of `M` in the linearization of `C`.
 *
 *          3.5 (done in `methodOverrides`) For every method
 *              `<mods> def f[Ts](ps1)...(psN): U` in M` that needs to be disambiguated:
 *
 *                <mods> def f[Ts](ps1)...(psN): U = super[M].f[Ts](ps1)...(psN)
 *
 *        A method in M needs to be disambiguated if it is concrete, not overridden in C,
 *        and if it overrides another concrete method.
 */
class Mixin extends MiniPhaseTransform with SymTransformer { thisTransform =>
  import ast.tpd._

  override def phaseName: String = "mixin"

  override def treeTransformPhase = thisTransform.next

  override def transformSym(sym: SymDenotation)(implicit ctx: Context): SymDenotation =
    if ((sym.isField || sym.isSetter) && sym.owner.is(Trait) && !sym.is(Deferred))
      sym.copySymDenotation(initFlags = sym.flags | Deferred)
    else
      sym

  private val MethodOrDeferred = Method | Deferred
  private val PrivateOrDeferred = Private | Deferred

  private def initializer(sym: Symbol)(implicit ctx: Context): TermSymbol = {
    val initName = InitializerName(sym.name.asTermName)
    sym.owner.info.decl(initName).symbol
      .orElse(
        ctx.newSymbol(
          sym.owner,
          initName,
          Protected | Synthetic | Method,
          ExprType(sym.info),
          coord = sym.symbol.coord).enteredAfter(thisTransform))
       .asTerm
  }

  override def transformTemplate(impl: Template)(implicit ctx: Context, info: TransformerInfo) = {
    val cls = impl.symbol.owner.asClass
    def superCls = cls.classInfo.parents.head.symbol

    def traitDefs(stats: List[Tree]): List[Tree] = {
      val initBuf = new mutable.ListBuffer[Tree]
      stats flatMap {
        case stat: ValDef if !stat.rhs.isEmpty =>
          val vsym = stat.symbol
          val isym = initializer(vsym)
          val rhs = Block(
            initBuf.toList.map(_.changeOwner(impl.symbol, isym)),
            stat.rhs.changeOwner(vsym, isym).ensureConforms(isym.info.widen))
          initBuf.clear()
          List(
            cpy.ValDef(stat)(mods = stat.mods | Deferred, rhs = EmptyTree),
            DefDef(isym, rhs))
        case stat: DefDef if stat.symbol.isSetter =>
          List(cpy.DefDef(stat)(
            mods = stat.mods | Deferred,
            rhs = EmptyTree))
        case stat: DefTree =>
          List(stat)
        case stat =>
          initBuf += stat
          Nil
      }
    }

    def superRef(target: Symbol, pos: Position = cls.pos): Tree = {
      val sup = if (target.isConstructor && !target.owner.is(Trait))
        Super(This(cls), tpnme.EMPTY, true)
      else
        Super(This(cls), target.owner.name.asTypeName, false, target.owner)
      //println(i"super ref $target on $sup")
      ast.untpd.Select(sup, target.name).withType(NamedType.withFixedSym(sup.tpe, target))
      //sup.select(target)
    }

    def transformSuper(tree: Tree): Tree = tree match {
      case tree @ Select(New(_), nme.CONSTRUCTOR) => superRef(tree.symbol, tree.pos)
      case Apply(fn, args) => cpy.Apply(fn)(transformSuper(fn), args)
      case TypeApply(fn, args) => cpy.TypeApply(fn)(transformSuper(fn), args)
    }

    val superCalls = (
      for (p <- impl.parents if p.symbol.isConstructor) yield p.symbol.owner -> transformSuper(p)
    ).toMap

    def superCallOpt(baseCls: Symbol): List[Tree] = superCalls.get(baseCls) match {
      case Some(call) =>
        if (defn.PhantomClasses.contains(baseCls)) Nil else call :: Nil
      case None =>
        if (baseCls.is(Interface) || defn.PhantomClasses.contains(baseCls)) Nil
        else {
          //println(i"synth super call ${baseCls.primaryConstructor}: ${baseCls.primaryConstructor.info}")
          superRef(baseCls.primaryConstructor, cls.pos)
            .appliedToTypes(cls.thisType.baseTypeWithArgs(baseCls).argTypes)
            .ensureApplied :: Nil
/*          constr.tpe.widen match {
            case tpe: PolyType =>
              val targs = cls.thisType.baseTypeWithArgs(baseCls).argTypes
              constr = constr.appliedToTypes(targs)
            case _ =>
          }
          constr.ensureApplied :: Nil
*/
        }
    }

    def wasDeferred(sym: Symbol) =
      ctx.atPhase(thisTransform) { implicit ctx => sym is Deferred }

    def implementation(member: TermSymbol): TermSymbol = {
      val res = member.copy(
        owner = cls,
        name = member.name.stripScala2LocalSuffix,
        flags = member.flags &~ Deferred &~ Module,
        info = cls.thisType.memberInfo(member)
      ).enteredAfter(thisTransform).asTerm
      assert(!res.is(Module))
      res
    }

    def forwarder(target: Symbol) = (targs: List[Type]) => (vrefss: List[List[Tree]]) =>
      superRef(target).appliedToTypes(targs).appliedToArgss(vrefss)

    /** Returns the symbol that is accessed by a super-accessor in a mixin composition.
     *
     *  @param base       The class in which everything is mixed together
     *  @param member     The symbol statically referred to by the superaccessor in the trait
     */
    def rebindSuper(base: Symbol, acc: Symbol): Symbol = {
      var bcs = cls.info.baseClasses.dropWhile(acc.owner != _).tail
      var sym: Symbol = NoSymbol
      val SuperAccessorName(memberName) = acc.name
      ctx.debuglog(i"starting rebindsuper from $cls of ${acc.showLocated} in $bcs, name = $memberName")
      while (!bcs.isEmpty && sym == NoSymbol) {
        val other = bcs.head.info.nonPrivateDecl(memberName)
        if (ctx.settings.debug.value)
          ctx.debuglog("rebindsuper " + bcs.head + " " + other + " " + other.info +
            " " + other.symbol.is(Deferred))
        sym = other.matchingDenotation(cls.thisType, cls.thisType.memberInfo(acc)).symbol
        bcs = bcs.tail
      }
      assert(sym.exists)
      sym
    }

    def superAccessors(mixin: ClassSymbol): List[Tree] =
      for (superAcc <- mixin.decls.filter(_ is SuperAccessor).toList)
        yield polyDefDef(implementation(superAcc.asTerm), forwarder(rebindSuper(cls, superAcc)))

    def traitInits(mixin: ClassSymbol): List[Tree] =
      for (field <- mixin.decls.filter(fld => fld.isField && !wasDeferred(fld)).toList)
        yield ValDef(implementation(field.asTerm), superRef(initializer(field)))

    def setters(mixin: ClassSymbol): List[Tree] =
      for (setter <- mixin.decls.filter(setr => setr.isSetter && !wasDeferred(setr)).toList)
        yield DefDef(implementation(setter.asTerm), unitLiteral.withPos(cls.pos))

    def methodOverrides(mixin: ClassSymbol): List[Tree] = {
      def isOverridden(meth: Symbol) = meth.overridingSymbol(cls).is(Method, butNot = Deferred)
      def needsDisambiguation(meth: Symbol): Boolean =
        meth.is(Method, butNot = PrivateOrDeferred) &&
          !isOverridden(meth) &&
          !meth.allOverriddenSymbols.forall(_ is Deferred)
      for (meth <- mixin.decls.toList if needsDisambiguation(meth))
        yield polyDefDef(implementation(meth.asTerm), forwarder(meth))
    }

    cpy.Template(impl)(
      parents = impl.parents.map(p => TypeTree(p.tpe).withPos(p.pos)),
      body =
        if (cls is Trait) traitDefs(impl.body)
        else {
          val mixins = cls.baseClasses.tail.takeWhile(_ ne superCls).reverse
          val mixInits = mixins.flatMap { mixin =>
            assert(mixin is Trait)
            traitInits(mixin) :::
              superCallOpt(mixin) :::
              setters(mixin) :::
              superAccessors(mixin) :::
              methodOverrides(mixin)
          }
          superCallOpt(superCls) ::: mixInits ::: impl.body
        })
  }
}