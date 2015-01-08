package dotty.tools.dotc.transform

import java.io.{FileOutputStream, BufferedOutputStream, BufferedWriter}

import dotty.tools.dotc.ast.Trees.GenericApply
import dotty.tools.dotc.ast.{untpd, tpd, Trees}
import dotty.tools.dotc.core.Constants.Constant
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.Symbols
import Symbols._
import dotty.tools.dotc.core.pickling.PickleBuffer
import dotty.tools.dotc.transform.TreeTransforms._
import tpd._
import dotty.tools.dotc.core.Types._

import scala.collection.immutable.SortedMap
import scala.collection.mutable
import scala.collection.mutable.{ArrayBuffer, ArrayBuilder}
import scala.runtime.BoxedUnit

class Serialize extends MiniPhaseTransform {
  def phaseName: String = "Serialize"
  val serializer: LowLevelSerializer = new BinarySerializer

  val symbolOffsetsAprox = new mutable.HashMap[Symbol, Int]()

  val annotationTransformer = mkTreeTransformer // used to recurse into annotations
  var annotationLevel = 0

  def writeString(str: String): Unit = {
    serializer.writeStringId(str)
  }

  def writeConst(c: Constant) = {
    serializer.writeConstantId(c)
  }

  def writeAnnots(t: DefTree): Unit = ()

  import serializer._

  def writeType(tp: Type)(implicit ctx: Context): Unit = {
    tp match {
      case AnnotatedType(annot, tpe) =>
        writeNodeHeader(tp)
        annotationLevel += 1
        annotationTransformer.macroTransform(annot.tree)
        annotationLevel -= 1
        writeType(tpe)
      case t: ThisType =>
        annotationLevel += 1
        annotationTransformer.macroTransform(tpd.This(t.cls))
        annotationLevel -= 1
      case t: SingletonType =>
        annotationLevel += 1
        annotationTransformer.macroTransform(tpd.ref(t.termSymbol))
        annotationLevel -= 1
      case t: AndOrType =>
        writeNodeHeader(tp)
        writeType(t.tp1)
        writeType(t.tp2)
      case t @ TypeRef(prefix, name) =>
        writeNodeHeader(tp)
        writeType(prefix)
        serializer.writeSymbolRef(t.typeSymbol)

    }
  }

  def singleRefTree(tree: Tree)(implicit ctx: Context) = {
    writeNodeHeader(tree)
    serializer.writeSymbolRef(tree.symbol)
    this
  }

  def noActualFields(tree: Tree, writeSize: Boolean)(implicit ctx: Context) = {
    writeNodeHeader(tree)
    this
  }

  // c
  override def prepareForIdent(tree: Ident)(implicit ctx: Context) = singleRefTree(tree)
  // r
  override def prepareForSelect(tree: Select)(implicit ctx: Context) = singleRefTree(tree)
  // c
  override def prepareForThis(tree: This)(implicit ctx: Context): TreeTransform = singleRefTree(tree)

  override def prepareForSuper(tree: tpd.Super)(implicit ctx: Context): TreeTransform = {
    writeNodeHeader(tree)
    serializer.writeSymbolRef(tree.qual.symbol)
    serializer.writeSymbolRef(tree.symbol.owner) // todo: check that this indeed returns `mix`
    this
  }

  def sizedTree(tree: Tree, args: Int)(implicit ctx: Context): TreeTransform = {
    writeNodeHeader(tree)
    putSizeField(tree)
    this
  }

  def closeSizedTree(tree: Tree)(implicit ctx: Context): Tree = {
    closeSizeField(tree)
    tree
  }

  override def prepareForApply(tree: tpd.Apply)(implicit ctx: Context): TreeTransform = sizedTree(tree, tree.args.size)

  override def transformApply(tree: tpd.Apply)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = closeSizedTree(tree)

  override def prepareForTypeApply(tree: tpd.TypeApply)(implicit ctx: Context): TreeTransform = sizedTree(tree, tree.args.size)

  override def transformTypeApply(tree: tpd.TypeApply)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = closeSizedTree(tree)

  override def prepareForLiteral(tree: tpd.Literal)(implicit ctx: Context): TreeTransform = {
    writeNodeHeader(tree)
    writeConst(tree.const)
    this
  }


  override def prepareForPair(tree: tpd.Pair)(implicit ctx: Context): TreeTransform = {
    writeNodeHeader(tree)
    writeString(tree.left.show)
    writeString(tree.right.show)
    this
  }

  override def prepareForNew(tree: tpd.New)(implicit ctx: Context): TreeTransform = noActualFields(tree, writeSize = false)

  override def prepareForTyped(tree: tpd.Typed)(implicit ctx: Context): TreeTransform = noActualFields(tree, writeSize = true)

  override def transformTyped(tree: tpd.Typed)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = closeSizedTree(tree)

  override def prepareForAssign(tree: tpd.Assign)(implicit ctx: Context): TreeTransform = noActualFields(tree, writeSize = true)


  override def transformAssign(tree: tpd.Assign)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = closeSizedTree(tree)

  override def prepareForBlock(tree: tpd.Block)(implicit ctx: Context): TreeTransform = sizedTree(tree, tree.stats.size + 1)

  override def transformBlock(tree: tpd.Block)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = closeSizedTree(tree)

  override def prepareForIf(tree: tpd.If)(implicit ctx: Context): TreeTransform = noActualFields(tree, writeSize = true)

  override def transformIf(tree: tpd.If)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = closeSizedTree(tree)

  override def prepareForClosure(tree: tpd.Closure)(implicit ctx: Context): TreeTransform = sizedTree(tree, tree.env.size)

  override def transformClosure(tree: tpd.Closure)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = closeSizedTree(tree)

  override def prepareForMatch(tree: tpd.Match)(implicit ctx: Context): TreeTransform = sizedTree(tree, tree.cases.size)

  override def transformMatch(tree: tpd.Match)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = closeSizedTree(tree)

  override def prepareForCaseDef(tree: tpd.CaseDef)(implicit ctx: Context): TreeTransform = noActualFields(tree, writeSize = true)

  override def transformCaseDef(tree: tpd.CaseDef)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = closeSizedTree(tree)

  override def prepareForReturn(tree: tpd.Return)(implicit ctx: Context): TreeTransform = noActualFields(tree, writeSize = true)

  override def transformReturn(tree: tpd.Return)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = closeSizedTree(tree)

  override def prepareForTry(tree: tpd.Try)(implicit ctx: Context): TreeTransform = sizedTree(tree, tree.cases.size)

  override def transformTry(tree: tpd.Try)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = closeSizedTree(tree)

  override def prepareForThrow(tree: tpd.Throw)(implicit ctx: Context): TreeTransform = noActualFields(tree, writeSize = true)

  override def transformThrow(tree: tpd.Throw)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = closeSizedTree(tree)

  override def prepareForSeqLiteral(tree: tpd.SeqLiteral)(implicit ctx: Context): TreeTransform = sizedTree(tree, tree.elems.size)

  override def transformSeqLiteral(tree: tpd.SeqLiteral)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = closeSizedTree(tree)

  override def prepareForTypeTree(tree: tpd.TypeTree)(implicit ctx: Context): TreeTransform = {
    writeType(tree.tpe)
    this
  }

  override def prepareForSelectFromTypeTree(tree: tpd.SelectFromTypeTree)(implicit ctx: Context): TreeTransform = singleRefTree(tree)

  override def prepareForBind(tree: tpd.Bind)(implicit ctx: Context): TreeTransform = {
    writeNodeHeader(tree)
    writeString(tree.name.toString)
    writeBoolean(tree.name.isTypeName)
    this
  }

  override def prepareForAlternative(tree: tpd.Alternative)(implicit ctx: Context): TreeTransform = sizedTree(tree, tree.trees.size)

  override def prepareForTypeDef(tree: tpd.TypeDef)(implicit ctx: Context): TreeTransform = {
    symbolOffsetsAprox.put(tree.symbol, currentOffset)
    writeNodeHeader(tree)
    putSizeField(tree)
    writeAnnots(tree)
    writeString(tree.name.toString)
    this
  }


  override def transformTypeDef(tree: tpd.TypeDef)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = closeSizedTree(tree)

  override def prepareForUnApply(tree: tpd.UnApply)(implicit ctx: Context): TreeTransform = {
    writeNodeHeader(tree)
    writeArgsCount(tree.implicits.size)
    putSizeField(tree)
    this
  }


  override def transformUnApply(tree: tpd.UnApply)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = closeSizedTree(tree)

  override def prepareForValDef(tree: tpd.ValDef)(implicit ctx: Context): TreeTransform = {
    symbolOffsetsAprox.put(tree.symbol, currentOffset)
    writeNodeHeader(tree)
    putSizeField(tree)
    writeAnnots(tree)
    writeString(tree.name.toString)
    this
  }


  override def transformValDef(tree: tpd.ValDef)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = closeSizedTree(tree)

  override def prepareForDefDef(tree: tpd.DefDef)(implicit ctx: Context): TreeTransform = {
    symbolOffsetsAprox.put(tree.symbol, currentOffset)
    writeNodeHeader(tree)
    putSizeField(tree)
    writeAnnots(tree)
    writeString(tree.name.toString)
    writeArgsCount(tree.tparams.size)
    writeArgsCount(tree.vparamss.size)
    for(i <- tree.vparamss)
      writeArgsCount(i.size)
    this
  }

  override def transformDefDef(tree: tpd.DefDef)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = closeSizedTree(tree)

  override def prepareForTemplate(tree: tpd.Template)(implicit ctx: Context): TreeTransform = {
    writeNodeHeader(tree)
    putSizeField(tree)
    writeArgsCount(tree.parents.size)
    // writeArgsCount(tree.body.size) // to be replaced by tree size
    this
  }


  override def transformTemplate(tree: tpd.Template)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = closeSizedTree(tree)

  override def prepareForPackageDef(tree: tpd.PackageDef)(implicit ctx: Context): TreeTransform = {
    writeNodeHeader(tree)
    putSizeField(tree)
    writeString(tree.pid.symbol.showFullName)
    // writeArgsCount(tree.stats.size) // to be replaced by tree size
    this
  }


  override def transformPackageDef(tree: tpd.PackageDef)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = closeSizedTree(tree)

  override def prepareForUnit(tree: tpd.Tree)(implicit ctx: Context): TreeTransform = {
    if(annotationLevel == 0) serializer.init(tree)
    this
  }


  override def transformUnit(tree: tpd.Tree)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    if(annotationLevel == 0) flush(tree)
    tree
  }

  trait LowLevelSerializer {
    def init(unit: tpd.Tree): Unit
    def writeSymbolRef(sym: Symbol): Unit
    def writeNodeHeader(nd: Any /* Tree | Type */): Unit
    def putSizeField(t: Tree): Unit
    def closeSizeField(t: Tree): Unit
    def writeArgsCount(count: Int): Unit
    def writeStringId(str: String): Unit
    def writeConstantId(str: Constant): Unit
    def writeBoolean(value: Boolean): Unit
    def currentOffset: Int
    def flush(tree: Tree): Unit
  }

  class BinarySerializer extends LowLevelSerializer {

    val verifyClosing: Boolean = true


    val treesToBeClozed = new mutable.Stack[Tree]()
    def putSizeField(t: Tree): Unit = {
      starts += trees.writeIndex
      sizes += -1
      if(verifyClosing) treesToBeClozed.push(t)
    }
    
    def serializedSizeOfNat(int: Int): Int = {
      assert(int > 0)
      var acc = 1
      var j = int
      while(j!=0) {
        acc += 1
        j = j >>> 7
      }
      acc
    }

    def closeSizeField(t: Tree): Unit = {
      // to be rewritten to index lookup
      if(verifyClosing) {
        val toBeClosedNext = treesToBeClozed.pop()
        assert(t eq toBeClosedNext)
      }
      val idx = sizes.lastIndexOf(-1)
      var size = trees.writeIndex - starts(idx)
      var j = idx + 1
      while(j < sizes.length) {
        /**
         * Find the first index of element that doesn't compare less than key, otherwise -1
         */
        def lowerBound(key: Int, start: Int, length: Int): Int = {
          var len = length - start
          var first = start
          while (len > 0) {
            val half = len >>> 1
            val middle = first + half
            if (starts(middle) < key) {
              first = middle + 1
              len = len - half - 1
            } else {
              len = half
            }
          }
          if (first < length)
            first
          else
            -1
        }

        assert(sizes(j) != -1)
        size += serializedSizeOfNat(sizes(j))
        val nextSizeStart = lowerBound(starts(j) + sizes(j), j, starts.length)
        if(nextSizeStart > 0)
          j = nextSizeStart
        else j = sizes.length
      }
      sizes(idx) = size
    }

    val current = 0
    // there could be a class Line(start, end, next) here, but I've done (array-of-structs -> struct of arrays) by hand,
    // knowing that start[i] = end[i-1]

    val starts = new mutable.ArrayBuffer[Int] // this is boxed. could be reimplemented for speed
    val sizes = new mutable.ArrayBuffer[Int]()
    val trees = new PickleBuffer(new Array[Byte](1024), 0, 0)
    val MAGIC = 0x000A11CE
    val VERSION = 0
    val compilerName = "Dotty 0.0"
    val compilerNameBytes = compilerName.getBytes("UTF-8")
    val referencesSectionName = "references"
    val referencesSectionNameBytes = referencesSectionName.getBytes("UTF-8")
    val treesSectionName = "trees"
    val treesSectionNameBytes = treesSectionName.getBytes("UTF-8")
    val constantsSectionName = "constants"
    val constantsSectionNameBytes = constantsSectionName.getBytes("UTF-8")
    val stringsSectionName = "strings"
    val stringsSectionNameBytes = stringsSectionName.getBytes("UTF-8")


    def flush(tree: Tree): Unit = {
      val output = new PickleBuffer(new Array[Byte](2048), 0, 0)
      output.writeRawInt(MAGIC)
      output.writeRawInt(VERSION)


      def writeAE(bt: Array[Byte], st: Int, until: Int): Unit = {
        output.writeRawInt(until - st)
        output.writeBytes(bt, st, until - st)
      }
      def writeByteArray(bt: Array[Byte]): Unit = writeAE(bt, 0, bt.size)
      def writePB(pb: PickleBuffer): Unit = writeAE(pb.bytes, 0, pb.writeIndex)


      writeByteArray(compilerNameBytes)

      writeByteArray(constantsSectionNameBytes)
      writePB(serializedConstants)

      writeByteArray(stringsSectionNameBytes)
      writePB(serializedStrings)

      def flushTrees: Unit = {
        var nextSizeIdx = 0

        var copiedUntil = 0
        while(nextSizeIdx < sizes.length) {
          writeAE(trees.bytes, copiedUntil, starts(nextSizeIdx))
          copiedUntil = starts(nextSizeIdx)
          output.writeNat(sizes(nextSizeIdx))
          nextSizeIdx = nextSizeIdx + 1
        }
        writeAE(trees.bytes, copiedUntil, trees.writeIndex)
      }

      writeByteArray(treesSectionNameBytes)
      flushTrees

      val f = java.io.File.createTempFile("serializedTree", ".tasty")
      f.createNewFile()
      println(s"flushed tree: $tree to " + f.getCanonicalPath)
      val d = new BufferedOutputStream(new FileOutputStream(f))
      d.write(output.bytes, 0, output.writeIndex)
      d.close()
    }


    def init(unit: tpd.Tree): Unit = {

    }

    val serializedSymbols = new PickleBuffer(new Array[Byte](1024), 0, 0)
    val symbolOffsets = new mutable.HashMap[Symbol, Int]()


    def writeSymbolRef(sym: Symbol): Unit = {
      trees.writeNat(333333)
    }

    def serializeSymbol(sym: Symbol): Unit = {

    }

    def writeModifiersId(mod: tpd.Modifiers, idx: Int): Unit = ()

    val serializedStrings = new PickleBuffer(new Array[Byte](1024), 0, 0)
    val stringOffsets = new mutable.HashMap[String, Int]()


    def addString(str: String): Int = {
      val data = str.getBytes("UTF-8")
      val cur = serializedStrings.writeIndex
      serializedStrings.writeRawInt(data.length)
      serializedStrings.writeBytes(data)
      cur
    }

    def writeStringId(str: String): Unit = {
      val id = stringOffsets.getOrElseUpdate(str, addString(str))
      trees.writeNat(id)
    }

    val serializedConstants = new PickleBuffer(new Array[Byte](1024), 0, 0)
    val constantOffsets = new mutable.HashMap[Any, Int]()

    def serializeConstant(c: Constant): Array[Byte] = {
      import dotty.tools.dotc.core.Constants._
      c.tag match {
        case UnitTag => Array.apply(0.toByte)
        case NullTag      => Array.apply(1.toByte)
        case BooleanTag if c.booleanValue      => Array.apply(2.toByte)
        case BooleanTag if !c.booleanValue     => Array.apply(3.toByte)
        case ByteTag   => Array.apply(4.toByte, c.byteValue)
        case ShortTag  => 
          val s = c.shortValue
          Array.apply(5.toByte, ((s >>> 8) & 0xFF).toByte, (s & 0xFF).toByte)
        case CharTag   =>
          val a = c.charValue
          Array.apply(6.toByte, a.toString.getBytes("UTF-8"): _*)
        case IntTag =>
          val i = c.intValue
          Array.apply(7.toByte, ((i >>> 24) & 0xFF).toByte, ((i >>> 16) & 0xFF).toByte, ((i >>> 8) & 0xFF).toByte, (i & 0xFF).toByte)
        case LongTag =>
          val l = c.longValue
          Array.apply(8.toByte,
          ((l >>> 56) & 0xFF).toByte, ((l >>> 48) & 0xFF).toByte, ((l >>> 40) & 0xFF).toByte, ((l >>> 32) & 0xFF).toByte,
          ((l >>> 24) & 0xFF).toByte, ((l >>> 16) & 0xFF).toByte, ((l >>> 8) & 0xFF).toByte, (l & 0xFF).toByte)
        case FloatTag =>
          val i = java.lang.Float.floatToIntBits(c.floatValue)
          Array.apply(9.toByte, ((i >>> 24) & 0xFF).toByte, ((i >>> 16) & 0xFF).toByte, ((i >>> 8) & 0xFF).toByte, (i & 0xFF).toByte)
        case DoubleTag    =>
          val l = java.lang.Double.doubleToRawLongBits(c.doubleValue)
          Array.apply(10.toByte,
            ((l >>> 56) & 0xFF).toByte, ((l >>> 48) & 0xFF).toByte, ((l >>> 40) & 0xFF).toByte, ((l >>> 32) & 0xFF).toByte,
            ((l >>> 24) & 0xFF).toByte, ((l >>> 16) & 0xFF).toByte, ((l >>> 8) & 0xFF).toByte, (l & 0xFF).toByte)
        case StringTag =>
          val a = c.stringValue
          val i = stringOffsets.getOrElseUpdate(a, addString(a))
          Array.apply(11.toByte, ((i >>> 24) & 0xFF).toByte, ((i >>> 16) & 0xFF).toByte, ((i >>> 8) & 0xFF).toByte, (i & 0xFF).toByte)
        case ClazzTag =>
          ???
        case EnumTag =>
          ???
      }
    }

    def writeConstantId(str: Constant): Unit = {
      val id = constantOffsets.getOrElseUpdate(str, {
        val data = serializeConstant(str)
        val cur = serializedConstants.writeIndex
        serializedConstants.writeBytes(data)
        cur
      })
      trees.writeNat(id)
    }

    def currentOffset: Int = 0

    def writeNodeHeader(nd: Any/* Tree | Type */): Unit = {
      val id = (nd: @unchecked) match {
        case EmptyTree => 0
        case _: Ident @unchecked => 1
        case _: Select @unchecked | _: TypeRef => 2
        case _: This @unchecked => 3
        case _: Super @unchecked => 4
        case _: Apply @unchecked => 5
        case _: UnApply @unchecked => 6
        case _: NamedArg @unchecked => 7
        case _: SeqLiteral @unchecked => 8
        case _: TypeApply @unchecked => 9
        case _: Literal @unchecked => 10
        case _: New @unchecked => 11
        case _: Typed @unchecked => 12
        case _: Assign @unchecked => 13
        case _: Block @unchecked => 14
        case _: If @unchecked => 15
        case _: Closure @unchecked => 16
        case _: Match @unchecked => 17
        case _: CaseDef @unchecked => 18
        case _: Return @unchecked => 19
        case _: Try @unchecked => 20
        case _: Throw @unchecked => 21
        case _: Bind  @unchecked => 22
        case _: Alternative @unchecked  => 23
       //24 is annotation
        case _: ValDef @unchecked => 25
        case _: DefDef @unchecked => 26
        case _: TypeDef @unchecked => 27
        //case _: moduleDef => 28 moduleDef
        case _: Template @unchecked => 29
        case _: PackageDef @unchecked => 30
        case _: Import @unchecked => 31
        case _: Pair @unchecked => 32
        case _: AnnotatedType @unchecked => 33
        case _: SingletonType @unchecked => 34
        case _: SelectFromTypeTree @unchecked => 35
        case _: AndType @unchecked => 36
        case _: OrType @unchecked => 37
        case _: RefinedType @unchecked => 38
        case _: ByNameTypeTree @unchecked => 39
        //case _: RepeatedType => 40
        case _: TypeBounds @unchecked => 41
        //case _: ExistentialType => 42
        //case _: AppliedType => 43
      }
      trees.writeByte(id)
    }

    def writeBoolean(value: Boolean): Unit = {
      if(value) trees.writeByte(1)
      else trees.writeByte(0)
    }

    def writeArgsCount(count: Int): Unit = {
      trees.writeNat(count)
    }
  }
}