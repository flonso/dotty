package dotty.tools
package dotc
package parsing

import scala.reflect.io._
import util._
import core._
import scala.io.Codec
import Tokens._, Parsers._
import ast.untpd._
import org.junit.Test
import scala.collection.mutable.ListBuffer

class ParserTest extends DottyTest {

  def parse(name: String): Tree = parse(new PlainFile(name))

  var parsed = 0
  val parsedTrees = new ListBuffer[Tree]

  def reset() = {
    parsed = 0
    parsedTrees.clear()
  }

  def parse(file: PlainFile): Tree = {
    //println("***** parsing " + file)
    val source = new SourceFile(file, Codec.UTF8)
    val parser = new Parser(source)
    val tree = parser.parse()
    parsed += 1
    parsedTrees += tree
    tree
  }

  def parseDir(path: String): Unit = parseDir(Directory(path))

  def parseDir(dir: Directory): Unit = {
    for (f <- dir.files)
      if (f.name.endsWith(".scala")) parse(new PlainFile(f))
    for (d <- dir.dirs)
      parseDir(d.path)
  }
}
