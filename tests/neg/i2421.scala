inline object Foo // error: inlined keyword cannot be used on object
inline class Bar // error: inlined keyword cannot be used on class
inline abstract class Baz // error: inlined keyword cannot be used on abstract class
inline trait Qux // error: inlined keyword cannot be used on trait

object Quux {
  inline type T // error: inlined keyword cannot be used on type
  inline var x: Int = 42 // error: inlined keyword cannot be used on var
  inline lazy val y: Int = 42 // error: inlined keyword cannot be used on lazy val
}
