/* Copyright 2009-2013 EPFL, Lausanne */

object MyTuple2 {

  abstract class A
  case class B(i: Int) extends A
  case class C(a: A) extends A

  def foo(): Int = {
    val t = (B(2), C(B(3)))
    t match {
      case (B(x), C(y)) => x
    }
  } ensuring( _ == 3)

}
