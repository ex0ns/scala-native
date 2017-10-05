package scala.scalanative
package optimizer
package pass

import analysis.ClassHierarchy.Top
import nir._
import scala.scalanative.nir.Inst.Let
import tools._

class InliningTest extends OptimizerSpec {

  private val commonPasses = Seq(MethodLowering, CopyPropagation, Inlining)

  it should "inline all occurrences of add5" in {
    val code = """
                         | object B {
                         |   @inline def add5(i: Int) = i + 5
                         | }
                         | object A {
                         |  def main(args: Array[String]): Unit =
                         |    println(B.add5(6))
                         |}""".stripMargin
    val driver =
      Some(Driver.empty.withPasses(commonPasses :+ AnnotatedInliningCheck))
    optimize("A$", code, driver) { case (_, _, _) => () }
  }

  it should "inline constructor" in {
    val code = """
                 | class B {
                 |   @inline def add5(i: Int) = i + 5
                 | }
                 | class C(start: Int) {
                 |  @inline def add(i: Int) = start + i
                 | }
                 | object A {
                 |  def main(args: Array[String]): Unit = {
                 |    println(new B().add5(6))
                 |    println(new C(6).add(5))
                 |  }
                 |}""".stripMargin

    val driver =
      Some(Driver.empty.withPasses(commonPasses :+ ConstructorInliningCheck))
    optimize("A$", code, driver) { case (_, _, _) => () }
  }

  it should "inline accessor (get)" in {
    val code = """
                 | class B {
                 |  var content = 5
                 |  val contentRO = 6
                 | }
                 | object A {
                 |  def main(args: Array[String]): Unit = {
                 |    val b = new B()
                 |    println(b.content)
                 |    println(b.contentRO)
                 |  }
                 |}""".stripMargin

    val driverWithInlining =
      Some(Driver.empty.withPasses(commonPasses :+ AccessorsInliningCheck))
    optimize("A$", code, driverWithInlining) { case (_, _, _) => () }
  }

  it should "fail if not get is not inlined" in {
    val code = """
                 | class B {
                 |  var content = 5
                 |  val contentRO = 6
                 | }
                 | object A {
                 |  def main(args: Array[String]): Unit = {
                 |    val b = new B()
                 |    println(b.content)
                 |    println(b.contentRO)
                 |  }
                 |}""".stripMargin

    val driverWithoutInlining =
      Some(Driver.empty.withPasses(Seq(MethodLowering, CopyPropagation, AccessorsInliningCheck)))

    val failure = intercept[Exception] {
      optimize("A$", code, driverWithoutInlining) { case (_, _, _) => () }
    }

    assert(failure.getMessage.indexOf("Found a call to") != -1)
  }

  it should "inline accessor (set)" in {
    val code = """
                 | class B {
                 |  var content = 5
                 | }
                 | object A {
                 |  def main(args: Array[String]): Unit = {
                 |    val b = new B()
                 |    b.content = 10
                 |  }
                 |}""".stripMargin
    val driverWithInlining =
      Some(Driver.empty.withPasses(commonPasses :+ AccessorsInliningCheck))
    optimize("A$", code, driverWithInlining) { case (_, _, _) => () }
  }

  it should "should fail if setter is not inlined" in {
    val code = """
                 | class B {
                 |  var content = 5
                 | }
                 | object A {
                 |  def main(args: Array[String]): Unit = {
                 |    val b = new B()
                 |    b.content = 10
                 |  }
                 |}""".stripMargin

    val driverWithoutInlining =
      Some(Driver.empty.withPasses(Seq(MethodLowering, CopyPropagation, AccessorsInliningCheck)))

    val failure = intercept[Exception] {
      optimize("A$", code, driverWithoutInlining) { case (_, _, _) => () }
    }

    assert(failure.getMessage.indexOf("Found a call to") != -1)
  }

  it should "inline tuple pattern match" in {
    val code = """
                 | case class Foo(content: Int, content1: Int)
                 |
                 | object A {
                 |  def main(args: Array[String]): Unit = {
                 |    val foo = Foo(1, 3)
                 |    val Foo(content, content1) = foo
                 |    println(content)
                 |    println(content1)
                 |  }
                 |}""".stripMargin

    val driverWithoutInlining =
      Some(Driver.empty.withPasses(Seq(MethodLowering, CopyPropagation, TupleInliningCheck)))


    val failure = intercept[Exception] {
      optimize("A$", code, driverWithoutInlining) { case (_, _, _) => () }
    }

    assert(failure.getMessage.indexOf("Found a call to") != -1)

    val driverWithInlining =
      Some(Driver.empty.withPasses(Seq(MethodLowering, CopyPropagation, Inlining, TupleInliningCheck)))
    optimize("A$", code, driverWithInlining) { case (_, _, _) => () }
  }

  private class ConstructorInliningCheck extends Pass {
    override def onInst(inst: Inst): Inst = inst match {
      case Let(_, Op.Call(Type.Function(_, _), Val.Global(global, _), _, _))  =>
        if(global.show.contains("C::init") || global.show.contains("B::init"))
          fail(s"Found a call to constructor ${global.show}")
        inst
      case _ => inst
    }
  }

  private class AnnotatedInliningCheck extends Pass {
    override def onInst(inst: Inst): Inst = inst match {
      case Let(_, Op.Call(Type.Function(_, _), Val.Global(global, _), _, _))  =>
        if(global.show.contains("add5")) fail("Found a call to add5")
        inst
      case _ => inst
    }
  }

  private class AccessorsInliningCheck extends Pass {
    override def onInst(inst: Inst): Inst = {
      inst match {
        case Let(_, Op.Call(Type.Function(_, _), Val.Global(global, _), _, _)) =>
          if(global.show.contains("content")) fail(s"Found a call to accessor ${inst.show}")
          inst
        case _ => inst
      }
    }
  }

  private class TupleInliningCheck extends Pass {
    override def onInst(inst: Inst): Inst = {
      inst match {
        case Let(_, Op.Call(Type.Function(_, _), Val.Global(global, _), _, _)) =>
          if(global.show.contains("content") || global.show.contains("Foo::"))
            fail(s"Found a call to accessor ${inst.show}")
          inst
        case _ => inst
      }
    }
  }


  private object ConstructorInliningCheck extends PassCompanion {
    override def apply(config: Config, top: Top): Pass = new ConstructorInliningCheck
  }

  private object AnnotatedInliningCheck extends PassCompanion {
    override def apply(config: Config, top: Top): Pass = new AnnotatedInliningCheck
  }

  private object AccessorsInliningCheck extends PassCompanion {
    override def apply(config: Config, top: Top): Pass = new AccessorsInliningCheck
  }

  private object TupleInliningCheck extends PassCompanion {
    override def apply(config: Config, top: Top): Pass = new TupleInliningCheck
  }
}
