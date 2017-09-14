package scala.scalanative
package optimizer
package pass

import analysis.ClassHierarchy.Top
import nir._
import scala.scalanative.nir.Inst.Let
import tools._

class InliningTest extends OptimizerSpec {

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
      Some(Driver.empty.withPasses(Seq(MethodLowering, CopyPropagation, Inlining, AnnotatedInliningCheck)))
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
      Some(Driver.empty.withPasses(Seq(MethodLowering, CopyPropagation, Inlining, ConstructorInliningCheck)))
    optimize("A$", code, driver) { case (_, _, _) => () }
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

  private object ConstructorInliningCheck extends PassCompanion {
    override def apply(config: Config, top: Top): Pass = new ConstructorInliningCheck
  }

  private object AnnotatedInliningCheck extends PassCompanion {
    override def apply(config: Config, top: Top): Pass = new AnnotatedInliningCheck
  }
}
