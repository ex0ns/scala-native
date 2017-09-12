package scala.scalanative
package optimizer
package pass

import analysis.ClassHierarchy.Top
import nir._
import scala.scalanative.nir.Inst.Let
import tools._

class InliningTest extends OptimizerSpec {

  it should "inline all occurrences of add5" in {
    val driver =
      Some(Driver.empty.withPasses(Seq(MethodLowering, CopyPropagation, Inlining, InliningCheck)))
    optimize("A$", code, driver) { case (_, _, _) => () }
  }

  private val code = """
                       | object B {
                       |   @inline def add5(i: Int) = i + 5
                       | }
                       | object A {
                       |  def main(args: Array[String]): Unit =
                       |    println(B.add5(6))
                       |}""".stripMargin

  private class InliningCheck extends Pass {
    override def onInst(inst: Inst): Inst = inst match {
      case Let(_, Op.Call(Type.Function(_, _), Val.Global(global, _), _, _))  =>
        if(global.show.contains("add5")) fail("Found a call to add5")
        inst
      case _ => inst
    }
  }

  private object InliningCheck extends PassCompanion {
    override def apply(config: Config, top: Top): Pass = new InliningCheck
  }
}
