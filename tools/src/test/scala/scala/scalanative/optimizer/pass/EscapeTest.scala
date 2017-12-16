package scala.scalanative
package optimizer
package pass

import scala.scalanative.nir.Inst.Let
import scala.scalanative.nir.{Inst, Op, Type, Val}
import scala.scalanative.optimizer.analysis.ClassHierarchy.Top
import scala.scalanative.tools.Config

class EscapeTest extends OptimizerSpec {

  private val className = "SimplestClassEver"
  private val commonPasses =
    Seq(Inlining, MethodLowering, CopyPropagation, EscapeAnalysis)
  private val classAllocDriver = Some(
    Driver.empty.withPasses(commonPasses :+ ClassAllocChecker))
  private val stackAllocDriver = Some(
    Driver.empty.withPasses(commonPasses :+ StackAllocChecker))

  private def shouldClassAlloc(code: String) = {
    val failure = intercept[Exception] {
      optimize("Main$", code, classAllocDriver) { case (_, _, _) => () }
    }

    assert(failure.getMessage.indexOf("Found a call to") != -1)

    optimize("Main$", code, stackAllocDriver) { case (_, _, _) => () }
  }

  private def shouldStackAlloc(code: String) = {
    val failure = intercept[Exception] {
      optimize("Main$", code, stackAllocDriver) { case (_, _, _) => () }
    }

    assert(failure.getMessage.indexOf("Found a call to") != -1)

    optimize("Main$", code, classAllocDriver) { case (_, _, _) => () }
  }

  it should "Should allocate object on the stack if it doesn't escape" in {
    val code = s"""
                  |object Main {
                  |  def main(args: Array[String]) : Unit = {
                  |    create()
                  |  }
                  |
                  |  @noinline def create() : Unit = {
                  |    val s = new ${className}()
                  |    println(s.x)
                  |    s.x = 10
                  |    println(s.x)
                  |  }
                  |}
                  |
                  |class ${className} {
                  |  var x = 5
                  |}
                  |""".stripMargin

    shouldStackAlloc(code)
  }

  it should "Should ClassAlloc if it escapes (store)" in {
    val code = s"""
                  |object Main {
                  |  var t : ${className} = _
                  |
                  |  def main(args: Array[String]) : Unit = {
                  |    create()
                  |  }
                  |
                  |  @noinline def create() : Unit = {
                  |    val s = new ${className}()
                  |    println(s.x)
                  |    s.x = 10
                  |    t = s
                  |    println(s.x)
                  |  }
                  |}
                  |
                  |class ${className} {
                  |  var x = 5
                  |}
                  |""".stripMargin

    shouldClassAlloc(code)
  }

  it should "Should ClassAlloc if it escapes (ret)" in {
    val code = s"""
                  |object Main {
                  |
                  |  def main(args: Array[String]) : Unit = {
                  |    create()
                  |  }
                  |
                  |  @noinline def create() : ${className} = {
                  |    val s = new ${className}()
                  |    println(s.x)
                  |    s.x = 10
                  |    println(s.x)
                  |    s
                  |  }
                  |}
                  |
                  |class ${className} {
                  |  var x = 5
                  |}
                  |""".stripMargin

    shouldClassAlloc(code)
  }

  it should "Should ClassAlloc if it escapes (throw)" in {
    val code = s"""
                  |object Main {
                  |private class MyException(s: ${className}) extends Exception
                  |
                  |  def main(args: Array[String]) : Unit = {
                  |    create()
                  |  }
                  |
                  |  @noinline def create() : Unit = {
                  |    val s = new ${className}()
                  |    println(s.x)
                  |    s.x = 10
                  |    println(s.x)
                  |    throw new MyException(s)
                  |  }
                  |}
                  |
                  |class ${className} {
                  |  var x = 5
                  |}
                  |""".stripMargin

    shouldClassAlloc(code)
  }
  private class ClassAllocChecker extends Pass {
    override def onInst(inst: Inst): Inst = inst match {
      case inst @ Let(_, _: Op.Classalloc) if inst.show.contains(className) =>
        fail(s"Found a call to classalloc ${inst.show}")
      case _ => inst
    }
  }

  private object ClassAllocChecker extends PassCompanion {
    override def apply(config: Config, top: Top): Pass = new ClassAllocChecker
  }

  private class StackAllocChecker extends Pass {
    override def onInst(inst: Inst): Inst = inst match {
      case inst @ Let(_, _: Op.Stackalloc) if inst.show.contains(className) =>
        fail(s"Found a call to stackalloc ${inst.show}")
      case _ => inst
    }
  }

  private object StackAllocChecker extends PassCompanion {
    override def apply(config: Config, top: Top): Pass = new StackAllocChecker
  }

}
