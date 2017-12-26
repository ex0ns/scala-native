package scala.scalanative
package optimizer

import tools.Mode

sealed trait Driver {

  /** Companion of all the passes in the driver's pipeline. */
  def passes: Seq[AnyPassCompanion]

  /** Create a copy with given passes. */
  def withPasses(passes: Seq[AnyPassCompanion]): Driver
}

object Driver {

  private val injectionPasses: Seq[InjectCompanion] = Seq(
    inject.Main,
    inject.TraitDispatchTables,
    inject.HasTrait,
    inject.RuntimeTypeInformation,
    inject.ClassStruct,
    inject.ObjectArrayId,
    inject.ModuleArray,
    inject.SafepointTrigger
  )

  private val fastOptPasses = Seq(
    pass.GlobalBoxingElimination,
    pass.UnitSimplification,
    pass.DeadCodeElimination
  )

  private val fullOptPasses = fastOptPasses ++ Seq(
    pass.BlockParamReduction,
    pass.CfChainsSimplification,
    pass.DeadBlockElimination,
    pass.BasicBlocksFusion,
    pass.Canonicalization,
    pass.PartialEvaluation,
    pass.InstCombine,
    pass.ConstantFolding,
    pass.GlobalValueNumbering
  )

  private def loweringPasses(config: tools.Config) = Seq(
    pass.Inlining,
    pass.DynmethodLowering,
    pass.ExternHoisting,
    pass.ModuleLowering,
    pass.TypeValueLowering,
    pass.BoxingLowering,
    pass.AsLowering,
    pass.IsLowering,
    pass.MethodLowering,
    pass.TraitLowering,
    pass.ClassLowering,
    pass.StringLowering,
    pass.UnitLowering, pass.NothingLowering) ++ escape(config) ++ Seq(pass.AllocLowering,
    pass.SizeofLowering,
    pass.CopyPropagation,
    pass.DeadCodeElimination
    // pass.SafepointInsertion
    )

  private def escape(config: tools.Config) = if(config.inlining.disableEscape) Seq() else Seq(pass.EscapeAnalysis)

  /** Create driver with default pipeline for this configuration. */
  def apply(config: tools.Config): Driver = {
    val optPasses = config.mode match {
      case Mode.Debug   => fastOptPasses
      case Mode.Release => fullOptPasses
    }
    new Impl(injectionPasses ++ optPasses ++ loweringPasses(config))
  }

  /** Create an empty pass-less driver. */
  def empty: Driver =
    new Impl(Seq.empty)

  private final class Impl(val passes: Seq[AnyPassCompanion]) extends Driver {
    def withPasses(passes: Seq[AnyPassCompanion]): Driver =
      new Impl(passes)
  }
}
