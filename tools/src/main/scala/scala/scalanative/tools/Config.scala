package scala.scalanative
package tools

import java.io.File

import nir.Global
import scala.scalanative.optimizer.pass.EscapeAnalysis

case class InliningConfig(inliningThreshold : Int = 64, maxMethodSize : Int = 10000, maxDepth : Int = 2, disableLLVM : Boolean = false, disableEscape: Boolean = false)

sealed trait Config {

  /** Entry point for linking. */
  def entry: Global

  /** Sequence of all NIR locations. */
  def paths: Seq[File]

  /** Directory to emit intermediate compilation results. */
  def workdir: File

  /** Target triple. */
  def target: String

  /** Compilation mode. */
  def mode: Mode

  def inlining: InliningConfig

  /** Create new config with given entry point. */
  def withEntry(value: Global): Config

  /** Create a new config with given nir paths. */
  def withPaths(value: Seq[File]): Config

  /** Create a new config with given directory. */
  def withWorkdir(value: File): Config

  /** Create a new config with given target triple. */
  def withTarget(value: String): Config

  /** Create a new config with given compilation mode. */
  def withMode(value: Mode): Config

  /** Create a new config with a given inlining config */
  def withInliningConfig(inlining: InliningConfig) : Config
}

object Config {

  /** Default empty config object. */
  val empty: Config =
    Impl(entry = Global.None,
         paths = Seq.empty,
         workdir = new File(""),
         target = "",
         mode = Mode.Debug,
      inlining = InliningConfig()
    )

  private final case class Impl(entry: Global,
                                paths: Seq[File],
                                workdir: File,
                                target: String,
                                mode: Mode,
                                inlining: InliningConfig)
      extends Config {
    def withEntry(value: Global): Config =
      copy(entry = value)

    def withPaths(value: Seq[File]): Config =
      copy(paths = value)

    def withWorkdir(value: File): Config =
      copy(workdir = value)

    def withTarget(value: String): Config =
      copy(target = value)

    def withMode(value: Mode): Config =
      copy(mode = value)

    def withInliningConfig(inlining: InliningConfig): Config =
      copy(inlining = inlining)
  }
}
