import RiemannHypothesis.AdelicFlow.IIILogGeneratorCore
import Mathlib.Topology.Algebra.Module.LinearPMap

noncomputable section

open MeasureTheory
open scoped LinearPMap FourierTransform SchwartzMap

namespace RiemannHypothesis.AdelicFlow

/-!
# Number III: Schwartz graph-core boundary

The local generator itself is now sealed: it is self-adjoint and agrees with
`-i ∂q` on Schwartz functions.  The next operator-theoretic obligation is the
stronger statement that Schwartz functions form a graph core.

This file packages the exact Schwartz `L²` submodule, proves that it lies in the
maximal domain, and isolates the remaining core equality in mathlib's native
`LinearPMap.HasCore` language.
-/

/-- The complex-linear submodule of `L²(ℝ)` represented by Schwartz functions. -/
def logSchwartzSubmodule : Submodule ℂ LogHilbert :=
  LinearMap.range
    (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 volume).toLinearMap

/-- Every Schwartz `L²` vector lies in the maximal logarithmic-generator domain. -/
theorem logSchwartzSubmodule_le_logGeneratorDomain :
    logSchwartzSubmodule ≤ logGenerator.domain := by
  intro u hu
  change u ∈ LinearMap.range
    (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 volume).toLinearMap at hu
  rcases hu with ⟨f, rfl⟩
  change f.toLp 2 volume ∈ logGenerator.domain
  exact schwartz_toLp_mem_logGeneratorDomain f

/-- Restriction of the maximal self-adjoint generator to Schwartz `L²` vectors. -/
def logGeneratorSchwartzRestriction : LogHilbert →ₗ.[ℂ] LogHilbert :=
  logGenerator.domRestrict logSchwartzSubmodule

/-- The Schwartz restriction is an operator restriction of the maximal generator. -/
theorem logGeneratorSchwartzRestriction_le_logGenerator :
    logGeneratorSchwartzRestriction ≤ logGenerator := by
  exact LinearPMap.domRestrict_le

/-- The Schwartz restriction is closable because it has the closed self-adjoint
maximal generator as an extension. -/
theorem logGeneratorSchwartzRestriction_isClosable :
    logGeneratorSchwartzRestriction.IsClosable := by
  exact logGenerator_selfAdjoint.isClosed.isClosable.leIsClosable
    logGeneratorSchwartzRestriction_le_logGenerator

/-- The exact remaining graph-core obligation.  Since containment in the maximal
domain is already proved above, `HasCore` is now equivalent to the single closure
equality for the Schwartz restriction. -/
theorem logGenerator_hasSchwartzCore_iff :
    logGenerator.HasCore logSchwartzSubmodule ↔
      logGeneratorSchwartzRestriction.closure = logGenerator := by
  constructor
  · intro hcore
    simpa [logGeneratorSchwartzRestriction] using hcore.closure_eq
  · intro hclosure
    refine ⟨logSchwartzSubmodule_le_logGeneratorDomain, ?_⟩
    simpa [logGeneratorSchwartzRestriction] using hclosure

end RiemannHypothesis.AdelicFlow
