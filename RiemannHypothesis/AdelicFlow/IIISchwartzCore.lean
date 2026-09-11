import RiemannHypothesis.AdelicFlow.IIILogGeneratorCore
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.MeasureTheory.Function.Holder

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
maximal domain and is dense in the ambient Hilbert space, and isolates the
remaining core equality in mathlib's native `LinearPMap.HasCore` language.
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

/-- Schwartz vectors are dense in the ambient logarithmic Hilbert space.  This
is ordinary Hilbert-space density; the stronger graph-density statement is the
remaining core obligation below. -/
theorem logSchwartzSubmodule_dense :
    Dense (logSchwartzSubmodule : Set LogHilbert) := by
  have hd :
      DenseRange (SchwartzMap.toLpCLM ℝ (E := ℝ) ℂ 2 volume) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  apply hd.mono
  rintro u ⟨f, rfl⟩
  change f.toLp 2 volume ∈ logSchwartzSubmodule
  change f.toLp 2 volume ∈ LinearMap.range
    (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 volume).toLinearMap
  exact ⟨f, rfl⟩

/-! ## Bounded resolvent package for graph-density

The coordinate resolvent `(Q+i)⁻¹` has already been constructed pointwise in
`IIIResolvent`.  For the graph-core proof we also need its bounded-operator
realization on `L²`, so that ordinary density can be transported continuously
into the graph of the unbounded operator.
-/

/-- The multiplier `(x+i)⁻¹`, bundled as an `L∞` vector. -/
def plusResolventLpInf : MeasureTheory.Lp ℂ ⊤ (volume : Measure ℝ) :=
  plusResolventMultiplier_memLp_top.toLp plusResolventMultiplier

/-- Almost-everywhere representative of the bundled `L∞` resolvent multiplier. -/
theorem plusResolventLpInf_ae :
    (plusResolventLpInf : ℝ → ℂ) =ᵐ[volume] plusResolventMultiplier := by
  exact MemLp.coeFn_toLp plusResolventMultiplier_memLp_top

/-- Multiplication by `(x+i)⁻¹` as a bounded operator `L² → L²`. -/
def plusResolventCLM : LogHilbert →L[ℂ] LogHilbert :=
  ((ContinuousLinearMap.lsmul ℂ ℂ).holderL (volume : Measure ℝ) ⊤ 2 2)
    plusResolventLpInf

/-- The bounded resolvent package has the expected pointwise representative. -/
theorem plusResolventCLM_ae (g : LogHilbert) :
    (plusResolventCLM g : ℝ → ℂ) =ᵐ[volume] plusResolventWeighted g := by
  have hmul :=
    (ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder
      (r := (2 : ENNReal)) plusResolventLpInf g
  have h :
      ((ContinuousLinearMap.lsmul ℂ ℂ).holder (2 : ENNReal)
          plusResolventLpInf g : ℝ → ℂ) =ᵐ[volume]
        plusResolventWeighted g := by
    filter_upwards [hmul, plusResolventLpInf_ae] with x hx hres
    rw [hx, hres]
    simp [plusResolventWeighted, smul_eq_mul]
  simpa [plusResolventCLM] using h

/-- The new bounded resolvent is exactly the previously constructed resolvent vector. -/
theorem plusResolventCLM_eq_plusResolventVector (g : LogHilbert) :
    plusResolventCLM g = plusResolventVector g := by
  rw [Lp.ext_iff]
  exact (plusResolventCLM_ae g).trans (plusResolventVector_ae g).symm

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

/-- A self-adjoint maximal generator is already equal to its operator closure. -/
theorem logGenerator_closure_eq :
    logGenerator.closure = logGenerator := by
  apply LinearPMap.eq_of_eq_graph
  have hc : logGenerator.IsClosable := logGenerator_selfAdjoint.isClosed.isClosable
  rw [← hc.graph_closure_eq_closure_graph]
  exact logGenerator_selfAdjoint.isClosed.submodule_topologicalClosure_eq

/-- Closing the Schwartz restriction cannot produce anything outside the maximal
self-adjoint logarithmic generator. -/
theorem logGeneratorSchwartzClosure_le_logGenerator :
    logGeneratorSchwartzRestriction.closure ≤ logGenerator := by
  have h :=
    (logGenerator_selfAdjoint.isClosed.isClosable).closure_mono
      logGeneratorSchwartzRestriction_le_logGenerator
  rw [logGenerator_closure_eq] at h
  exact h

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
