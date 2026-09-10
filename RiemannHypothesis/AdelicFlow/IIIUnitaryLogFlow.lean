import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.LinearPMap

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RiemannHypothesis.AdelicFlow

/-!
# Number III: quantum log-flow boundary

The correct self-adjointness target is an unbounded operator on a complex Hilbert
space. Before constructing its generator, we first construct the kinematic
one-parameter unitary representation associated with translation in the
logarithmic coordinate `q = log x`.

This is the rigorous quantum counterpart of the classical dilation flow: the
measure `dq` is translation invariant, hence pullback by `q ↦ q+t` is an
isometry on `L²(ℝ, dq)`.
-/

/-- The logarithmic Hilbert space `L²(ℝ, ℂ)` with its canonical volume measure. -/
abbrev LogHilbert : Type :=
  MeasureTheory.Lp (α := ℝ) ℂ 2

/-- Pullback by translation in the logarithmic coordinate. The domain-action
wrapper is used by mathlib precisely so that these pullbacks form a left group
action on `Lᵖ`. -/
def logUnitaryFlow (t : ℝ) (f : LogHilbert) : LogHilbert :=
  DomAddAct.mk t +ᵥ f

@[simp]
theorem logUnitaryFlow_zero (f : LogHilbert) :
    logUnitaryFlow 0 f = f := by
  simp [logUnitaryFlow]

/-- The logarithmic pullbacks obey the one-parameter group law. -/
theorem logUnitaryFlow_add (s t : ℝ) (f : LogHilbert) :
    logUnitaryFlow (s + t) f = logUnitaryFlow s (logUnitaryFlow t f) := by
  simp [logUnitaryFlow]

/-- Each logarithmic translation preserves the `L²` norm. -/
theorem logUnitaryFlow_norm (t : ℝ) (f : LogHilbert) :
    ‖logUnitaryFlow t f‖ = ‖f‖ := by
  simp [logUnitaryFlow]

/-- The inverse flow is translation by the opposite time. -/
theorem logUnitaryFlow_neg_left (t : ℝ) (f : LogHilbert) :
    logUnitaryFlow (-t) (logUnitaryFlow t f) = f := by
  rw [← logUnitaryFlow_add]
  simp

/-- Strong continuity: for every vector in `L²`, its orbit under logarithmic
translation depends continuously on time. -/
theorem logUnitaryFlow_strongContinuous (f : LogHilbert) :
    Continuous (fun t : ℝ => logUnitaryFlow t f) := by
  fun_prop

/-! ## The exact unbounded Number III target

Mathlib's `LinearPMap` is the appropriate object for an unbounded Hilbert-space
operator. We do not replace the Hilbert--Pólya generator by a bounded surrogate.
-/

open scoped LinearPMap

/-- Number III for an unbounded operator is literally equality with its Hilbert
space adjoint. -/
def NumberIII {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : H →ₗ.[ℂ] H) : Prop :=
  M† = M

/-- Our formulation is exactly mathlib's `IsSelfAdjoint` predicate. -/
theorem numberIII_iff_isSelfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : H →ₗ.[ℂ] H) :
    NumberIII M ↔ IsSelfAdjoint M := by
  rfl

/-- A completed Number III proof automatically gives a dense operator domain. -/
theorem numberIII_dense_domain
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {M : H →ₗ.[ℂ] H} (hM : NumberIII M) :
    Dense (M.domain : Set H) := by
  exact (numberIII_iff_isSelfAdjoint M).mp hM |>.dense_domain

/-- A completed Number III proof automatically gives a closed operator. -/
theorem numberIII_isClosed
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {M : H →ₗ.[ℂ] H} (hM : NumberIII M) :
    M.IsClosed := by
  exact (numberIII_iff_isSelfAdjoint M).mp hM |>.isClosed

end RiemannHypothesis.AdelicFlow
