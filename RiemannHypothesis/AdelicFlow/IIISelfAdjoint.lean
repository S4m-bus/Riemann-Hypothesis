import RiemannHypothesis.AdelicFlow.IIIGenerator
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

noncomputable section

open MeasureTheory
open scoped LinearPMap

namespace RiemannHypothesis.AdelicFlow

/-!
# Number III: self-adjointness of the maximal coordinate operator

This file proves the analytic theorem needed before transporting Number III back
through Fourier conjugation.  The operator is the maximal real multiplication
operator `Q f(x) = x f(x)`.
-/

/-- Multiplication by the real coordinate is symmetric on its maximal domain. -/
theorem coordinateOperator_isFormalAdjoint :
    coordinateOperator.IsFormalAdjoint coordinateOperator := by
  intro f g
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coordinateApply_ae f, coordinateApply_ae g] with x hf hg
  simp only [coordinateOperator_apply]
  rw [hf, hg]
  simp [coordinateWeighted, RCLike.inner_apply']
  ring

/-! ## A dense Schwartz core

Schwartz functions are dense in `L²`, and multiplication by the coordinate sends
a Schwartz function to another Schwartz function.  Therefore their `L²` image is
a dense subset of the maximal coordinate domain.
-/

/-- Multiplication by the real coordinate preserves Schwartz space. -/
def coordinateSchwartz (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.evalCLM ℂ ℝ ℂ (1 : ℝ)
    (SchwartzMap.smulRightCLM ℂ ℂ (ContinuousLinearMap.lsmul ℝ ℝ) f)

@[simp]
theorem coordinateSchwartz_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    coordinateSchwartz f x = (x : ℂ) * f x := by
  simp [coordinateSchwartz, smul_eq_mul]

/-- Every Schwartz `L²` vector belongs to the maximal multiplication domain. -/
theorem schwartz_toLp_mem_coordinateDomain (f : SchwartzMap ℝ ℂ) :
    f.toLp 2 volume ∈ coordinateDomain := by
  have hweighted : MemLp (coordinateSchwartz f) 2 volume :=
    (coordinateSchwartz f).memLp 2 volume
  apply MemLp.ae_eq ?_ hweighted
  filter_upwards [f.coeFn_toLp 2 volume] with x hx
  rw [coordinateSchwartz_apply]
  simp [coordinateWeighted, hx]

/-- The maximal coordinate-multiplication domain is dense in `L²(ℝ,ℂ)`. -/
theorem coordinateDomain_dense : Dense (coordinateDomain : Set LogHilbert) := by
  have hd : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 volume) :=
    SchwartzMap.denseRange_toLpCLM (F := ℂ) (E := ℝ) (p := 2) (μ := volume) (by norm_num)
  apply hd.mono
  rintro _ ⟨f, rfl⟩
  simpa using schwartz_toLp_mem_coordinateDomain f

end RiemannHypothesis.AdelicFlow
