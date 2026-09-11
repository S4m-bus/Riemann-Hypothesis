import RiemannHypothesis.AdelicFlow.IIIGenerator

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

end RiemannHypothesis.AdelicFlow
