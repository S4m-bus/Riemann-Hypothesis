import RiemannHypothesis.AdelicFlow.IIISelfAdjoint
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

noncomputable section

open MeasureTheory
open scoped LinearPMap

namespace RiemannHypothesis.AdelicFlow

/-!
# Number III: non-real resolvents of the coordinate operator

We construct the two vectors obtained by multiplying an arbitrary `L²` vector by
`(x+i)⁻¹` and `(x-i)⁻¹`, prove that they lie in the maximal coordinate domain,
and prove the exact resolvent equations.
-/

/-- The positive resolvent multiplier is continuous. -/
theorem continuous_plusResolventMultiplier : Continuous plusResolventMultiplier := by
  unfold plusResolventMultiplier plusDenom
  exact (Complex.continuous_ofReal.add continuous_const).inv₀ plusDenom_ne_zero

/-- The negative resolvent multiplier is continuous. -/
theorem continuous_minusResolventMultiplier : Continuous minusResolventMultiplier := by
  unfold minusResolventMultiplier minusDenom
  exact (Complex.continuous_ofReal.sub continuous_const).inv₀ minusDenom_ne_zero

/-- The positive resolvent multiplier belongs to `L∞`. -/
theorem plusResolventMultiplier_memLp_top :
    MemLp plusResolventMultiplier ⊤ volume := by
  refine memLp_top_of_bound continuous_plusResolventMultiplier.aestronglyMeasurable 1 ?_
  exact Filter.Eventually.of_forall norm_plusResolventMultiplier_le_one

/-- The negative resolvent multiplier belongs to `L∞`. -/
theorem minusResolventMultiplier_memLp_top :
    MemLp minusResolventMultiplier ⊤ volume := by
  refine memLp_top_of_bound continuous_minusResolventMultiplier.aestronglyMeasurable 1 ?_
  exact Filter.Eventually.of_forall norm_minusResolventMultiplier_le_one

/-- Raw representative of `(Q+i)⁻¹ g`. -/
def plusResolventWeighted (g : LogHilbert) : ℝ → ℂ :=
  fun x => plusResolventMultiplier x * g x

/-- Raw representative of `(Q-i)⁻¹ g`. -/
def minusResolventWeighted (g : LogHilbert) : ℝ → ℂ :=
  fun x => minusResolventMultiplier x * g x

/-- The positive resolvent representative is in `L²`. -/
theorem plusResolventWeighted_memLp (g : LogHilbert) :
    MemLp (plusResolventWeighted g) 2 volume := by
  have h := (Lp.memLp g).mul (r := 2) plusResolventMultiplier_memLp_top
  apply MemLp.ae_eq ?_ h
  filter_upwards with x
  rfl

/-- The negative resolvent representative is in `L²`. -/
theorem minusResolventWeighted_memLp (g : LogHilbert) :
    MemLp (minusResolventWeighted g) 2 volume := by
  have h := (Lp.memLp g).mul (r := 2) minusResolventMultiplier_memLp_top
  apply MemLp.ae_eq ?_ h
  filter_upwards with x
  rfl

/-- The `L²` vector `(Q+i)⁻¹ g`. -/
def plusResolventVector (g : LogHilbert) : LogHilbert :=
  (plusResolventWeighted_memLp g).toLp (plusResolventWeighted g)

/-- The `L²` vector `(Q-i)⁻¹ g`. -/
def minusResolventVector (g : LogHilbert) : LogHilbert :=
  (minusResolventWeighted_memLp g).toLp (minusResolventWeighted g)

/-- Almost-everywhere representative of the positive resolvent vector. -/
theorem plusResolventVector_ae (g : LogHilbert) :
    (plusResolventVector g : ℝ → ℂ) =ᵐ[volume] plusResolventWeighted g := by
  exact MemLp.coeFn_toLp (plusResolventWeighted_memLp g)

/-- Almost-everywhere representative of the negative resolvent vector. -/
theorem minusResolventVector_ae (g : LogHilbert) :
    (minusResolventVector g : ℝ → ℂ) =ᵐ[volume] minusResolventWeighted g := by
  exact MemLp.coeFn_toLp (minusResolventWeighted_memLp g)

/-- `(Q+i)⁻¹ g` belongs to the maximal coordinate domain. -/
theorem plusResolventVector_mem_coordinateDomain (g : LogHilbert) :
    plusResolventVector g ∈ coordinateDomain := by
  change MemLp (coordinateWeighted (plusResolventVector g)) 2 volume
  have hsub : MemLp
      ((g : ℝ → ℂ) - Complex.I • (plusResolventVector g : ℝ → ℂ)) 2 volume :=
    (Lp.memLp g).sub ((Lp.memLp (plusResolventVector g)).const_smul Complex.I)
  apply MemLp.ae_eq ?_ hsub
  filter_upwards [plusResolventVector_ae g] with x hx
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, coordinateWeighted]
  rw [hx]
  change g x - Complex.I * (plusResolventMultiplier x * g x) =
    (x : ℂ) * (plusResolventMultiplier x * g x)
  calc
    g x - Complex.I * (plusResolventMultiplier x * g x) =
        (1 - Complex.I * plusResolventMultiplier x) * g x := by ring
    _ = (((x : ℂ) * plusResolventMultiplier x) * g x) := by
      rw [coord_mul_plusResolventMultiplier]
    _ = (x : ℂ) * (plusResolventMultiplier x * g x) := by ring

/-- `(Q-i)⁻¹ g` belongs to the maximal coordinate domain. -/
theorem minusResolventVector_mem_coordinateDomain (g : LogHilbert) :
    minusResolventVector g ∈ coordinateDomain := by
  change MemLp (coordinateWeighted (minusResolventVector g)) 2 volume
  have hadd : MemLp
      ((g : ℝ → ℂ) + Complex.I • (minusResolventVector g : ℝ → ℂ)) 2 volume :=
    (Lp.memLp g).add ((Lp.memLp (minusResolventVector g)).const_smul Complex.I)
  apply MemLp.ae_eq ?_ hadd
  filter_upwards [minusResolventVector_ae g] with x hx
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coordinateWeighted]
  rw [hx]
  change g x + Complex.I * (minusResolventMultiplier x * g x) =
    (x : ℂ) * (minusResolventMultiplier x * g x)
  calc
    g x + Complex.I * (minusResolventMultiplier x * g x) =
        (1 + Complex.I * minusResolventMultiplier x) * g x := by ring
    _ = (((x : ℂ) * minusResolventMultiplier x) * g x) := by
      rw [coord_mul_minusResolventMultiplier]
    _ = (x : ℂ) * (minusResolventMultiplier x * g x) := by ring

/-- Positive resolvent vector packaged in the operator domain. -/
def plusResolventDomain (g : LogHilbert) : coordinateOperator.domain :=
  ⟨plusResolventVector g, plusResolventVector_mem_coordinateDomain g⟩

/-- Negative resolvent vector packaged in the operator domain. -/
def minusResolventDomain (g : LogHilbert) : coordinateOperator.domain :=
  ⟨minusResolventVector g, minusResolventVector_mem_coordinateDomain g⟩

/-- Exact positive resolvent equation `(Q+i)R₊g=g`. -/
theorem plusResolvent_equation (g : LogHilbert) :
    coordinateOperator (plusResolventDomain g) +
      Complex.I • plusResolventVector g = g := by
  rw [Lp.ext_iff]
  filter_upwards [coordinateApply_ae (plusResolventDomain g), plusResolventVector_ae g,
    Lp.coeFn_add (coordinateOperator (plusResolventDomain g))
      (Complex.I • plusResolventVector g),
    Lp.coeFn_smul Complex.I (plusResolventVector g)] with x hQ hR hAdd hSmul
  rw [hAdd]
  simp only [Pi.add_apply]
  rw [hSmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [coordinateOperator_apply, hQ]
  simp only [coordinateWeighted, plusResolventDomain, plusResolventWeighted]
  rw [hR]
  change (x : ℂ) * (plusResolventMultiplier x * g x) +
      Complex.I * (plusResolventMultiplier x * g x) = g x
  have h := plusDenom_mul_resolvent x
  dsimp [plusDenom] at h
  calc
    (x : ℂ) * (plusResolventMultiplier x * g x) +
        Complex.I * (plusResolventMultiplier x * g x) =
        (((x : ℂ) + Complex.I) * plusResolventMultiplier x) * g x := by ring
    _ = g x := by rw [h, one_mul]

/-- Exact negative resolvent equation `(Q-i)R₋g=g`. -/
theorem minusResolvent_equation (g : LogHilbert) :
    coordinateOperator (minusResolventDomain g) -
      Complex.I • minusResolventVector g = g := by
  rw [Lp.ext_iff]
  filter_upwards [coordinateApply_ae (minusResolventDomain g), minusResolventVector_ae g,
    Lp.coeFn_sub (coordinateOperator (minusResolventDomain g))
      (Complex.I • minusResolventVector g),
    Lp.coeFn_smul Complex.I (minusResolventVector g)] with x hQ hR hSub hSmul
  rw [hSub]
  simp only [Pi.sub_apply]
  rw [hSmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [coordinateOperator_apply, hQ]
  simp only [coordinateWeighted, minusResolventDomain, minusResolventWeighted]
  rw [hR]
  change (x : ℂ) * (minusResolventMultiplier x * g x) -
      Complex.I * (minusResolventMultiplier x * g x) = g x
  have h := minusDenom_mul_resolvent x
  dsimp [minusDenom] at h
  calc
    (x : ℂ) * (minusResolventMultiplier x * g x) -
        Complex.I * (minusResolventMultiplier x * g x) =
        (((x : ℂ) - Complex.I) * minusResolventMultiplier x) * g x := by ring
    _ = g x := by rw [h, one_mul]

/-- Surjectivity of `Q+iI`, expressed without replacing the unbounded operator by
a bounded surrogate. -/
theorem coordinateOperator_plus_I_surjective (g : LogHilbert) :
    ∃ f : coordinateOperator.domain,
      coordinateOperator f + Complex.I • (f : LogHilbert) = g := by
  refine ⟨plusResolventDomain g, ?_⟩
  exact plusResolvent_equation g

/-- Surjectivity of `Q-iI`. -/
theorem coordinateOperator_minus_I_surjective (g : LogHilbert) :
    ∃ f : coordinateOperator.domain,
      coordinateOperator f - Complex.I • (f : LogHilbert) = g := by
  refine ⟨minusResolventDomain g, ?_⟩
  exact minusResolvent_equation g

end RiemannHypothesis.AdelicFlow
