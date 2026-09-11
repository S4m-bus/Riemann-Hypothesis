import RiemannHypothesis.AdelicFlow.IIIUnitaryLogFlow
import Mathlib.Analysis.Complex.Norm

noncomputable section

open MeasureTheory

namespace RiemannHypothesis.AdelicFlow

/-!
# Number III: generator and resolvent boundary

For the logarithmic translation group, the self-adjoint generator is expected to
be `-i ∂q`.  On the Fourier side this becomes multiplication by a real spectral
coordinate (up to the Fourier normalization constant).

The clean self-adjointness route is therefore to construct the maximal real
multiplication operator and prove that its two non-real resolvents are everywhere
defined.  The pointwise estimates below are the analytic core of that argument.
-/

/-- The positive imaginary resolvent denominator `x + i`. -/
def plusDenom (x : ℝ) : ℂ := (x : ℂ) + Complex.I

/-- The negative imaginary resolvent denominator `x - i`. -/
def minusDenom (x : ℝ) : ℂ := (x : ℂ) - Complex.I

@[simp]
theorem normSq_plusDenom (x : ℝ) :
    Complex.normSq (plusDenom x) = x ^ 2 + 1 := by
  simp [plusDenom, Complex.normSq_apply, pow_two]

@[simp]
theorem normSq_minusDenom (x : ℝ) :
    Complex.normSq (minusDenom x) = x ^ 2 + 1 := by
  simp [minusDenom, Complex.normSq_apply, pow_two]

/-- `x + i` never vanishes for real `x`. -/
theorem plusDenom_ne_zero (x : ℝ) : plusDenom x ≠ 0 := by
  intro h
  have hsq := congrArg Complex.normSq h
  simp at hsq
  nlinarith [sq_nonneg x]

/-- `x - i` never vanishes for real `x`. -/
theorem minusDenom_ne_zero (x : ℝ) : minusDenom x ≠ 0 := by
  intro h
  have hsq := congrArg Complex.normSq h
  simp at hsq
  nlinarith [sq_nonneg x]

/-- The pointwise multiplier for `(Q + i)⁻¹`. -/
def plusResolventMultiplier (x : ℝ) : ℂ := (plusDenom x)⁻¹

/-- The pointwise multiplier for `(Q - i)⁻¹`. -/
def minusResolventMultiplier (x : ℝ) : ℂ := (minusDenom x)⁻¹

@[simp]
theorem plusDenom_mul_resolvent (x : ℝ) :
    plusDenom x * plusResolventMultiplier x = 1 := by
  simp [plusResolventMultiplier, plusDenom_ne_zero]

@[simp]
theorem minusDenom_mul_resolvent (x : ℝ) :
    minusDenom x * minusResolventMultiplier x = 1 := by
  simp [minusResolventMultiplier, minusDenom_ne_zero]

/-- Both non-real resolvent multipliers are contractions. -/
theorem norm_plusResolventMultiplier_le_one (x : ℝ) :
    ‖plusResolventMultiplier x‖ ≤ 1 := by
  have hsq : 1 ≤ Complex.normSq (plusDenom x) := by
    rw [normSq_plusDenom]
    nlinarith [sq_nonneg x]
  have hn : 1 ≤ ‖plusDenom x‖ := Complex.one_le_normSq_iff.mp hsq
  have hp : 0 < ‖plusDenom x‖ := lt_of_lt_of_le zero_lt_one hn
  rw [plusResolventMultiplier, norm_inv]
  exact (inv_le_one₀ hp).2 hn

/-- The negative-imaginary resolvent multiplier is also a contraction. -/
theorem norm_minusResolventMultiplier_le_one (x : ℝ) :
    ‖minusResolventMultiplier x‖ ≤ 1 := by
  have hsq : 1 ≤ Complex.normSq (minusDenom x) := by
    rw [normSq_minusDenom]
    nlinarith [sq_nonneg x]
  have hn : 1 ≤ ‖minusDenom x‖ := Complex.one_le_normSq_iff.mp hsq
  have hp : 0 < ‖minusDenom x‖ := lt_of_lt_of_le zero_lt_one hn
  rw [minusResolventMultiplier, norm_inv]
  exact (inv_le_one₀ hp).2 hn

/-- Multiplication by the spectral coordinate after applying `(Q+i)⁻¹` is
bounded pointwise.  The identity is more useful for the `L²` domain proof than
a sharp estimate. -/
theorem coord_mul_plusResolventMultiplier (x : ℝ) :
    (x : ℂ) * plusResolventMultiplier x =
      1 - Complex.I * plusResolventMultiplier x := by
  have h := plusDenom_mul_resolvent x
  dsimp [plusDenom] at h
  calc
    (x : ℂ) * plusResolventMultiplier x =
        (((x : ℂ) + Complex.I) - Complex.I) * plusResolventMultiplier x := by ring
    _ = ((x : ℂ) + Complex.I) * plusResolventMultiplier x -
        Complex.I * plusResolventMultiplier x := by ring
    _ = 1 - Complex.I * plusResolventMultiplier x := by rw [h]

/-- The analogous coordinate identity for `(Q-i)⁻¹`. -/
theorem coord_mul_minusResolventMultiplier (x : ℝ) :
    (x : ℂ) * minusResolventMultiplier x =
      1 + Complex.I * minusResolventMultiplier x := by
  have h := minusDenom_mul_resolvent x
  dsimp [minusDenom] at h
  calc
    (x : ℂ) * minusResolventMultiplier x =
        (((x : ℂ) - Complex.I) + Complex.I) * minusResolventMultiplier x := by ring
    _ = ((x : ℂ) - Complex.I) * minusResolventMultiplier x +
        Complex.I * minusResolventMultiplier x := by ring
    _ = 1 + Complex.I * minusResolventMultiplier x := by rw [h]

/-! ## Maximal coordinate multiplication operator

The Fourier-side operator is multiplication by the real coordinate.  Its maximal
domain consists exactly of those `L²` classes for which multiplication by the
coordinate is again in `L²`.
-/

/-- A representative of coordinate multiplication on an `L²` class. -/
def coordinateWeighted (f : LogHilbert) : ℝ → ℂ :=
  fun x => (x : ℂ) * f x

/-- Maximal `L²` domain of multiplication by the real coordinate. -/
def coordinateDomain : Submodule ℂ LogHilbert where
  carrier := {f | MemLp (coordinateWeighted f) 2 volume}
  zero_mem' := by
    apply MemLp.ae_eq ?_ (MemLp.zero)
    filter_upwards [Lp.coeFn_zero ℂ 2 volume] with x hx
    simp [coordinateWeighted, hx]
  add_mem' {f g} hf hg := by
    apply MemLp.ae_eq ?_ (hf.add hg)
    filter_upwards [Lp.coeFn_add f g] with x hx
    change (x : ℂ) * f x + (x : ℂ) * g x = (x : ℂ) * (f + g) x
    rw [hx]
    simp [mul_add]
  smul_mem' c f hf := by
    apply MemLp.ae_eq ?_ (hf.const_smul c)
    filter_upwards [Lp.coeFn_smul c f] with x hx
    change c * ((x : ℂ) * f x) = (x : ℂ) * (c • f) x
    rw [hx]
    simp [smul_eq_mul]
    ring

/-- Coordinate multiplication as an `L²` vector on its maximal domain. -/
def coordinateApply (f : coordinateDomain) : LogHilbert :=
  f.property.toLp (coordinateWeighted f.1)

/-- On representatives, coordinate application is literally multiplication by `x`. -/
theorem coordinateApply_ae (f : coordinateDomain) :
    (coordinateApply f : ℝ → ℂ) =ᵐ[volume] coordinateWeighted f.1 := by
  exact MemLp.coeFn_toLp f.property

@[simp]
theorem coordinateApply_add (f g : coordinateDomain) :
    coordinateApply (f + g) = coordinateApply f + coordinateApply g := by
  rw [Lp.ext_iff]
  filter_upwards [coordinateApply_ae (f + g), coordinateApply_ae f,
    coordinateApply_ae g, Lp.coeFn_add (coordinateApply f) (coordinateApply g),
    Lp.coeFn_add f.1 g.1] with x hfg hf hg hsum hbase
  rw [hfg, hsum]
  simp only [Pi.add_apply]
  rw [hf, hg]
  change (x : ℂ) * (f + g : coordinateDomain).1 x =
    (x : ℂ) * f.1 x + (x : ℂ) * g.1 x
  rw [Submodule.coe_add, hbase]
  ring

@[simp]
theorem coordinateApply_smul (c : ℂ) (f : coordinateDomain) :
    coordinateApply (c • f) = c • coordinateApply f := by
  rw [Lp.ext_iff]
  filter_upwards [coordinateApply_ae (c • f), coordinateApply_ae f,
    Lp.coeFn_smul c (coordinateApply f), Lp.coeFn_smul c f.1] with x hcf hf hsum hbase
  rw [hcf, hsum]
  simp only [Pi.smul_apply]
  rw [hf]
  change (x : ℂ) * (c • f : coordinateDomain).1 x = c * ((x : ℂ) * f.1 x)
  rw [Submodule.coe_smul, hbase]
  simp [smul_eq_mul]
  ring

/-- The maximal unbounded multiplication operator `Q f(x) = x f(x)`. -/
def coordinateOperator : LogHilbert →ₗ.[ℂ] LogHilbert where
  domain := coordinateDomain
  toFun :=
    { toFun := coordinateApply
      map_add' := coordinateApply_add
      map_smul' := coordinateApply_smul }

@[simp]
theorem coordinateOperator_apply (f : coordinateOperator.domain) :
    coordinateOperator f = coordinateApply f := by
  rfl

end RiemannHypothesis.AdelicFlow
