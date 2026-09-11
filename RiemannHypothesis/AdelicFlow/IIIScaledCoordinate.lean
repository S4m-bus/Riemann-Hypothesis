import RiemannHypothesis.AdelicFlow.IIICoordinateSelfAdjoint

noncomputable section

open MeasureTheory
open scoped LinearPMap ComplexConjugate

namespace RiemannHypothesis.AdelicFlow

/-!
# Number III: the Fourier-normalized coordinate operator

Mathlib's Fourier convention sends differentiation to multiplication by
`2π I x`.  The Fourier-side operator corresponding to `-i ∂q` is therefore
`2π Q`, not `Q`.  This file proves that this nonzero real scalar multiple of
the maximal coordinate operator is again self-adjoint.
-/

/-- The Fourier normalization constant, viewed as a complex scalar. -/
def fourierScale : ℂ := ((2 * Real.pi : ℝ) : ℂ)

@[simp]
theorem fourierScale_ne_zero : fourierScale ≠ 0 := by
  rw [fourierScale]
  exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero

@[simp]
theorem conj_fourierScale : conj fourierScale = fourierScale := by
  unfold fourierScale
  exact Complex.conj_ofReal (2 * Real.pi)

@[simp]
theorem conj_fourierScale_inv : conj (fourierScale⁻¹) = fourierScale⁻¹ := by
  rw [map_inv₀, conj_fourierScale]

/-- The Fourier-normalized multiplication operator `2π Q`. -/
def scaledCoordinateOperator : LogHilbert →ₗ.[ℂ] LogHilbert :=
  fourierScale • coordinateOperator

@[simp]
theorem scaledCoordinateOperator_domain :
    scaledCoordinateOperator.domain = coordinateOperator.domain := by
  rfl

@[simp]
theorem scaledCoordinateOperator_apply (f : scaledCoordinateOperator.domain) :
    scaledCoordinateOperator f = fourierScale • coordinateOperator
      ⟨(f : LogHilbert), by simpa using f.property⟩ := by
  rfl

/-- `2π Q` has the same dense maximal domain as `Q`. -/
theorem scaledCoordinateDomain_dense :
    Dense (scaledCoordinateOperator.domain : Set LogHilbert) := by
  change Dense (coordinateOperator.domain : Set LogHilbert)
  change Dense (coordinateDomain : Set LogHilbert)
  exact coordinateDomain_dense

/-- A nonzero real scalar multiple of the symmetric coordinate operator remains symmetric. -/
theorem scaledCoordinateOperator_isFormalAdjoint :
    scaledCoordinateOperator.IsFormalAdjoint scaledCoordinateOperator := by
  intro f g
  let fq : coordinateOperator.domain := ⟨(f : LogHilbert), by simpa using f.property⟩
  let gq : coordinateOperator.domain := ⟨(g : LogHilbert), by simpa using g.property⟩
  have hQ := coordinateOperator_isFormalAdjoint fq gq
  change inner ℂ (fourierScale • coordinateOperator fq) (g : LogHilbert) =
    inner ℂ (f : LogHilbert) (fourierScale • coordinateOperator gq)
  rw [inner_smul_left, inner_smul_right, conj_fourierScale, hQ]

/-- Membership in the adjoint domain of `2π Q` implies membership in the
adjoint domain of `Q`.  The inverse scalar is legitimate because `2π ≠ 0`. -/
theorem scaledAdjoint_domain_le_coordinateAdjoint :
    (scaledCoordinateOperator†).domain ≤ (coordinateOperator†).domain := by
  intro y hy
  let yA : (scaledCoordinateOperator†).domain := ⟨y, hy⟩
  apply LinearPMap.mem_adjoint_domain_of_exists
  refine ⟨fourierScale⁻¹ • scaledCoordinateOperator† yA, ?_⟩
  intro x
  let xA : scaledCoordinateOperator.domain :=
    ⟨(x : LogHilbert), by simpa using x.property⟩
  have hA := LinearPMap.adjoint_isFormalAdjoint scaledCoordinateDomain_dense yA xA
  change inner ℂ (fourierScale⁻¹ • scaledCoordinateOperator† yA) (x : LogHilbert) =
    inner ℂ y (coordinateOperator x)
  rw [inner_smul_left, conj_fourierScale_inv, hA]
  change fourierScale⁻¹ *
      inner ℂ y (fourierScale • coordinateOperator x) =
    inner ℂ y (coordinateOperator x)
  rw [inner_smul_right]
  field_simp [fourierScale_ne_zero]

/-- The adjoint of `2π Q` has no larger domain than `2π Q` itself. -/
theorem scaledAdjoint_domain_le :
    (scaledCoordinateOperator†).domain ≤ scaledCoordinateOperator.domain := by
  intro y hy
  have hQadj : y ∈ (coordinateOperator†).domain :=
    scaledAdjoint_domain_le_coordinateAdjoint hy
  have hQ : y ∈ coordinateOperator.domain := by
    rw [coordinateOperator_domain_eq_adjoint]
    exact hQadj
  simpa [scaledCoordinateOperator] using hQ

/-- Symmetry and density embed `2π Q` in its adjoint. -/
theorem scaledCoordinateOperator_le_adjoint :
    scaledCoordinateOperator ≤ scaledCoordinateOperator† := by
  exact scaledCoordinateOperator_isFormalAdjoint.le_adjoint scaledCoordinateDomain_dense

/-- The Fourier-normalized coordinate operator is self-adjoint. -/
theorem scaledCoordinateOperator_selfAdjoint :
    IsSelfAdjoint scaledCoordinateOperator := by
  have hdom : scaledCoordinateOperator.domain = (scaledCoordinateOperator†).domain := by
    apply le_antisymm
    · exact scaledCoordinateOperator_le_adjoint.1
    · exact scaledAdjoint_domain_le
  rw [LinearPMap.isSelfAdjoint_def]
  exact (LinearPMap.eq_of_le_of_domain_eq scaledCoordinateOperator_le_adjoint hdom).symm

/-- Number III already holds on the Fourier side with the exact `2π` normalization. -/
theorem scaledCoordinateOperator_numberIII : NumberIII scaledCoordinateOperator := by
  exact (numberIII_iff_isSelfAdjoint scaledCoordinateOperator).2
    scaledCoordinateOperator_selfAdjoint

end RiemannHypothesis.AdelicFlow
