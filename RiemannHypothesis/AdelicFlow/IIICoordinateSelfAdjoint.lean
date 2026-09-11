import RiemannHypothesis.AdelicFlow.IIIResolvent
import Mathlib.Tactic.Module

noncomputable section

open MeasureTheory
open scoped LinearPMap

namespace RiemannHypothesis.AdelicFlow

/-!
# Number III: self-adjoint maximal coordinate multiplication

The maximal multiplication operator `Q f(x) = x f(x)` is densely defined and
symmetric.  The two non-real shifts `Q ± iI` are surjective.  We use those facts
to prove equality with the Hilbert-space adjoint.
-/

/-- Symmetry plus density embeds `Q` in its Hilbert-space adjoint. -/
theorem coordinateOperator_le_adjoint :
    coordinateOperator ≤ coordinateOperator† := by
  exact coordinateOperator_isFormalAdjoint.le_adjoint coordinateDomain_dense

/-- The fundamental adjoint identity in the orientation used below. -/
theorem coordinateOperator_formalAdjoint_adjoint :
    coordinateOperator.IsFormalAdjoint coordinateOperator† := by
  exact (LinearPMap.adjoint_isFormalAdjoint coordinateDomain_dense).symm

/-- The adjoint has no larger domain than the maximal coordinate-multiplication
operator.  Surjectivity of both non-real shifts kills the deficiency vector. -/
theorem coordinateAdjoint_domain_le :
    (coordinateOperator†).domain ≤ coordinateOperator.domain := by
  intro y hy

  let yAdj : (coordinateOperator†).domain := ⟨y, hy⟩
  let g : LogHilbert := coordinateOperator† yAdj + Complex.I • y
  obtain ⟨x, hx⟩ := coordinateOperator_plus_I_surjective g
  dsimp [g] at hx

  have hxAdjMem : (x : LogHilbert) ∈ (coordinateOperator†).domain :=
    coordinateOperator_le_adjoint.1 x.property
  let xAdj : (coordinateOperator†).domain := ⟨(x : LogHilbert), hxAdjMem⟩

  have hQx : coordinateOperator† xAdj = coordinateOperator x := by
    exact (coordinateOperator_le_adjoint.2 (x := x) (y := xAdj) rfl).symm

  let d : LogHilbert := y - (x : LogHilbert)
  have hdAdjMem : d ∈ (coordinateOperator†).domain := by
    dsimp [d]
    exact (coordinateOperator†).domain.sub_mem hy hxAdjMem
  let dAdj : (coordinateOperator†).domain := ⟨d, hdAdjMem⟩

  have hdAdj_eq : dAdj = yAdj - xAdj := by
    apply Subtype.ext
    rfl

  have hQy :
      coordinateOperator† yAdj =
        coordinateOperator x + Complex.I • (x : LogHilbert) - Complex.I • y := by
    calc
      coordinateOperator† yAdj =
          (coordinateOperator† yAdj + Complex.I • y) - Complex.I • y := by module
      _ = (coordinateOperator x + Complex.I • (x : LogHilbert)) - Complex.I • y := by
        rw [← hx]

  have hAdjD : coordinateOperator† dAdj = -Complex.I • d := by
    rw [hdAdj_eq, LinearPMap.map_sub, hQx, hQy]
    dsimp [d]
    module

  obtain ⟨u, hu⟩ := coordinateOperator_minus_I_surjective d

  have hinnerShift :
      inner ℂ (coordinateOperator u - Complex.I • (u : LogHilbert)) d = 0 := by
    rw [inner_sub_left]
    have hf := coordinateOperator_formalAdjoint_adjoint u dAdj
    change inner ℂ (coordinateOperator u) d =
      inner ℂ (u : LogHilbert) (coordinateOperator† dAdj) at hf
    rw [hf, hAdjD]
    simp [inner_smul_left, inner_smul_right]

  have hself : inner ℂ d d = 0 := by
    calc
      inner ℂ d d =
          inner ℂ (coordinateOperator u - Complex.I • (u : LogHilbert)) d := by
            rw [hu]
      _ = 0 := hinnerShift

  have hd0 : d = 0 := (inner_self_eq_zero).1 hself
  have hyx : y = (x : LogHilbert) := by
    dsimp [d] at hd0
    exact sub_eq_zero.mp hd0

  rw [hyx]
  exact x.property

/-- The maximal coordinate domain is exactly the domain of the adjoint. -/
theorem coordinateOperator_domain_eq_adjoint :
    coordinateOperator.domain = (coordinateOperator†).domain := by
  apply le_antisymm
  · exact coordinateOperator_le_adjoint.1
  · exact coordinateAdjoint_domain_le

/-- The maximal real coordinate multiplication operator on `L²(ℝ,ℂ)` is
self-adjoint. -/
theorem coordinateOperator_selfAdjoint : IsSelfAdjoint coordinateOperator := by
  rw [LinearPMap.isSelfAdjoint_def]
  exact (LinearPMap.eq_of_le_of_domain_eq coordinateOperator_le_adjoint
    coordinateOperator_domain_eq_adjoint).symm

/-- Number III is therefore complete for the Fourier-side local operator `Q`. -/
theorem coordinateOperator_numberIII : NumberIII coordinateOperator := by
  exact (numberIII_iff_isSelfAdjoint coordinateOperator).2 coordinateOperator_selfAdjoint

end RiemannHypothesis.AdelicFlow
