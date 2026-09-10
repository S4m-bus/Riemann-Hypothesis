import RiemannHypothesis.AdelicFlow.ReturnWitness
import RiemannHypothesis.AdelicFlow.ScalingSiteBoundary

noncomputable section

namespace RiemannHypothesis.AdelicFlow

/-!
# Necessary archimedean condition for G3 closed orbits

The singleton finite-zero criterion is meaningful only on the nonzero
archimedean stratum.  If the infinite component vanishes, the real scaling
flow fixes the representative for every real time, so its stabilizer is all of
`ℝ` rather than a discrete cyclic lattice.
-/

/-- Vanishing of the infinite component makes the global archimedean flow
pointwise stationary. -/
theorem archimedeanGlobalFlow_fixed_of_infinite_zero
    (a : GlobalSpace) (ha : a.1 = 0) (t : ℝ) :
    archimedeanGlobalFlow t a = a := by
  apply Prod.ext
  · change rationalInfiniteRealFlow t a.1 = a.1
    rw [ha]
    simp [rationalInfiniteRealFlow]
  · rfl

/-- Hence the twice-quotiented scaling-site class is fixed for every real
parameter as well. -/
theorem scalingSiteClass_fixed_of_infinite_zero
    (a : GlobalSpace) (ha : a.1 = 0) (t : ℝ) :
    scalingSiteFlow t (scalingSiteClass a) = scalingSiteClass a := by
  change toScalingSiteQuotient
      (toPrincipalQuotient (archimedeanGlobalFlow t a)) =
    toScalingSiteQuotient (toPrincipalQuotient a)
  rw [archimedeanGlobalFlow_fixed_of_infinite_zero a ha t]

/-- Any point fixed by every real time has stabilizer `ℝ`, hence cannot have a
positive discrete cyclic stabilizer `Tℤ`. -/
theorem not_closedPrimitive_of_fixed_all
    {S : ScalingSiteQuotientBoundary} {y : S.X}
    (hfix : ∀ t : ℝ, S.flow t y = y) :
    ¬ LiesOnClosedPrimitiveOrbit S y := by
  rintro ⟨T, hT, hperiod⟩
  have hhalf := hfix (T / 2)
  rcases (hperiod (T / 2)).1 hhalf with ⟨n, hn⟩
  rw [zsmul_eq_mul] at hn
  have hnHalf : (n : ℝ) = (1 / 2 : ℝ) := by
    apply mul_right_cancel₀ hT.ne'
    calc
      (n : ℝ) * T = T / 2 := hn
      _ = (1 / 2 : ℝ) * T := by ring
  have hcases : n ≤ 0 ∨ 1 ≤ n := by omega
  rcases hcases with hn0 | hn1
  · have hn0' : (n : ℝ) ≤ 0 := by exact_mod_cast hn0
    linarith
  · have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith

/-- Kernel-level necessary condition for any genuine G3 closed primitive orbit:
the representative's infinite component must be nonzero. -/
theorem closedPrimitive_implies_infinite_ne_zero
    (a : GlobalSpace)
    (hclosed : LiesOnClosedPrimitiveOrbit actualScalingSiteQuotientBoundary
      (scalingSiteClass a)) :
    a.1 ≠ 0 := by
  intro ha
  apply not_closedPrimitive_of_fixed_all
    (S := actualScalingSiteQuotientBoundary)
    (y := scalingSiteClass a)
  · intro t
    exact scalingSiteClass_fixed_of_infinite_zero a ha t
  · exact hclosed

end RiemannHypothesis.AdelicFlow
