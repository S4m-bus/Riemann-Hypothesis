import RiemannHypothesis.AdelicFlow.G4PoincareReturn

noncomputable section

namespace RiemannHypothesis.AdelicFlow

/-!
# G4: corrected global returns and their transverse projections

The transverse maps from `G4PoincareReturn` are not introduced independently
of the global flow.  Once the principal rational compensator is fixed, they are
exactly the finite projections of the compensated global archimedean flow.

This file proves that compatibility on the exposed pre-quotient adelic product.
Whether a given compensated time is a genuine closed-orbit return in the final
scaling-site quotient is the separate G3 orbit-classification obligation.
-/

/-- Corrected positive-time global map: flow for `+m log p` and compensate by
`p^{-m}` so that the archimedean scaling can return to a normalized slice. -/
def positiveCorrectedGlobalReturn
    (p m : ℕ) (hp : Nat.Prime p) (a : GlobalSpace) : GlobalSpace :=
  globalScale (primePowerUnit p m hp)⁻¹
    (archimedeanGlobalFlow (positivePrimeReturnTime p m) a)

/-- Corrected inverse/negative-time global map: flow for `-m log p` and
compensate by `p^m`.  This is the stable orientation. -/
def stableCorrectedGlobalReturn
    (p m : ℕ) (hp : Nat.Prime p) (a : GlobalSpace) : GlobalSpace :=
  globalScale (primePowerUnit p m hp)
    (archimedeanGlobalFlow (negativePrimeReturnTime p m) a)

/-- General compatibility: after archimedean flow and rational compensation,
the finite transverse coordinate sees exactly the rational finite scaling. -/
theorem transverseProjection_corrected_globalScale
    (u : ℚˣ) (t : ℝ) (a : GlobalSpace) :
    transverseProjection (globalScale u (archimedeanGlobalFlow t a)) =
      finiteScale u (transverseProjection a) := rfl

/-- The positive corrected global return projects exactly to the expanding
positive transverse return. -/
theorem transverseProjection_positiveCorrectedGlobalReturn
    (p m : ℕ) (hp : Nat.Prime p) (a : GlobalSpace) :
    transverseProjection (positiveCorrectedGlobalReturn p m hp a) =
      positiveTransverseReturn p m hp (transverseProjection a) := rfl

/-- The inverse/negative corrected global return projects exactly to the stable
contracting transverse return. -/
theorem transverseProjection_stableCorrectedGlobalReturn
    (p m : ℕ) (hp : Nat.Prime p) (a : GlobalSpace) :
    transverseProjection (stableCorrectedGlobalReturn p m hp a) =
      stableTransverseReturn p m hp (transverseProjection a) := rfl

/-- Applying the positive and stable corrected maps in succession restores the
finite transverse coordinate. -/
theorem transverseProjection_positive_after_stable_corrected
    (p m : ℕ) (hp : Nat.Prime p) (a : GlobalSpace) :
    transverseProjection
      (positiveCorrectedGlobalReturn p m hp
        (stableCorrectedGlobalReturn p m hp a)) =
      transverseProjection a := by
  rw [transverseProjection_positiveCorrectedGlobalReturn,
    transverseProjection_stableCorrectedGlobalReturn]
  exact positive_after_stable_return p m hp (transverseProjection a)

/-- Conversely, stable after positive also restores the transverse coordinate. -/
theorem transverseProjection_stable_after_positive_corrected
    (p m : ℕ) (hp : Nat.Prime p) (a : GlobalSpace) :
    transverseProjection
      (stableCorrectedGlobalReturn p m hp
        (positiveCorrectedGlobalReturn p m hp a)) =
      transverseProjection a := by
  rw [transverseProjection_stableCorrectedGlobalReturn,
    transverseProjection_positiveCorrectedGlobalReturn]
  exact stable_after_positive_return p m hp (transverseProjection a)

end RiemannHypothesis.AdelicFlow
