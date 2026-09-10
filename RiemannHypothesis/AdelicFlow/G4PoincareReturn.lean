import RiemannHypothesis.AdelicFlow.G4ReturnOrientation

noncomputable section

namespace RiemannHypothesis.AdelicFlow

/-!
# G4 candidate Poincare return maps on the finite transversal

For a prime `p` and repetition `m`, let `u = p^m ∈ ℚˣ`.  The positive-time
archimedean return is normalized by `u⁻¹`, while the inverse/negative-time
return is normalized by `u`.  On the finite transversal these give mutually
inverse maps

    y ↦ u⁻¹ y,
    y ↦ u y.

The second map is the contracting/stable orientation at the p-adic place and
has local modulus `p^{-m}`.

This is a pre-quotient transverse construction.  Identifying it with the true
Poincare map of every global prime orbit still depends on the G3 orbit
exhaustion theorem.
-/

/-- The rational unit represented by the nonzero prime power `p^m`. -/
def primePowerUnit (p m : ℕ) (hp : Nat.Prime p) : ℚˣ :=
  Units.mk0 ((p : ℚ) ^ m) (by
    exact pow_ne_zero _ (by exact_mod_cast hp.ne_zero))

@[simp]
theorem coe_primePowerUnit (p m : ℕ) (hp : Nat.Prime p) :
    ((primePowerUnit p m hp : ℚˣ) : ℚ) = (p : ℚ) ^ m := rfl

/-- Positive-time normalized return on the finite transversal. -/
def positiveTransverseReturn
    (p m : ℕ) (hp : Nat.Prime p)
    (y : PrequotientTransverseCarrier) : PrequotientTransverseCarrier :=
  finiteScale (primePowerUnit p m hp)⁻¹ y

/-- Negative-time/inverse normalized return on the finite transversal. -/
def stableTransverseReturn
    (p m : ℕ) (hp : Nat.Prime p)
    (y : PrequotientTransverseCarrier) : PrequotientTransverseCarrier :=
  finiteScale (primePowerUnit p m hp) y

/-- The positive and stable returns are inverse maps. -/
theorem positive_after_stable_return
    (p m : ℕ) (hp : Nat.Prime p)
    (y : PrequotientTransverseCarrier) :
    positiveTransverseReturn p m hp (stableTransverseReturn p m hp y) = y := by
  unfold positiveTransverseReturn stableTransverseReturn
  rw [← finiteScale_mul]
  simp

/-- The inverse composition also cancels. -/
theorem stable_after_positive_return
    (p m : ℕ) (hp : Nat.Prime p)
    (y : PrequotientTransverseCarrier) :
    stableTransverseReturn p m hp (positiveTransverseReturn p m hp y) = y := by
  unfold positiveTransverseReturn stableTransverseReturn
  rw [← finiteScale_mul]
  simp

/-- The scalar of the stable return has exactly the desired p-adic modulus. -/
theorem stableTransverseReturn_scalar_modulus
    (p m : ℕ) (hp : Nat.Prime p) :
    padicNorm p ((primePowerUnit p m hp : ℚˣ) : ℚ) = ((p : ℚ) ^ m)⁻¹ := by
  change padicNorm p ((p : ℚ) ^ m) = ((p : ℚ) ^ m)⁻¹
  exact padic_return_modulus_eq_inv_pow p m hp

/-- The positive-time return has the reciprocal p-adic modulus `p^m`. -/
theorem positiveTransverseReturn_scalar_modulus
    (p m : ℕ) (hp : Nat.Prime p) :
    padicNorm p (((primePowerUnit p m hp)⁻¹ : ℚˣ) : ℚ) = (p : ℚ) ^ m := by
  simpa [primePowerUnit, positiveReturnCompensator] using
    padic_positiveReturnCompensator p m hp

/-- At all different prime places, the stable return scalar is a local unit. -/
theorem stableTransverseReturn_off_diagonal
    (p q m : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hqp : q ≠ p) :
    padicNorm q ((primePowerUnit p m hp : ℚˣ) : ℚ) = 1 := by
  change padicNorm q ((p : ℚ) ^ m) = 1
  exact padic_off_diagonal_pow_unit p q m hp hq hqp

/-- G4 transverse-map summary: the stable return is invertible, has modulus
`p^{-m}` at `p`, and modulus one at every other prime. -/
theorem G4_stable_return_map_summary
    (p m : ℕ) (hp : Nat.Prime p) :
    (∀ y : PrequotientTransverseCarrier,
      positiveTransverseReturn p m hp (stableTransverseReturn p m hp y) = y) ∧
    padicNorm p ((primePowerUnit p m hp : ℚˣ) : ℚ) = ((p : ℚ) ^ m)⁻¹ ∧
    (∀ q : ℕ, Nat.Prime q → q ≠ p →
      padicNorm q ((primePowerUnit p m hp : ℚˣ) : ℚ) = 1) := by
  refine ⟨positive_after_stable_return p m hp, ?_, ?_⟩
  · exact stableTransverseReturn_scalar_modulus p m hp
  · intro q hq hqp
    exact stableTransverseReturn_off_diagonal p q m hp hq hqp

end RiemannHypothesis.AdelicFlow
