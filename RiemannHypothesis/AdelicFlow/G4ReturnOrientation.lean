import RiemannHypothesis.AdelicFlow.G4TransverseGeometry

noncomputable section

namespace RiemannHypothesis.AdelicFlow

/-!
# G4 orientation of the prime return map

The real flow is `a_∞ ↦ e^t a_∞`.  At positive prime time
`t = m log p`, its archimedean scale is `p^m`, so the principal rational
compensator that restores the archimedean slice is `(p^m)⁻¹`.

At the distinguished p-adic place that compensator has norm `p^m`: positive
time is transversely expanding.  The inverse/negative-time return uses the
compensator `p^m`, whose p-adic norm is `p⁻m`: that is the contracting stable
return used by the G4 half-density.
-/

/-- Positive `m`-fold prime return time. -/
def positivePrimeReturnTime (p m : ℕ) : ℝ :=
  (m : ℝ) * Real.log (p : ℝ)

/-- Negative/inverse return time. -/
def negativePrimeReturnTime (p m : ℕ) : ℝ :=
  - positivePrimeReturnTime p m

/-- At positive prime time the archimedean exponential scale is exactly `p^m`. -/
theorem exp_positivePrimeReturnTime
    (p m : ℕ) (hp : Nat.Prime p) :
    Real.exp (positivePrimeReturnTime p m) = (p : ℝ) ^ m := by
  unfold positivePrimeReturnTime
  rw [← Real.log_pow]
  exact Real.exp_log (pow_pos (by exact_mod_cast hp.pos) m)

/-- At negative prime time the archimedean exponential scale is `p^{-m}`. -/
theorem exp_negativePrimeReturnTime
    (p m : ℕ) (hp : Nat.Prime p) :
    Real.exp (negativePrimeReturnTime p m) = ((p : ℝ) ^ m)⁻¹ := by
  unfold negativePrimeReturnTime
  rw [Real.exp_neg, exp_positivePrimeReturnTime p m hp]

/-- Principal rational correction for the positive-time return. -/
def positiveReturnCompensator (p m : ℕ) : ℚ :=
  ((p : ℚ) ^ m)⁻¹

/-- Principal rational correction for the inverse/negative-time return. -/
def negativeReturnCompensator (p m : ℕ) : ℚ :=
  (p : ℚ) ^ m

/-- The positive-time compensator has p-adic modulus `p^m`, so the positive
return is transversely expanding at the distinguished place. -/
theorem padic_positiveReturnCompensator
    (p m : ℕ) (hp : Nat.Prime p) :
    padicNorm p (positiveReturnCompensator p m) = (p : ℚ) ^ m := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : ((p : ℚ) ^ m) ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hdiv := padicNorm.div (p := p) (1 : ℚ) ((p : ℚ) ^ m)
  unfold positiveReturnCompensator
  simpa [one_div, padicNorm.one,
    padic_return_modulus_eq_inv_pow p m hp, hp0] using hdiv

/-- At every other prime, the positive-time compensator is still a local unit. -/
theorem padic_positiveReturnCompensator_off_diagonal
    (p q m : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hqp : q ≠ p) :
    padicNorm q (positiveReturnCompensator p m) = 1 := by
  letI : Fact q.Prime := ⟨hq⟩
  have hdiv := padicNorm.div (p := q) (1 : ℚ) ((p : ℚ) ^ m)
  unfold positiveReturnCompensator
  simpa [one_div, padicNorm.one,
    padic_off_diagonal_pow_unit p q m hp hq hqp] using hdiv

/-- The negative-time compensator has the contracting p-adic modulus `p^{-m}`. -/
theorem padic_negativeReturnCompensator
    (p m : ℕ) (hp : Nat.Prime p) :
    padicNorm p (negativeReturnCompensator p m) = ((p : ℚ) ^ m)⁻¹ := by
  unfold negativeReturnCompensator
  exact padic_return_modulus_eq_inv_pow p m hp

/-- At every other prime, the negative-time compensator has modulus one. -/
theorem padic_negativeReturnCompensator_off_diagonal
    (p q m : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hqp : q ≠ p) :
    padicNorm q (negativeReturnCompensator p m) = 1 := by
  unfold negativeReturnCompensator
  exact padic_off_diagonal_pow_unit p q m hp hq hqp

/-- Orientation summary: positive and negative prime returns have reciprocal
local p-adic moduli. -/
theorem primeReturnOrientation
    (p m : ℕ) (hp : Nat.Prime p) :
    padicNorm p (positiveReturnCompensator p m) = (p : ℚ) ^ m ∧
    padicNorm p (negativeReturnCompensator p m) = ((p : ℚ) ^ m)⁻¹ := by
  exact ⟨padic_positiveReturnCompensator p m hp,
    padic_negativeReturnCompensator p m hp⟩

end RiemannHypothesis.AdelicFlow
