import Mathlib

namespace RiemannHypothesis.AdelicFlow

/-- The exact local `p`-adic modulus for the `m`-fold return map `y ↦ p^m y`.
    We formulate it on `ℚ` through `padicNorm`, where mathlib already proves
    multiplicativity and `|p|_p = p⁻¹` for prime `p`. -/
theorem padic_return_modulus (p m : ℕ) (hp : Nat.Prime p) :
    padicNorm p ((p : ℚ) ^ m) = ((p : ℚ)⁻¹) ^ m := by
  letI : Fact p.Prime := ⟨hp⟩
  induction m with
  | zero =>
      simp [padicNorm.one]
  | succ m ih =>
      rw [pow_succ, padicNorm.mul, ih, padicNorm.padicNorm_p_of_prime, pow_succ]

/-- The local modulus is exactly `p^{-m}`. -/
theorem padic_return_modulus_eq_inv_pow (p m : ℕ) (hp : Nat.Prime p) :
    padicNorm p ((p : ℚ) ^ m) = ((p : ℚ) ^ m)⁻¹ := by
  rw [padic_return_modulus p m hp, inv_pow]

/-- At every different prime `q`, the scale `p` is a `q`-adic unit and has
    norm one. -/
theorem padic_off_diagonal_unit (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hqp : q ≠ p) :
    padicNorm q (p : ℚ) = 1 := by
  letI : Fact q.Prime := ⟨hq⟩
  letI : Fact p.Prime := ⟨hp⟩
  exact padicNorm.padicNorm_of_prime_of_ne hqp

/-- Consequently, at a different prime `q`, every repeated scale `p^m`
    still has `q`-adic norm one. -/
theorem padic_off_diagonal_pow_unit (p q m : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hqp : q ≠ p) :
    padicNorm q ((p : ℚ) ^ m) = 1 := by
  letI : Fact q.Prime := ⟨hq⟩
  induction m with
  | zero => simp [padicNorm.one]
  | succ m ih =>
      rw [pow_succ, padicNorm.mul, ih, padic_off_diagonal_unit p q hp hq hqp, one_mul]

end RiemannHypothesis.AdelicFlow
