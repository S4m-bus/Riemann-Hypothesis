import Mathlib

noncomputable section

namespace RiemannHypothesis.AdelicFlow

/-- A multiplicative scale `n` is primitive when `n ≥ 2` and it does not admit
    a nontrivial factorization into two smaller positive scales. -/
def IsPrimitiveScale (n : ℕ) : Prop :=
  2 ≤ n ∧ ¬ ∃ a b : ℕ, a < n ∧ b < n ∧ a * b = n

/-- Primitive multiplicative scales are exactly the prime numbers.  This is the
    arithmetic "no unwanted primitive cycles" statement for the scale monoid. -/
theorem primitiveScale_iff_prime {n : ℕ} :
    IsPrimitiveScale n ↔ Nat.Prime n := by
  constructor
  · rintro ⟨hn2, hnodecomp⟩
    by_contra hnp
    exact hnodecomp ((Nat.not_prime_iff_exists_mul_eq hn2).1 hnp)
  · intro hp
    refine ⟨hp.two_le, ?_⟩
    intro hdecomp
    exact ((Nat.not_prime_iff_exists_mul_eq hp.two_le).2 hdecomp) hp

/-- The logarithmic length of the `m`-fold repetition of a scale `p` is
    `m * log p`. -/
theorem log_length_pow (p m : ℕ) :
    Real.log (((p : ℝ) ^ m)) = (m : ℝ) * Real.log (p : ℝ) := by
  simpa using Real.log_pow (p : ℝ) m

/-- For a prime scale, the primitive arithmetic cycle has length `log p`. -/
def primeLength (p : ℕ) : ℝ := Real.log (p : ℝ)

/-- The repeated cycle length used by the trace formula. -/
def repeatedPrimeLength (p m : ℕ) : ℝ := (m : ℝ) * primeLength p

@[simp]
theorem repeatedPrimeLength_one (p : ℕ) :
    repeatedPrimeLength p 1 = primeLength p := by
  simp [repeatedPrimeLength]

end RiemannHypothesis.AdelicFlow
