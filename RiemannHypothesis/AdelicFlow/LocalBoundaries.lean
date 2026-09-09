import RiemannHypothesis.AdelicFlow.ArithmeticCycles
import RiemannHypothesis.AdelicFlow.LocalPrime

namespace RiemannHypothesis.AdelicFlow

/-- The exact local arithmetic obligations attached to a candidate prime cycle `p`.

This predicate deliberately separates the four pieces that later have to be glued
by a global adelic flow:

* primality / primitive arithmetic label;
* logarithmic period at the real place;
* the unique nontrivial finite-place modulus at `p`;
* unit modulus at every different prime `q`.
-/
def LocalPrimeBoundary (p : ℕ) : Prop :=
  Nat.Prime p ∧
  (∀ m : ℕ,
    repeatedPrimeLength p m = (m : ℝ) * Real.log (p : ℝ)) ∧
  (∀ m : ℕ,
    padicNorm p ((p : ℚ) ^ m) = ((p : ℚ) ^ m)⁻¹) ∧
  (∀ q m : ℕ,
    Nat.Prime q → q ≠ p →
      padicNorm q ((p : ℚ) ^ m) = 1)

/-- The local boundary conditions are available exactly for prime labels. -/
theorem localPrimeBoundary_iff_prime (p : ℕ) :
    LocalPrimeBoundary p ↔ Nat.Prime p := by
  constructor
  · intro h
    exact h.1
  · intro hp
    refine ⟨hp, ?_, ?_, ?_⟩
    · intro m
      simp [repeatedPrimeLength, primeLength]
    · intro m
      exact padic_return_modulus_eq_inv_pow p m hp
    · intro q m hq hqp
      exact padic_off_diagonal_pow_unit p q m hp hq hqp

/-- Boundary B0: primitive global arithmetic labels must coincide with primitive
multiplicative scales.  Since primitive scales are exactly primes, this is the
first anti-spurious-cycle condition for the global construction. -/
def PrimitiveLabelBoundary (primitiveCycle : ℕ → Prop) : Prop :=
  ∀ n : ℕ, primitiveCycle n ↔ IsPrimitiveScale n

/-- Boundary B∞: the archimedean/logarithmic period map must agree with repeated
prime length on every prime cycle. -/
def ArchimedeanPeriodBoundary (period : ℕ → ℕ → ℝ) : Prop :=
  ∀ p m : ℕ, Nat.Prime p →
    period p m = repeatedPrimeLength p m

/-- Boundary Bp: on the finite place indexed by the cycle prime itself, the
return modulus must be the exact p-adic norm of `p^m`. -/
def DiagonalFiniteBoundary (returnModulus : ℕ → ℕ → ℚ) : Prop :=
  ∀ p m : ℕ, Nat.Prime p →
    returnModulus p m = padicNorm p ((p : ℚ) ^ m)

/-- Boundary Bq≠p: a prime cycle must be a unit at every other finite place. -/
def OffDiagonalFiniteBoundary : Prop :=
  ∀ p q m : ℕ,
    Nat.Prime p → Nat.Prime q → q ≠ p →
      padicNorm q ((p : ℚ) ^ m) = 1

/-- Boundary Bprod: the finite local contributions of a p-cycle are supported
at a single finite place: its own p-adic component.  This is stated as the exact
pair of diagonal/off-diagonal conditions needed before taking any restricted
adelic product. -/
def SingleFiniteSupportBoundary : Prop :=
  (∀ p m : ℕ, Nat.Prime p →
    padicNorm p ((p : ℚ) ^ m) = ((p : ℚ) ^ m)⁻¹) ∧
  OffDiagonalFiniteBoundary

/-- All currently proved finite-place arithmetic bounds can be packaged without
assuming existence of a global adelic flow. -/
theorem singleFiniteSupportBoundary_proved : SingleFiniteSupportBoundary := by
  constructor
  · intro p m hp
    exact padic_return_modulus_eq_inv_pow p m hp
  · intro p q m hp hq hqp
    exact padic_off_diagonal_pow_unit p q m hp hq hqp

/-- The remaining gluing frontier.  An eventual global flow has to cross each
boundary below simultaneously.  No existence statement is asserted here. -/
structure GlobalGluingBoundary where
  primitiveCycle : ℕ → Prop
  period : ℕ → ℕ → ℝ
  returnModulus : ℕ → ℕ → ℚ

  primitiveLabels : PrimitiveLabelBoundary primitiveCycle
  archimedeanPeriods : ArchimedeanPeriodBoundary period
  diagonalFinite : DiagonalFiniteBoundary returnModulus

  /-- Distinct local prime sectors must be identified only through the global
  arithmetic quotient; locally they retain the unit condition at q ≠ p. -/
  offDiagonalFinite : OffDiagonalFiniteBoundary

  /-- Every primitive global orbit must arise from one arithmetic primitive
  label.  This field is intentionally separated from `primitiveLabels`: in the
  future geometric model it is the orbit-exhaustion/no-hidden-cycle theorem. -/
  noHiddenPrimitiveOrbit :
    ∀ n : ℕ, primitiveCycle n → Nat.Prime n

/-- Any object satisfying the local gluing interface automatically has exactly
prime primitive labels.  This is not yet existence of such an object. -/
theorem GlobalGluingBoundary.primitive_iff_prime
    (G : GlobalGluingBoundary) (n : ℕ) :
    G.primitiveCycle n ↔ Nat.Prime n := by
  rw [G.primitiveLabels n]
  exact primitiveScale_iff_prime

/-- A successful gluing object inherits the required prime repetition period. -/
theorem GlobalGluingBoundary.period_eq_log
    (G : GlobalGluingBoundary) (p m : ℕ) (hp : Nat.Prime p) :
    G.period p m = (m : ℝ) * Real.log (p : ℝ) := by
  rw [G.archimedeanPeriods p m hp]
  simp [repeatedPrimeLength, primeLength]

/-- A successful gluing object inherits the required p^{-m} finite return
modulus from the local p-adic boundary. -/
theorem GlobalGluingBoundary.returnModulus_eq_inv_pow
    (G : GlobalGluingBoundary) (p m : ℕ) (hp : Nat.Prime p) :
    G.returnModulus p m = ((p : ℚ) ^ m)⁻¹ := by
  rw [G.diagonalFinite p m hp]
  exact padic_return_modulus_eq_inv_pow p m hp

end RiemannHypothesis.AdelicFlow
