import RiemannHypothesis.AdelicFlow.LocalPrime

noncomputable section

namespace RiemannHypothesis.AdelicFlow

/-!
# G4 return-modulus sanity check

For the `m`-fold prime scale `p^m`, the finite local modulus is `p^{-m}` at
`p` and `1` at every other prime.  We package the product over all finite
primes with `finprod`, setting non-prime indices to `1`.

A separate sanity check records the product-formula issue: if one also includes
the ordinary archimedean absolute-value modulus `p^m`, the full adelic product
is `1`, not `p^{-m}`.  Thus the desired `p^{-m/2}` half-density must come from
a transverse/finite modulus in which the orbit-direction archimedean factor is
removed (or normalized to `1`), not from the unmodified full adelic modulus.
-/

/-- Local finite factor at an index `q`. Non-primes are assigned the neutral
factor `1`, so `finprod` literally ranges over all natural indices while only
prime places contribute. -/
def finiteLocalReturnModulus (p m q : ℕ) : ℚ :=
  if hq : Nat.Prime q then padicNorm q ((p : ℚ) ^ m) else 1

/-- At the distinguished prime `p`, the local factor is exactly `p^{-m}`. -/
theorem finiteLocalReturnModulus_at_prime
    (p m : ℕ) (hp : Nat.Prime p) :
    finiteLocalReturnModulus p m p = ((p : ℚ) ^ m)⁻¹ := by
  simp [finiteLocalReturnModulus, hp,
    padic_return_modulus_eq_inv_pow p m hp]

/-- At every different index, the local factor is `1`: for a different prime
this is the off-diagonal p-adic unit theorem, and for a non-prime it holds by
definition. -/
theorem finiteLocalReturnModulus_off_diagonal
    (p q m : ℕ) (hp : Nat.Prime p) (hqp : q ≠ p) :
    finiteLocalReturnModulus p m q = 1 := by
  by_cases hq : Nat.Prime q
  · simp [finiteLocalReturnModulus, hq,
      padic_off_diagonal_pow_unit p q m hp hq hqp]
  · simp [finiteLocalReturnModulus, hq]

/-- Product of all finite local return moduli. -/
def finiteReturnModulus (p m : ℕ) : ℚ :=
  ∏ᶠ q : ℕ, finiteLocalReturnModulus p m q

/-- The complete finite-place product is exactly `p^{-m}`. -/
theorem finiteReturnModulus_eq_inv_pow
    (p m : ℕ) (hp : Nat.Prime p) :
    finiteReturnModulus p m = ((p : ℚ) ^ m)⁻¹ := by
  unfold finiteReturnModulus
  rw [finprod_eq_single (finiteLocalReturnModulus p m) p]
  · exact finiteLocalReturnModulus_at_prime p m hp
  · intro q hqp
    exact finiteLocalReturnModulus_off_diagonal p q m hp hqp

/-- Ordinary archimedean modulus of multiplication by `p^m`, written in `ℚ`
only so it can be multiplied directly with the finite product above. -/
def archimedeanReturnModulus (p m : ℕ) : ℚ := (p : ℚ) ^ m

/-- Unmodified product over the archimedean and all finite places. -/
def fullAdelicReturnModulus (p m : ℕ) : ℚ :=
  archimedeanReturnModulus p m * finiteReturnModulus p m

/-- Product-formula sanity check: the ordinary archimedean factor `p^m`
cancels the finite factor `p^{-m}`. -/
theorem fullAdelicReturnModulus_eq_one
    (p m : ℕ) (hp : Nat.Prime p) :
    fullAdelicReturnModulus p m = 1 := by
  have hp0 : (p : ℚ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  simp [fullAdelicReturnModulus, archimedeanReturnModulus,
    finiteReturnModulus_eq_inv_pow p m hp, hp0]

/-- The positive half-density associated to the finite/transverse modulus.
For a prime `p` this is the rigorous square-root form of `p^{-m/2}`. -/
def finiteReturnHalfDensity (p m : ℕ) : ℝ :=
  Real.sqrt (((p : ℝ) ^ m)⁻¹)

/-- Kernel-level half-density check: squaring the half-density recovers the
finite return modulus `p^{-m}`. -/
theorem finiteReturnHalfDensity_sq
    (p m : ℕ) (hp : Nat.Prime p) :
    (finiteReturnHalfDensity p m) ^ 2 = ((p : ℝ) ^ m)⁻¹ := by
  unfold finiteReturnHalfDensity
  rw [Real.sq_sqrt]
  positivity

end RiemannHypothesis.AdelicFlow
