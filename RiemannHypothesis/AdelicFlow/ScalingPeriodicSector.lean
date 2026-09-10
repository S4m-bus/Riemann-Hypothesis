import Mathlib.Topology.Instances.AddCircle.Defs
import RiemannHypothesis.AdelicFlow.PrincipalQuotient

noncomputable section

namespace RiemannHypothesis.AdelicFlow

/-!
# G3: the prime periodic sector of the scaling flow

For each prime `p` we construct the logarithmic orbit

    C_p = ℝ / (log p)ℤ,

with translation flow.  We prove its full period lattice and that `log p` is its
least positive period.  The disjoint union over primes therefore has primitive
component labels exactly the primes.

This file only constructs and classifies the explicit prime circles.  The later
global theorem must identify these with the closed/cyclic-stabilizer orbits of
the maximal-compact adelic quotient.  Merely having one positive return time is
not sufficient for that global classification: points with several vanishing
finite components can have several incommensurable return times.
-/

abbrev PrimeLabel := {p : ℕ // Nat.Prime p}

def primeOrbitPeriod (p : PrimeLabel) : ℝ := Real.log (p.1 : ℝ)

theorem primeOrbitPeriod_pos (p : PrimeLabel) : 0 < primeOrbitPeriod p := by
  unfold primeOrbitPeriod
  apply Real.log_pos
  exact_mod_cast p.2.one_lt

abbrev PrimeOrbit (p : PrimeLabel) : Type := AddCircle (primeOrbitPeriod p)

def primeOrbitFlow (p : PrimeLabel) (t : ℝ) (x : PrimeOrbit p) : PrimeOrbit p :=
  (t : PrimeOrbit p) + x

@[simp]
theorem primeOrbitFlow_zero (p : PrimeLabel) (x : PrimeOrbit p) :
    primeOrbitFlow p 0 x = x := by
  simp [primeOrbitFlow]

theorem primeOrbitFlow_add (p : PrimeLabel) (s t : ℝ) (x : PrimeOrbit p) :
    primeOrbitFlow p (s + t) x =
      primeOrbitFlow p s (primeOrbitFlow p t x) := by
  change ((s + t : ℝ) : PrimeOrbit p) + x =
    (s : PrimeOrbit p) + ((t : PrimeOrbit p) + x)
  rw [AddCircle.coe_add]
  exact add_assoc _ _ _

@[simp]
theorem primeOrbitFlow_period (p : PrimeLabel) (x : PrimeOrbit p) :
    primeOrbitFlow p (primeOrbitPeriod p) x = x := by
  change (primeOrbitPeriod p : PrimeOrbit p) + x = x
  rw [AddCircle.coe_period]
  exact zero_add x

/-- A time translating every point back to itself. -/
def IsPrimeOrbitPeriod (p : PrimeLabel) (t : ℝ) : Prop :=
  ∀ x : PrimeOrbit p, primeOrbitFlow p t x = x

/-- Exact return-time lattice: all and only integer multiples of `log p`. -/
theorem isPrimeOrbitPeriod_iff_zmultiple (p : PrimeLabel) (t : ℝ) :
    IsPrimeOrbitPeriod p t ↔
      ∃ n : ℤ, n • primeOrbitPeriod p = t := by
  constructor
  · intro h
    have h0 := h (0 : PrimeOrbit p)
    have ht0 : (t : PrimeOrbit p) = 0 := by
      simpa [primeOrbitFlow] using h0
    exact (AddCircle.coe_eq_zero_iff (primeOrbitPeriod p)).1 ht0
  · rintro ⟨n, hn⟩
    have ht0 : (t : PrimeOrbit p) = 0 :=
      (AddCircle.coe_eq_zero_iff (primeOrbitPeriod p)).2 ⟨n, hn⟩
    intro x
    simp [primeOrbitFlow, ht0]

theorem primeOrbitPeriod_isPeriod (p : PrimeLabel) :
    IsPrimeOrbitPeriod p (primeOrbitPeriod p) := by
  intro x
  exact primeOrbitFlow_period p x

/-- A primitive period is a positive period no larger than any other positive
period. -/
def IsPrimitivePrimeOrbitPeriod (p : PrimeLabel) (t : ℝ) : Prop :=
  0 < t ∧ IsPrimeOrbitPeriod p t ∧
    ∀ s : ℝ, 0 < s → IsPrimeOrbitPeriod p s → t ≤ s

/-- `log p` is the least positive return time of the prime orbit. -/
theorem primeOrbitPeriod_isPrimitive (p : PrimeLabel) :
    IsPrimitivePrimeOrbitPeriod p (primeOrbitPeriod p) := by
  refine ⟨primeOrbitPeriod_pos p, primeOrbitPeriod_isPeriod p, ?_⟩
  intro s hs hperiod
  have h0 := hperiod (0 : PrimeOrbit p)
  have hs0 : (s : PrimeOrbit p) = 0 := by
    simpa [primeOrbitFlow] using h0
  rcases (AddCircle.coe_eq_zero_of_pos_iff
      (primeOrbitPeriod p) (primeOrbitPeriod_pos p) hs).1 hs0 with ⟨n, hn⟩
  have hn_ne : n ≠ 0 := by
    intro hn0
    subst n
    simp at hn
    exact (ne_of_gt hs) hn.symm
  have hn_one : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn_ne
  have hn_cast : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn_one
  have hn_real : (n : ℝ) * primeOrbitPeriod p = s := by
    simpa [nsmul_eq_mul] using hn
  nlinarith [primeOrbitPeriod_pos p]

/-- The full constructed prime-periodic sector. -/
abbrev PrimePeriodicSector : Type :=
  Sigma fun p : PrimeLabel => PrimeOrbit p

def primePeriodicSectorFlow (t : ℝ) (x : PrimePeriodicSector) : PrimePeriodicSector :=
  ⟨x.1, primeOrbitFlow x.1 t x.2⟩

@[simp]
theorem primePeriodicSectorFlow_zero (x : PrimePeriodicSector) :
    primePeriodicSectorFlow 0 x = x := by
  rcases x with ⟨p, x⟩
  simp [primePeriodicSectorFlow]

theorem primePeriodicSectorFlow_add (s t : ℝ) (x : PrimePeriodicSector) :
    primePeriodicSectorFlow (s + t) x =
      primePeriodicSectorFlow s (primePeriodicSectorFlow t x) := by
  rcases x with ⟨p, x⟩
  simp [primePeriodicSectorFlow, primeOrbitFlow_add]

def primeOrbitBasepoint (p : PrimeLabel) : PrimePeriodicSector :=
  ⟨p, 0⟩

theorem primeOrbitBasepoint_returns (p : PrimeLabel) :
    primePeriodicSectorFlow (primeOrbitPeriod p) (primeOrbitBasepoint p) =
      primeOrbitBasepoint p := by
  simp [primePeriodicSectorFlow, primeOrbitBasepoint]

theorem periodicSector_label_prime (x : PrimePeriodicSector) :
    Nat.Prime x.1.1 := x.1.2

theorem prime_has_periodic_component (p : ℕ) (hp : Nat.Prime p) :
    ∃ x : PrimePeriodicSector, x.1.1 = p := by
  exact ⟨primeOrbitBasepoint ⟨p, hp⟩, rfl⟩

theorem periodicSector_labels_exactly_primes (n : ℕ) :
    (∃ x : PrimePeriodicSector, x.1.1 = n) ↔ Nat.Prime n := by
  constructor
  · rintro ⟨x, rfl⟩
    exact periodicSector_label_prime x
  · intro hn
    exact prime_has_periodic_component n hn

/-- A natural-number label occurs as one of the constructed primitive orbit
components. -/
def HasConstructedPrimitiveOrbit (n : ℕ) : Prop :=
  ∃ hp : Nat.Prime n,
    IsPrimitivePrimeOrbitPeriod (⟨n, hp⟩ : PrimeLabel)
      (primeOrbitPeriod (⟨n, hp⟩ : PrimeLabel))

/-- Primitive component labels in the constructed G3 periodic sector are exactly
prime numbers. -/
theorem constructedPrimitiveOrbits_iff_prime (n : ℕ) :
    HasConstructedPrimitiveOrbit n ↔ Nat.Prime n := by
  constructor
  · rintro ⟨hp, _⟩
    exact hp
  · intro hp
    exact ⟨hp, primeOrbitPeriod_isPrimitive (⟨n, hp⟩ : PrimeLabel)⟩

end RiemannHypothesis.AdelicFlow
