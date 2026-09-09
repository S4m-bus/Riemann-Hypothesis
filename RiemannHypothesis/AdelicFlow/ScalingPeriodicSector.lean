import Mathlib.Topology.Instances.AddCircle.Defs
import RiemannHypothesis.AdelicFlow.PrincipalQuotient

noncomputable section

namespace RiemannHypothesis.AdelicFlow

/-!
# G3: the prime periodic sector of the scaling flow

The periodic orbit attached to a prime `p` is modeled in logarithmic coordinates
by

    ℝ / (log p)ℤ.

This is the additive form of the classical scaling orbit

    ℝ₊ˣ / p^ℤ.

The file constructs the translation flow on every prime orbit, proves its exact
period lattice, and assembles all prime fibers into one periodic sector.

Important boundary: this file does NOT yet prove that this periodic sector
exhausts the periodic points of the adelic quotient from `PrincipalQuotient.lean`.
That local-to-global identification is isolated at the end as the remaining G3
adelic bridge theorem.
-/

/-- A prime together with its proof of primality. -/
abbrev PrimeLabel := {p : ℕ // Nat.Prime p}

/-- The positive logarithmic period attached to a prime. -/
def primeOrbitPeriod (p : PrimeLabel) : ℝ := Real.log (p.1 : ℝ)

/-- Prime logarithmic periods are strictly positive. -/
theorem primeOrbitPeriod_pos (p : PrimeLabel) : 0 < primeOrbitPeriod p := by
  unfold primeOrbitPeriod
  apply Real.log_pos
  exact_mod_cast p.2.one_lt

/-- The logarithmic prime orbit `C_p = ℝ / (log p)ℤ`. -/
abbrev PrimeOrbit (p : PrimeLabel) : Type := AddCircle (primeOrbitPeriod p)

/-- Translation by logarithmic time on the prime orbit. -/
def primeOrbitFlow (p : PrimeLabel) (t : ℝ) (x : PrimeOrbit p) : PrimeOrbit p :=
  (t : PrimeOrbit p) + x

@[simp]
theorem primeOrbitFlow_zero (p : PrimeLabel) (x : PrimeOrbit p) :
    primeOrbitFlow p 0 x = x := by
  simp [primeOrbitFlow]

/-- The translation maps form an additive `ℝ`-flow. -/
theorem primeOrbitFlow_add (p : PrimeLabel) (s t : ℝ) (x : PrimeOrbit p) :
    primeOrbitFlow p (s + t) x =
      primeOrbitFlow p s (primeOrbitFlow p t x) := by
  change ((s + t : ℝ) : PrimeOrbit p) + x =
    (s : PrimeOrbit p) + ((t : PrimeOrbit p) + x)
  rw [AddCircle.coe_add]
  exact add_assoc _ _ _

/-- Every point of the `p`-orbit returns after time `log p`. -/
@[simp]
theorem primeOrbitFlow_period (p : PrimeLabel) (x : PrimeOrbit p) :
    primeOrbitFlow p (primeOrbitPeriod p) x = x := by
  change (primeOrbitPeriod p : PrimeOrbit p) + x = x
  rw [AddCircle.coe_period]
  exact zero_add x

/-- A real time is a global return time for the entire prime orbit. -/
def IsPrimeOrbitPeriod (p : PrimeLabel) (t : ℝ) : Prop :=
  ∀ x : PrimeOrbit p, primeOrbitFlow p t x = x

/-- The exact period lattice of the `p`-orbit is `(log p)ℤ`.

This is the rigorous periodicity statement needed later for primitive-orbit
classification: no period can occur unless it is an integer multiple of `log p`.
-/
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

/-- The fundamental logarithmic time really is a period. -/
theorem primeOrbitPeriod_isPeriod (p : PrimeLabel) :
    IsPrimeOrbitPeriod p (primeOrbitPeriod p) := by
  intro x
  exact primeOrbitFlow_period p x

/-- The disjoint union of all prime periodic scaling orbits. -/
abbrev PrimePeriodicSector : Type :=
  Sigma fun p : PrimeLabel => PrimeOrbit p

/-- The logarithmic flow on the full prime-periodic sector, acting fiberwise. -/
def primePeriodicSectorFlow (t : ℝ) (x : PrimePeriodicSector) : PrimePeriodicSector :=
  ⟨x.1, primeOrbitFlow x.1 t x.2⟩

@[simp]
theorem primePeriodicSectorFlow_zero (x : PrimePeriodicSector) :
    primePeriodicSectorFlow 0 x = x := by
  rcases x with ⟨p, x⟩
  simp [primePeriodicSectorFlow]

/-- The assembled periodic sector is itself an `ℝ`-flow. -/
theorem primePeriodicSectorFlow_add (s t : ℝ) (x : PrimePeriodicSector) :
    primePeriodicSectorFlow (s + t) x =
      primePeriodicSectorFlow s (primePeriodicSectorFlow t x) := by
  rcases x with ⟨p, x⟩
  simp [primePeriodicSectorFlow, primeOrbitFlow_add]

/-- Distinguished point on the prime orbit, used as an orbit representative. -/
def primeOrbitBasepoint (p : PrimeLabel) : PrimePeriodicSector :=
  ⟨p, 0⟩

/-- The distinguished `p`-point closes after exactly the expected basic return
length at the level of the prime fiber. -/
theorem primeOrbitBasepoint_returns (p : PrimeLabel) :
    primePeriodicSectorFlow (primeOrbitPeriod p) (primeOrbitBasepoint p) =
      primeOrbitBasepoint p := by
  simp [primePeriodicSectorFlow, primeOrbitBasepoint]

/-- Every component label of the constructed periodic sector is prime. -/
theorem periodicSector_label_prime (x : PrimePeriodicSector) :
    Nat.Prime x.1.1 :=
  x.1.2

/-- Conversely every prime has a canonical periodic component. -/
theorem prime_has_periodic_component (p : ℕ) (hp : Nat.Prime p) :
    ∃ x : PrimePeriodicSector, x.1.1 = p := by
  exact ⟨primeOrbitBasepoint ⟨p, hp⟩, rfl⟩

/-- Thus the connected-component labels of the constructed prime-periodic sector
are exactly the primes.  The stronger statement that these are exactly all
primitive periodic components of the adelic quotient is the bridge obligation
below, not an assumption hidden in this theorem. -/
theorem periodicSector_labels_exactly_primes (n : ℕ) :
    (∃ x : PrimePeriodicSector, x.1.1 = n) ↔ Nat.Prime n := by
  constructor
  · rintro ⟨x, rfl⟩
    exact periodicSector_label_prime x
  · intro hn
    exact prime_has_periodic_component n hn

/-! ## Remaining G3 adelic bridge

To turn the explicit periodic-sector construction above into a theorem about the
actual principal adelic quotient, we must exhibit a quotient flow and prove that
its positive-periodic locus is exactly the image of this sector.  Keeping this as
a structure prevents the formalization from silently assuming the decisive
orbit-exhaustion statement.
-/

/-- Exact remaining G3 boundary between the constructed prime periodic sector
and the actual adelic principal quotient. -/
structure G3AdelicPeriodicBridge where
  quotientDynamics : QuotientFlowBoundary
  embedPeriodicSector : PrimePeriodicSector → PrincipalQuotient
  embed_injective : Function.Injective embedPeriodicSector

  /-- The explicit logarithmic translation flow must agree with the descended
  adelic flow on the periodic sector. -/
  intertwining : ∀ t x,
    embedPeriodicSector (primePeriodicSectorFlow t x) =
      quotientDynamics.quotientFlow t (embedPeriodicSector x)

  /-- No hidden positive-periodic points: every periodic point of the quotient
  must come from one of the prime fibers constructed above. -/
  periodic_exhaustion : ∀ y : PrincipalQuotient,
    (∃ t : ℝ, 0 < t ∧ quotientDynamics.quotientFlow t y = y) →
      ∃ x : PrimePeriodicSector, embedPeriodicSector x = y

/-- If the G3 adelic bridge is proved, every positive-periodic quotient point is
represented by a uniquely embedded prime-sector point. -/
theorem G3AdelicPeriodicBridge.periodic_point_has_prime_representative
    (G : G3AdelicPeriodicBridge) (y : PrincipalQuotient)
    (hy : ∃ t : ℝ, 0 < t ∧ G.quotientDynamics.quotientFlow t y = y) :
    ∃ x : PrimePeriodicSector,
      G.embedPeriodicSector x = y ∧ Nat.Prime x.1.1 := by
  rcases G.periodic_exhaustion y hy with ⟨x, hx⟩
  exact ⟨x, hx, periodicSector_label_prime x⟩

end RiemannHypothesis.AdelicFlow
