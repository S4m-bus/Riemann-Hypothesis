import RiemannHypothesis.AdelicFlow.ArchimedeanFlow
import RiemannHypothesis.AdelicFlow.ScalingPeriodicSector

noncomputable section

namespace RiemannHypothesis.AdelicFlow

/-!
# G3 global bridge: closed orbits of the scaling-site quotient

The prime circles constructed in `ScalingPeriodicSector.lean` belong naturally
to a further quotient of the principal adele class space by the maximal compact
finite-idelic subgroup.

A crucial distinction is enforced here: a point having one positive return time
is NOT by itself a primitive closed orbit.  Points with several vanishing finite
components can carry several incommensurable return times.  The correct G3
object is a point/component whose stabilizer is a discrete cyclic lattice
`Tℤ`.  Prime circles have precisely the stabilizer `(log p)ℤ`.
-/

/-- Interface for a scaling-site quotient carrying the descended real scaling
flow. -/
structure ScalingSiteQuotientBoundary where
  X : Type
  project : PrincipalQuotient → X
  flow : ℝ → X → X

  flow_zero : ∀ x, flow 0 x = x
  flow_add : ∀ s t x, flow (s + t) x = flow s (flow t x)

  project_intertwines : ∀ t x,
    project (principalArchimedeanFlow t x) = flow t (project x)

/-- A point has a genuine closed-orbit stabilizer of primitive length `T` when
its complete return-time set is exactly `Tℤ`. -/
def HasCyclicStabilizer (S : ScalingSiteQuotientBoundary)
    (y : S.X) (T : ℝ) : Prop :=
  0 < T ∧ ∀ t : ℝ,
    S.flow t y = y ↔ ∃ n : ℤ, n • T = t

/-- A point lies on a closed primitive orbit if its stabilizer is a nonzero
cyclic lattice. -/
def LiesOnClosedPrimitiveOrbit (S : ScalingSiteQuotientBoundary)
    (y : S.X) : Prop :=
  ∃ T : ℝ, HasCyclicStabilizer S y T

/-- Complete G3 bridge obligation.  It asks that the explicit prime circles
embed equivariantly and exhaust the cyclic-stabilizer (closed-orbit) locus,
not every point with an isolated positive return. -/
structure G3ScalingSiteBridge where
  site : ScalingSiteQuotientBoundary
  embedPeriodicSector : PrimePeriodicSector → site.X
  embed_injective : Function.Injective embedPeriodicSector

  intertwining : ∀ t x,
    embedPeriodicSector (primePeriodicSectorFlow t x) =
      site.flow t (embedPeriodicSector x)

  closedOrbitExhaustion : ∀ y : site.X,
    LiesOnClosedPrimitiveOrbit site y →
      ∃ x : PrimePeriodicSector, embedPeriodicSector x = y

/-- A time is a period of the entire embedded `p`-circle. -/
def IsEmbeddedPrimePeriod (G : G3ScalingSiteBridge)
    (p : PrimeLabel) (t : ℝ) : Prop :=
  ∀ x : PrimeOrbit p,
    G.site.flow t (G.embedPeriodicSector ⟨p, x⟩) =
      G.embedPeriodicSector ⟨p, x⟩

/-- Injectivity and intertwining make the global embedded period condition
exactly equivalent to the already proved local circle period condition. -/
theorem G3ScalingSiteBridge.embeddedPrimePeriod_iff
    (G : G3ScalingSiteBridge) (p : PrimeLabel) (t : ℝ) :
    IsEmbeddedPrimePeriod G p t ↔ IsPrimeOrbitPeriod p t := by
  constructor
  · intro h x
    apply G.embed_injective
    rw [G.intertwining]
    exact h x
  · intro h x
    rw [← G.intertwining, h x]

/-- Primitive positive period for an embedded global prime circle. -/
def IsPrimitiveEmbeddedPrimePeriod (G : G3ScalingSiteBridge)
    (p : PrimeLabel) (t : ℝ) : Prop :=
  0 < t ∧ IsEmbeddedPrimePeriod G p t ∧
    ∀ s : ℝ, 0 < s → IsEmbeddedPrimePeriod G p s → t ≤ s

/-- Once the bridge exists, the primitive period of the embedded `p`-orbit is
forced to remain exactly `log p`. -/
theorem G3ScalingSiteBridge.primePeriod_isPrimitive
    (G : G3ScalingSiteBridge) (p : PrimeLabel) :
    IsPrimitiveEmbeddedPrimePeriod G p (primeOrbitPeriod p) := by
  have hlocal := primeOrbitPeriod_isPrimitive p
  refine ⟨hlocal.1, ?_, ?_⟩
  · exact (G.embeddedPrimePeriod_iff p (primeOrbitPeriod p)).2 hlocal.2.1
  · intro s hs hperiod
    apply hlocal.2.2 s hs
    exact (G.embeddedPrimePeriod_iff p s).1 hperiod

/-- Under the corrected bridge, every point on a genuine closed primitive orbit
has a representative in a prime circle. -/
theorem G3ScalingSiteBridge.closed_orbit_has_prime_representative
    (G : G3ScalingSiteBridge) (y : G.site.X)
    (hy : LiesOnClosedPrimitiveOrbit G.site y) :
    ∃ x : PrimePeriodicSector,
      G.embedPeriodicSector x = y ∧ Nat.Prime x.1.1 := by
  rcases G.closedOrbitExhaustion y hy with ⟨x, hx⟩
  exact ⟨x, hx, periodicSector_label_prime x⟩

/-- Correct G3 package: prime fibers have exact primitive length `log p`, and
all cyclic-stabilizer closed orbits are exhausted by those prime fibers. -/
theorem G3ScalingSiteBridge.G3_prime_orbit_package
    (G : G3ScalingSiteBridge) :
    (∀ p : PrimeLabel,
      IsPrimitiveEmbeddedPrimePeriod G p (primeOrbitPeriod p)) ∧
    (∀ y : G.site.X,
      LiesOnClosedPrimitiveOrbit G.site y →
        ∃ x : PrimePeriodicSector,
          G.embedPeriodicSector x = y ∧ Nat.Prime x.1.1) := by
  constructor
  · intro p
    exact G.primePeriod_isPrimitive p
  · intro y hy
    exact G.closed_orbit_has_prime_representative y hy

end RiemannHypothesis.AdelicFlow
