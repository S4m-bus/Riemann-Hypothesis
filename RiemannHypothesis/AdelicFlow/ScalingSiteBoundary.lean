import RiemannHypothesis.AdelicFlow.ArchimedeanFlow
import RiemannHypothesis.AdelicFlow.ScalingPeriodicSector

noncomputable section

namespace RiemannHypothesis.AdelicFlow

/-!
# G3 global bridge: from the adele class space to the scaling-site quotient

The prime circles constructed in `ScalingPeriodicSector.lean` should not be
forced directly into the principal quotient `ℚˣ \ 𝔸_ℚ`.  The natural geometric
target is a further quotient by the maximal compact finite-idelic subgroup.

This file isolates that remaining construction as an explicit interface.  No
existence of the maximal-compact quotient is asserted here.
-/

/-- Boundary for the further quotient of the principal adele class space on
which the real scaling flow is to act.  The intended future implementation is
the maximal-compact/scaling-site quotient. -/
structure ScalingSiteQuotientBoundary where
  X : Type
  project : PrincipalQuotient → X
  flow : ℝ → X → X

  flow_zero : ∀ x, flow 0 x = x
  flow_add : ∀ s t x, flow (s + t) x = flow s (flow t x)

  /-- The further quotient must intertwine the actual archimedean flow already
  constructed on the principal quotient. -/
  project_intertwines : ∀ t x,
    project (principalArchimedeanFlow t x) = flow t (project x)

/-- Complete G3 bridge obligation.  Once constructed, the explicit prime
periodic sector must embed into the scaling-site quotient, with its flow, and it
must exhaust all positive-periodic points. -/
structure G3ScalingSiteBridge where
  site : ScalingSiteQuotientBoundary
  embedPeriodicSector : PrimePeriodicSector → site.X
  embed_injective : Function.Injective embedPeriodicSector

  intertwining : ∀ t x,
    embedPeriodicSector (primePeriodicSectorFlow t x) =
      site.flow t (embedPeriodicSector x)

  periodic_exhaustion : ∀ y : site.X,
    (∃ t : ℝ, 0 < t ∧ site.flow t y = y) →
      ∃ x : PrimePeriodicSector, embedPeriodicSector x = y

/-- A time is a period of the entire embedded `p`-circle in the scaling-site
model. -/
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

/-- Once the scaling-site bridge exists, the primitive period of the embedded
`p`-orbit is forced to remain exactly `log p`; no shorter return can be created
by the quotient because the prime-sector embedding is injective. -/
theorem G3ScalingSiteBridge.primePeriod_isPrimitive
    (G : G3ScalingSiteBridge) (p : PrimeLabel) :
    IsPrimitiveEmbeddedPrimePeriod G p (primeOrbitPeriod p) := by
  have hlocal := primeOrbitPeriod_isPrimitive p
  refine ⟨hlocal.1, ?_, ?_⟩
  · exact (G.embeddedPrimePeriod_iff p (primeOrbitPeriod p)).2 hlocal.2.1
  · intro s hs hperiod
    apply hlocal.2.2 s hs
    exact (G.embeddedPrimePeriod_iff p s).1 hperiod

/-- Under the bridge, every positive-periodic global point belongs to the image
of a uniquely embedded point whose component label is prime. -/
theorem G3ScalingSiteBridge.periodic_point_has_prime_representative
    (G : G3ScalingSiteBridge) (y : G.site.X)
    (hy : ∃ t : ℝ, 0 < t ∧ G.site.flow t y = y) :
    ∃ x : PrimePeriodicSector,
      G.embedPeriodicSector x = y ∧ Nat.Prime x.1.1 := by
  rcases G.periodic_exhaustion y hy with ⟨x, hx⟩
  exact ⟨x, hx, periodicSector_label_prime x⟩

/-- Therefore a completed G3 bridge simultaneously gives prime-only periodic
components and the exact primitive length `log p` on each such component. -/
theorem G3ScalingSiteBridge.G3_prime_orbit_package
    (G : G3ScalingSiteBridge) :
    (∀ p : PrimeLabel,
      IsPrimitiveEmbeddedPrimePeriod G p (primeOrbitPeriod p)) ∧
    (∀ y : G.site.X,
      (∃ t : ℝ, 0 < t ∧ G.site.flow t y = y) →
        ∃ x : PrimePeriodicSector,
          G.embedPeriodicSector x = y ∧ Nat.Prime x.1.1) := by
  constructor
  · intro p
    exact G.primePeriod_isPrimitive p
  · intro y hy
    exact G.periodic_point_has_prime_representative y hy

end RiemannHypothesis.AdelicFlow
