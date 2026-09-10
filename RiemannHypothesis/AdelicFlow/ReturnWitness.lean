import RiemannHypothesis.AdelicFlow.MaximalCompactQuotient

noncomputable section

namespace RiemannHypothesis.AdelicFlow

/-!
# Exact witnesses for returns of the scaling-site flow

A return of the twice-quotiented flow can be unfolded without any arithmetic
assumption.  Equality in the maximal-compact quotient produces a compact finite
unit, and equality in the principal quotient then produces one rational unit.
This is the algebraic entry point for the G3 stabilizer classification.
-/

/-- Canonical scaling-site class of a global adele representative. -/
def scalingSiteClass (a : GlobalSpace) : ScalingSiteQuotient :=
  toScalingSiteQuotient (toPrincipalQuotient a)

/-- Exact witness theorem for a return time.  A real time `t` fixes the
scaling-site class of `a` iff one can compensate the archimedean scaling first
by a maximal-compact finite unit and then by one principal rational unit. -/
theorem scalingSiteFlow_fixed_iff_witness (a : GlobalSpace) (t : ℝ) :
    scalingSiteFlow t (scalingSiteClass a) = scalingSiteClass a ↔
      ∃ k : MaxCompactFiniteUnit, ∃ u : ℚˣ,
        globalScale u
          (compactGlobalScale k (archimedeanGlobalFlow t a)) = a := by
  constructor
  · intro h
    change toScalingSiteQuotient
        (principalArchimedeanFlow t (toPrincipalQuotient a)) =
      toScalingSiteQuotient (toPrincipalQuotient a) at h
    have hkrel :
        MaxCompactEquivalent
          (principalArchimedeanFlow t (toPrincipalQuotient a))
          (toPrincipalQuotient a) :=
      Quotient.exact h
    rcases hkrel with ⟨k, hk⟩
    change toPrincipalQuotient
        (compactGlobalScale k (archimedeanGlobalFlow t a)) =
      toPrincipalQuotient a at hk
    have hurel :
        PrincipalEquivalent
          (compactGlobalScale k (archimedeanGlobalFlow t a)) a :=
      Quotient.exact hk
    rcases hurel with ⟨u, hu⟩
    exact ⟨k, u, hu⟩
  · rintro ⟨k, u, hu⟩
    change toScalingSiteQuotient
        (principalArchimedeanFlow t (toPrincipalQuotient a)) =
      toScalingSiteQuotient (toPrincipalQuotient a)
    apply Quotient.sound
    refine ⟨k, ?_⟩
    change toPrincipalQuotient
        (compactGlobalScale k (archimedeanGlobalFlow t a)) =
      toPrincipalQuotient a
    apply Quotient.sound
    exact ⟨u, hu⟩

/-- Finite zero support of a representative.  This is the arithmetic set whose
cardinality/rank will control the return-time lattice after the archimedean
nonzero stratum is imposed. -/
def finiteZeroSupport (a : GlobalSpace) : Set RationalFinitePlace :=
  {v | a.2 v = 0}

@[simp]
theorem mem_finiteZeroSupport_iff (a : GlobalSpace) (v : RationalFinitePlace) :
    v ∈ finiteZeroSupport a ↔ a.2 v = 0 := Iff.rfl

end RiemannHypothesis.AdelicFlow
