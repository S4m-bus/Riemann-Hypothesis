import RiemannHypothesis.AdelicFlow.G4CorrectedReturn
import RiemannHypothesis.AdelicFlow.MaximalCompactQuotient

noncomputable section

namespace RiemannHypothesis.AdelicFlow

/-!
# G4: quotient-level finite transversal

The pre-quotient finite adele carrier still contains local unit directions.
For the actual arithmetic transverse geometry these are gauge directions:
we quotient the finite adele carrier by multiplication by

    K_f = ∏_v O_v^×.

The stable and positive prime return maps commute with this compact action, so
they descend to mutually inverse maps of the quotient.  This removes the
off-diagonal unit changes from the transverse state space while retaining the
non-unit p-adic contraction/expansion.
-/

/-- Compact finite scaling directly on the finite adele transversal. -/
def compactFiniteScale
    (k : MaxCompactFiniteUnit) (y : PrequotientTransverseCarrier) :
    PrequotientTransverseCarrier :=
  maxCompactAdele k * y

@[simp]
theorem compactFiniteScale_one (y : PrequotientTransverseCarrier) :
    compactFiniteScale (1 : MaxCompactFiniteUnit) y = y := by
  simp [compactFiniteScale]

/-- Compact scalings compose multiplicatively. -/
theorem compactFiniteScale_mul
    (k l : MaxCompactFiniteUnit) (y : PrequotientTransverseCarrier) :
    compactFiniteScale (k * l) y =
      compactFiniteScale k (compactFiniteScale l y) := by
  simp only [compactFiniteScale, maxCompactAdele_mul]
  ac_rfl

/-- Orbit equivalence on the finite transversal under maximal compact units. -/
def FiniteCompactEquivalent
    (x y : PrequotientTransverseCarrier) : Prop :=
  ∃ k : MaxCompactFiniteUnit, compactFiniteScale k x = y

theorem finiteCompactEquivalent_refl
    (x : PrequotientTransverseCarrier) : FiniteCompactEquivalent x x := by
  exact ⟨1, compactFiniteScale_one x⟩

theorem finiteCompactEquivalent_symm
    {x y : PrequotientTransverseCarrier}
    (h : FiniteCompactEquivalent x y) : FiniteCompactEquivalent y x := by
  rcases h with ⟨k, rfl⟩
  refine ⟨k⁻¹, ?_⟩
  rw [← compactFiniteScale_mul]
  simp

theorem finiteCompactEquivalent_trans
    {x y z : PrequotientTransverseCarrier}
    (hxy : FiniteCompactEquivalent x y)
    (hyz : FiniteCompactEquivalent y z) : FiniteCompactEquivalent x z := by
  rcases hxy with ⟨k, hk⟩
  rcases hyz with ⟨l, hl⟩
  refine ⟨l * k, ?_⟩
  rw [compactFiniteScale_mul, hk, hl]

def finiteCompactSetoid : Setoid PrequotientTransverseCarrier where
  r := FiniteCompactEquivalent
  iseqv := ⟨finiteCompactEquivalent_refl, finiteCompactEquivalent_symm,
    finiteCompactEquivalent_trans⟩

/-- Finite arithmetic transverse quotient `A_f / K_f`. -/
abbrev FiniteTransverseQuotient : Type := Quotient finiteCompactSetoid

/-- Canonical projection to the finite arithmetic transverse quotient. -/
def toFiniteTransverseQuotient
    (y : PrequotientTransverseCarrier) : FiniteTransverseQuotient :=
  Quotient.mk finiteCompactSetoid y

/-- Compact finite-unit scaling is trivial in the transverse quotient. -/
theorem compactFiniteScale_trivial_on_quotient
    (k : MaxCompactFiniteUnit) (y : PrequotientTransverseCarrier) :
    toFiniteTransverseQuotient (compactFiniteScale k y) =
      toFiniteTransverseQuotient y := by
  apply Quotient.sound
  refine ⟨k⁻¹, ?_⟩
  rw [← compactFiniteScale_mul]
  simp

/-- Stable prime return commutes with every compact finite scaling. -/
theorem stableTransverseReturn_commutes_compact
    (p m : ℕ) (hp : Nat.Prime p)
    (k : MaxCompactFiniteUnit) (y : PrequotientTransverseCarrier) :
    stableTransverseReturn p m hp (compactFiniteScale k y) =
      compactFiniteScale k (stableTransverseReturn p m hp y) := by
  simp only [stableTransverseReturn, compactFiniteScale, finiteScale]
  ac_rfl

/-- Positive/inverse prime return also commutes with compact finite scaling. -/
theorem positiveTransverseReturn_commutes_compact
    (p m : ℕ) (hp : Nat.Prime p)
    (k : MaxCompactFiniteUnit) (y : PrequotientTransverseCarrier) :
    positiveTransverseReturn p m hp (compactFiniteScale k y) =
      compactFiniteScale k (positiveTransverseReturn p m hp y) := by
  simp only [positiveTransverseReturn, compactFiniteScale, finiteScale]
  ac_rfl

/-- Stable return respects finite compact orbit-equivalence. -/
theorem stableTransverseReturn_respects_compact
    (p m : ℕ) (hp : Nat.Prime p)
    {x y : PrequotientTransverseCarrier}
    (hxy : FiniteCompactEquivalent x y) :
    FiniteCompactEquivalent
      (stableTransverseReturn p m hp x)
      (stableTransverseReturn p m hp y) := by
  rcases hxy with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [← stableTransverseReturn_commutes_compact p m hp k x, hk]

/-- Positive return respects finite compact orbit-equivalence. -/
theorem positiveTransverseReturn_respects_compact
    (p m : ℕ) (hp : Nat.Prime p)
    {x y : PrequotientTransverseCarrier}
    (hxy : FiniteCompactEquivalent x y) :
    FiniteCompactEquivalent
      (positiveTransverseReturn p m hp x)
      (positiveTransverseReturn p m hp y) := by
  rcases hxy with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [← positiveTransverseReturn_commutes_compact p m hp k x, hk]

/-- Stable prime return descended to the finite arithmetic transverse quotient. -/
def stableTransverseQuotientReturn
    (p m : ℕ) (hp : Nat.Prime p) :
    FiniteTransverseQuotient → FiniteTransverseQuotient :=
  Quotient.lift
    (fun y => toFiniteTransverseQuotient (stableTransverseReturn p m hp y))
    (by
      intro x y hxy
      exact Quotient.sound (stableTransverseReturn_respects_compact p m hp hxy))

/-- Positive prime return descended to the finite arithmetic transverse quotient. -/
def positiveTransverseQuotientReturn
    (p m : ℕ) (hp : Nat.Prime p) :
    FiniteTransverseQuotient → FiniteTransverseQuotient :=
  Quotient.lift
    (fun y => toFiniteTransverseQuotient (positiveTransverseReturn p m hp y))
    (by
      intro x y hxy
      exact Quotient.sound (positiveTransverseReturn_respects_compact p m hp hxy))

@[simp]
theorem stableTransverseQuotientReturn_mk
    (p m : ℕ) (hp : Nat.Prime p) (y : PrequotientTransverseCarrier) :
    stableTransverseQuotientReturn p m hp (toFiniteTransverseQuotient y) =
      toFiniteTransverseQuotient (stableTransverseReturn p m hp y) := rfl

@[simp]
theorem positiveTransverseQuotientReturn_mk
    (p m : ℕ) (hp : Nat.Prime p) (y : PrequotientTransverseCarrier) :
    positiveTransverseQuotientReturn p m hp (toFiniteTransverseQuotient y) =
      toFiniteTransverseQuotient (positiveTransverseReturn p m hp y) := rfl

/-- The descended positive and stable returns are mutually inverse. -/
theorem positive_after_stable_transverse_quotient
    (p m : ℕ) (hp : Nat.Prime p) (x : FiniteTransverseQuotient) :
    positiveTransverseQuotientReturn p m hp
      (stableTransverseQuotientReturn p m hp x) = x := by
  refine Quotient.inductionOn x ?_
  intro y
  change toFiniteTransverseQuotient
      (positiveTransverseReturn p m hp (stableTransverseReturn p m hp y)) =
    toFiniteTransverseQuotient y
  rw [positive_after_stable_return]

/-- The other composition also gives the identity. -/
theorem stable_after_positive_transverse_quotient
    (p m : ℕ) (hp : Nat.Prime p) (x : FiniteTransverseQuotient) :
    stableTransverseQuotientReturn p m hp
      (positiveTransverseQuotientReturn p m hp x) = x := by
  refine Quotient.inductionOn x ?_
  intro y
  change toFiniteTransverseQuotient
      (stableTransverseReturn p m hp (positiveTransverseReturn p m hp y)) =
    toFiniteTransverseQuotient y
  rw [stable_after_positive_return]

end RiemannHypothesis.AdelicFlow
