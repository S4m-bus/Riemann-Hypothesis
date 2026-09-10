import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import RiemannHypothesis.AdelicFlow.ArchimedeanFlow

noncomputable section

namespace RiemannHypothesis.AdelicFlow

/-!
# The maximal compact finite-unit quotient

For `ℚ`, the finite maximal compact idelic group is the product of the local
integer-unit groups

    K_f = ∏_v (O_v)ˣ,

canonically corresponding to `Ẑˣ = ∏_p ℤ_pˣ`.

We construct this group directly from mathlib's finite places, embed it into the
finite adele ring, let it act on the principal quotient from G2, and take the
second orbit quotient.  The archimedean real flow acts only at infinity, so it
commutes with this finite compact action and descends once more.

This gives an actual set-level version of the scaling-site quotient.  Topological
compactness and the complete closed-orbit exhaustion theorem are separate later
obligations.
-/

abbrev RationalFinitePlace := IsDedekindDomain.HeightOneSpectrum ℤ

/-- Algebraic maximal compact finite ideles `∏_v (O_v)ˣ`. -/
abbrev MaxCompactFiniteUnit : Type :=
  (v : RationalFinitePlace) → (v.adicCompletionIntegers ℚ)ˣ

/-- Regard a maximal-compact element as a finite adele. -/
def maxCompactAdele (k : MaxCompactFiniteUnit) : RationalFiniteAdele := by
  refine ⟨fun v => ((k v : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ), ?_⟩
  exact Filter.Eventually.of_forall fun v => (k v : v.adicCompletionIntegers ℚ).property

@[simp]
theorem maxCompactAdele_one :
    maxCompactAdele (1 : MaxCompactFiniteUnit) = 1 := by
  apply IsDedekindDomain.FiniteAdeleRing.ext
  intro v
  change (1 : v.adicCompletion ℚ) = (1 : v.adicCompletion ℚ)
  rfl

/-- The maximal-compact embedding is multiplicative. -/
theorem maxCompactAdele_mul (k l : MaxCompactFiniteUnit) :
    maxCompactAdele (k * l) = maxCompactAdele k * maxCompactAdele l := by
  apply IsDedekindDomain.FiniteAdeleRing.ext
  intro v
  rw [RestrictedProduct.mul_apply]
  rfl

/-- Inverses in the local unit product cancel on the finite adele image. -/
theorem maxCompactAdele_inv_mul (k : MaxCompactFiniteUnit) :
    maxCompactAdele k⁻¹ * maxCompactAdele k = 1 := by
  rw [← maxCompactAdele_mul]
  simp

/-- Maximal-compact action on the global adele carrier. -/
def compactGlobalScale (k : MaxCompactFiniteUnit) (a : GlobalSpace) : GlobalSpace :=
  (a.1, maxCompactAdele k * a.2)

@[simp]
theorem compactGlobalScale_one (a : GlobalSpace) :
    compactGlobalScale (1 : MaxCompactFiniteUnit) a = a := by
  apply Prod.ext
  · rfl
  · simp [compactGlobalScale]

theorem compactGlobalScale_mul (k l : MaxCompactFiniteUnit) (a : GlobalSpace) :
    compactGlobalScale (k * l) a =
      compactGlobalScale k (compactGlobalScale l a) := by
  apply Prod.ext
  · rfl
  · simp [compactGlobalScale, maxCompactAdele_mul, mul_assoc]

theorem compactGlobalScale_inv_cancel (k : MaxCompactFiniteUnit) (a : GlobalSpace) :
    compactGlobalScale k⁻¹ (compactGlobalScale k a) = a := by
  rw [← compactGlobalScale_mul]
  simp

/-- Finite compact scaling commutes with principal rational scaling. -/
theorem compactGlobalScale_commutes_principal (k : MaxCompactFiniteUnit) :
    CommutesWithPrincipalScaling (compactGlobalScale k) := by
  intro u a
  apply Prod.ext
  · rfl
  · simp only [compactGlobalScale, globalScale, finiteScale]
    ac_rfl

/-- Descended compact finite scaling on the principal quotient. -/
def principalCompactScale (k : MaxCompactFiniteUnit) :
    PrincipalQuotient → PrincipalQuotient :=
  descendCommutingMap (compactGlobalScale k)
    (compactGlobalScale_commutes_principal k)

@[simp]
theorem principalCompactScale_mk (k : MaxCompactFiniteUnit) (a : GlobalSpace) :
    principalCompactScale k (toPrincipalQuotient a) =
      toPrincipalQuotient (compactGlobalScale k a) := rfl

@[simp]
theorem principalCompactScale_one (x : PrincipalQuotient) :
    principalCompactScale (1 : MaxCompactFiniteUnit) x = x := by
  refine Quotient.inductionOn x ?_
  intro a
  change toPrincipalQuotient (compactGlobalScale 1 a) = toPrincipalQuotient a
  rw [compactGlobalScale_one]

theorem principalCompactScale_mul (k l : MaxCompactFiniteUnit)
    (x : PrincipalQuotient) :
    principalCompactScale (k * l) x =
      principalCompactScale k (principalCompactScale l x) := by
  refine Quotient.inductionOn x ?_
  intro a
  change toPrincipalQuotient (compactGlobalScale (k * l) a) =
    toPrincipalQuotient (compactGlobalScale k (compactGlobalScale l a))
  rw [compactGlobalScale_mul]

/-- Orbit equivalence for the maximal compact finite-unit action. -/
def MaxCompactEquivalent (x y : PrincipalQuotient) : Prop :=
  ∃ k : MaxCompactFiniteUnit, principalCompactScale k x = y

theorem maxCompactEquivalent_refl (x : PrincipalQuotient) :
    MaxCompactEquivalent x x := by
  exact ⟨1, principalCompactScale_one x⟩

theorem maxCompactEquivalent_symm {x y : PrincipalQuotient}
    (h : MaxCompactEquivalent x y) : MaxCompactEquivalent y x := by
  rcases h with ⟨k, rfl⟩
  refine ⟨k⁻¹, ?_⟩
  rw [← principalCompactScale_mul]
  simp

theorem maxCompactEquivalent_trans {x y z : PrincipalQuotient}
    (hxy : MaxCompactEquivalent x y) (hyz : MaxCompactEquivalent y z) :
    MaxCompactEquivalent x z := by
  rcases hxy with ⟨k, hk⟩
  rcases hyz with ⟨l, hl⟩
  refine ⟨l * k, ?_⟩
  rw [principalCompactScale_mul, hk, hl]

def maxCompactSetoid : Setoid PrincipalQuotient where
  r := MaxCompactEquivalent
  iseqv := ⟨maxCompactEquivalent_refl, maxCompactEquivalent_symm,
    maxCompactEquivalent_trans⟩

/-- The set-level quotient `(ℚˣ \ 𝔸_ℚ) / K_f`. -/
abbrev ScalingSiteQuotient : Type := Quotient maxCompactSetoid

def toScalingSiteQuotient (x : PrincipalQuotient) : ScalingSiteQuotient :=
  Quotient.mk maxCompactSetoid x

/-- Compact finite scaling is killed by the second quotient. -/
theorem compact_scale_trivial_on_scalingSite
    (k : MaxCompactFiniteUnit) (x : PrincipalQuotient) :
    toScalingSiteQuotient (principalCompactScale k x) =
      toScalingSiteQuotient x := by
  apply Quotient.sound
  exact ⟨k⁻¹, by
    rw [← principalCompactScale_mul]
    simp⟩

/-! ## Descent of the actual archimedean flow -/

theorem archimedeanGlobalFlow_commutes_compact
    (t : ℝ) (k : MaxCompactFiniteUnit) (a : GlobalSpace) :
    archimedeanGlobalFlow t (compactGlobalScale k a) =
      compactGlobalScale k (archimedeanGlobalFlow t a) := rfl

theorem principalArchimedeanFlow_commutes_compact
    (t : ℝ) (k : MaxCompactFiniteUnit) (x : PrincipalQuotient) :
    principalArchimedeanFlow t (principalCompactScale k x) =
      principalCompactScale k (principalArchimedeanFlow t x) := by
  refine Quotient.inductionOn x ?_
  intro a
  change toPrincipalQuotient
      (archimedeanGlobalFlow t (compactGlobalScale k a)) =
    toPrincipalQuotient
      (compactGlobalScale k (archimedeanGlobalFlow t a))
  rw [archimedeanGlobalFlow_commutes_compact]

theorem principalArchimedeanFlow_respects_maxCompact (t : ℝ) :
    ∀ ⦃x y : PrincipalQuotient⦄,
      MaxCompactEquivalent x y →
        MaxCompactEquivalent (principalArchimedeanFlow t x)
          (principalArchimedeanFlow t y) := by
  intro x y hxy
  rcases hxy with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [← principalArchimedeanFlow_commutes_compact t k x, hk]

/-- Actual real scaling flow on the maximal-compact quotient. -/
def scalingSiteFlow (t : ℝ) : ScalingSiteQuotient → ScalingSiteQuotient :=
  Quotient.lift
    (fun x => toScalingSiteQuotient (principalArchimedeanFlow t x))
    (by
      intro x y hxy
      exact Quotient.sound
        (principalArchimedeanFlow_respects_maxCompact t hxy))

@[simp]
theorem scalingSiteFlow_mk (t : ℝ) (x : PrincipalQuotient) :
    scalingSiteFlow t (toScalingSiteQuotient x) =
      toScalingSiteQuotient (principalArchimedeanFlow t x) := rfl

@[simp]
theorem scalingSiteFlow_zero (x : ScalingSiteQuotient) :
    scalingSiteFlow 0 x = x := by
  refine Quotient.inductionOn x ?_
  intro y
  change toScalingSiteQuotient (principalArchimedeanFlow 0 y) =
    toScalingSiteQuotient y
  rw [principalArchimedeanFlow_zero]

theorem scalingSiteFlow_add (s t : ℝ) (x : ScalingSiteQuotient) :
    scalingSiteFlow (s + t) x = scalingSiteFlow s (scalingSiteFlow t x) := by
  refine Quotient.inductionOn x ?_
  intro y
  change toScalingSiteQuotient (principalArchimedeanFlow (s + t) y) =
    toScalingSiteQuotient
      (principalArchimedeanFlow s (principalArchimedeanFlow t y))
  rw [principalArchimedeanFlow_add]

/-- Summary of the actual second quotient construction. -/
theorem maximalCompactQuotient_constructed :
    (∀ k : MaxCompactFiniteUnit, ∀ x : PrincipalQuotient,
      toScalingSiteQuotient (principalCompactScale k x) =
        toScalingSiteQuotient x) ∧
    (∀ s t : ℝ, ∀ x : ScalingSiteQuotient,
      scalingSiteFlow (s + t) x = scalingSiteFlow s (scalingSiteFlow t x)) := by
  exact ⟨compact_scale_trivial_on_scalingSite, scalingSiteFlow_add⟩

end RiemannHypothesis.AdelicFlow
