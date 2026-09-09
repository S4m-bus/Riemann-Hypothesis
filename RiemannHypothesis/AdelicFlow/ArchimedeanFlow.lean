import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import RiemannHypothesis.AdelicFlow.PrincipalQuotient

noncomputable section

namespace RiemannHypothesis.AdelicFlow

/-!
# The external real scaling flow

The principal `ℚˣ` action becomes trivial after G2, so the nontrivial flow must
come from a larger scaling group.  Over `ℚ` there is a unique infinite place,
and its completion is canonically isomorphic to `ℝ`.

We form an infinite adele whose value at every infinite place has real
coordinate `exp t`, and use multiplication by that adele as the real-parameter
scaling flow.  Because the infinite adele ring is commutative, this flow
commutes formally with principal rational scaling and therefore descends to the
G2 quotient.
-/

/-- Every infinite place of `ℚ` is the unique real place. -/
theorem ratInfinitePlaceIsReal (v : NumberField.InfinitePlace ℚ) :
    NumberField.InfinitePlace.IsReal v := by
  rw [Subsingleton.elim v Rat.infinitePlace]
  exact Rat.isReal_infinitePlace

/-- Real coordinate on the completion at an infinite place of `ℚ`. -/
def ratRealCoordinate (v : NumberField.InfinitePlace ℚ) :
    v.Completion ≃+* ℝ :=
  NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
    (ratInfinitePlaceIsReal v)

/-- The infinite adele with real coordinate `e^t` at each infinite place. -/
def infiniteExpAdele (t : ℝ) : RationalInfiniteAdele :=
  fun v => (ratRealCoordinate v).symm (Real.exp t)

@[simp]
theorem infiniteExpAdele_zero :
    infiniteExpAdele 0 = 1 := by
  funext v
  apply (ratRealCoordinate v).injective
  simp [infiniteExpAdele]

/-- Exponential adeles convert addition of times to multiplication. -/
theorem infiniteExpAdele_add (s t : ℝ) :
    infiniteExpAdele (s + t) = infiniteExpAdele s * infiniteExpAdele t := by
  funext v
  apply (ratRealCoordinate v).injective
  simp [infiniteExpAdele, Real.exp_add]

/-- Real scaling on the infinite-adele component. -/
def rationalInfiniteRealFlow (t : ℝ)
    (x : RationalInfiniteAdele) : RationalInfiniteAdele :=
  infiniteExpAdele t * x

@[simp]
theorem rationalInfiniteRealFlow_zero (x : RationalInfiniteAdele) :
    rationalInfiniteRealFlow 0 x = x := by
  simp [rationalInfiniteRealFlow]

/-- The infinite-adele real scaling is an additive `ℝ`-flow. -/
theorem rationalInfiniteRealFlow_add (s t : ℝ) (x : RationalInfiniteAdele) :
    rationalInfiniteRealFlow (s + t) x =
      rationalInfiniteRealFlow s (rationalInfiniteRealFlow t x) := by
  rw [rationalInfiniteRealFlow, infiniteExpAdele_add]
  simp only [rationalInfiniteRealFlow]
  exact mul_assoc _ _ _

/-- The real scaling commutes with multiplication by every principal rational
unit on the infinite-adele sector. -/
theorem rationalInfiniteRealFlow_commutes_principal
    (t : ℝ) (u : ℚˣ) (x : RationalInfiniteAdele) :
    rationalInfiniteRealFlow t (infiniteScale u x) =
      infiniteScale u (rationalInfiniteRealFlow t x) := by
  simp only [rationalInfiniteRealFlow, infiniteScale]
  ac_rfl

/-- The external real flow on the exposed rational adele product: scale only the
infinite component. -/
def archimedeanGlobalFlow (t : ℝ) (a : GlobalSpace) : GlobalSpace :=
  (rationalInfiniteRealFlow t a.1, a.2)

@[simp]
theorem archimedeanGlobalFlow_zero (a : GlobalSpace) :
    archimedeanGlobalFlow 0 a = a := by
  apply Prod.ext
  · simp [archimedeanGlobalFlow]
  · rfl

/-- The external scaling satisfies the global additive time law. -/
theorem archimedeanGlobalFlow_add (s t : ℝ) (a : GlobalSpace) :
    archimedeanGlobalFlow (s + t) a =
      archimedeanGlobalFlow s (archimedeanGlobalFlow t a) := by
  apply Prod.ext
  · exact rationalInfiniteRealFlow_add s t a.1
  · rfl

/-- The external real flow commutes with every principal rational scaling. -/
theorem archimedeanGlobalFlow_commutes_principal (t : ℝ) :
    CommutesWithPrincipalScaling (archimedeanGlobalFlow t) := by
  intro u a
  apply Prod.ext
  · exact rationalInfiniteRealFlow_commutes_principal t u a.1
  · rfl

/-- Hence the real scaling gives an actual instance of the G2 quotient-flow
boundary, not merely an axiomatized placeholder. -/
def archimedeanQuotientFlowBoundary : QuotientFlowBoundary where
  flow := archimedeanGlobalFlow
  zero := archimedeanGlobalFlow_zero
  add := archimedeanGlobalFlow_add
  principal_commutation := archimedeanGlobalFlow_commutes_principal

/-- The descended real-parameter flow on the principal adele quotient. -/
def principalArchimedeanFlow (t : ℝ) :
    PrincipalQuotient → PrincipalQuotient :=
  archimedeanQuotientFlowBoundary.quotientFlow t

@[simp]
theorem principalArchimedeanFlow_zero (x : PrincipalQuotient) :
    principalArchimedeanFlow 0 x = x :=
  archimedeanQuotientFlowBoundary.quotientFlow_zero x

/-- The descended real scaling is itself an additive flow. -/
theorem principalArchimedeanFlow_add (s t : ℝ) (x : PrincipalQuotient) :
    principalArchimedeanFlow (s + t) x =
      principalArchimedeanFlow s (principalArchimedeanFlow t x) :=
  archimedeanQuotientFlowBoundary.quotientFlow_add s t x

end RiemannHypothesis.AdelicFlow
