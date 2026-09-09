import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import RiemannHypothesis.AdelicFlow.PrincipalQuotient

noncomputable section

namespace RiemannHypothesis.AdelicFlow

/-!
# The external real scaling flow

The principal `ℚˣ` action becomes trivial after G2, so the nontrivial flow must
come from a larger scaling group.  Over `ℚ` there is a unique infinite place,
and its completion is canonically isomorphic to `ℝ`.  We use this to multiply
the infinite component by `exp t`, while leaving the finite adele component
fixed.

This constructs an actual real-parameter flow on the pre-quotient carrier and
proves that it commutes with principal rational scaling, hence descends to the
G2 quotient.
-/

/-- Every infinite place of `ℚ` is the unique real place. -/
def ratInfinitePlaceIsReal (v : NumberField.InfinitePlace ℚ) :
    NumberField.InfinitePlace.IsReal v := by
  rw [Subsingleton.elim v Rat.infinitePlace]
  exact Rat.isReal_infinitePlace

/-- Real coordinate on the completion at an infinite place of `ℚ`. -/
def ratRealCoordinate (v : NumberField.InfinitePlace ℚ) :
    v.Completion ≃+* ℝ :=
  NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
    (ratInfinitePlaceIsReal v)

/-- Multiplication by `e^t` in the real coordinate of one infinite completion. -/
def scaleAtInfinitePlace (t : ℝ) (v : NumberField.InfinitePlace ℚ)
    (x : v.Completion) : v.Completion :=
  (ratRealCoordinate v).symm (Real.exp t * ratRealCoordinate v x)

@[simp]
theorem scaleAtInfinitePlace_zero (v : NumberField.InfinitePlace ℚ)
    (x : v.Completion) :
    scaleAtInfinitePlace 0 v x = x := by
  apply (ratRealCoordinate v).injective
  simp [scaleAtInfinitePlace]

/-- Local real scalings satisfy the additive time law. -/
theorem scaleAtInfinitePlace_add (s t : ℝ) (v : NumberField.InfinitePlace ℚ)
    (x : v.Completion) :
    scaleAtInfinitePlace (s + t) v x =
      scaleAtInfinitePlace s v (scaleAtInfinitePlace t v x) := by
  apply (ratRealCoordinate v).injective
  simp [scaleAtInfinitePlace, Real.exp_add, mul_assoc]

/-- Real scaling on the full infinite-adele component. -/
def rationalInfiniteRealFlow (t : ℝ)
    (x : RationalInfiniteAdele) : RationalInfiniteAdele :=
  fun v => scaleAtInfinitePlace t v (x v)

@[simp]
theorem rationalInfiniteRealFlow_zero (x : RationalInfiniteAdele) :
    rationalInfiniteRealFlow 0 x = x := by
  funext v
  exact scaleAtInfinitePlace_zero v (x v)

/-- The infinite-adele real scaling is an additive `ℝ`-flow. -/
theorem rationalInfiniteRealFlow_add (s t : ℝ) (x : RationalInfiniteAdele) :
    rationalInfiniteRealFlow (s + t) x =
      rationalInfiniteRealFlow s (rationalInfiniteRealFlow t x) := by
  funext v
  exact scaleAtInfinitePlace_add s t v (x v)

/-- The real scaling commutes with multiplication by a principal rational unit
on the infinite-adele sector.  This uses only commutativity after moving to the
real coordinate. -/
theorem rationalInfiniteRealFlow_commutes_principal
    (t : ℝ) (u : ℚˣ) (x : RationalInfiniteAdele) :
    rationalInfiniteRealFlow t (infiniteScale u x) =
      infiniteScale u (rationalInfiniteRealFlow t x) := by
  funext v
  apply (ratRealCoordinate v).injective
  simp [rationalInfiniteRealFlow, scaleAtInfinitePlace, infiniteScale,
    mul_assoc, mul_left_comm, mul_comm]

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
