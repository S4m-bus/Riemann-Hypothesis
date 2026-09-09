import Mathlib.NumberTheory.NumberField.AdeleRing
import RiemannHypothesis.AdelicFlow.LocalBoundaries

noncomputable section

namespace RiemannHypothesis.AdelicFlow

/-!
# G1: the global arithmetic carrier and local-to-global embeddings

This file constructs an actual adelic carrier over `ℚ` using mathlib's adeles.
It deliberately stops before quotienting by principal rational scalings.  That
quotient is the next boundary (G2).

The global carrier is

    `NumberField.AdeleRing ℤ ℚ`

which is definitionally the product of the infinite adele ring and the finite
restricted adele ring.  We prove that both sectors embed injectively and that
the canonical arithmetic scaling action of `ℚˣ` intertwines with both local
sectors.
-/

/-- The archimedean sector of the rational adeles. -/
abbrev RationalInfiniteAdele : Type := NumberField.InfiniteAdeleRing ℚ

/-- The finite restricted-product sector of the rational adeles. -/
abbrev RationalFiniteAdele : Type := IsDedekindDomain.FiniteAdeleRing ℤ ℚ

/-- The actual adele ring of `ℚ`, using `ℤ` as its Dedekind domain. -/
abbrev RationalAdele : Type := NumberField.AdeleRing ℤ ℚ

/-- Our pre-quotient global arithmetic space.  It is an actual mathlib adele ring,
not an axiomatized placeholder. -/
abbrev GlobalSpace : Type := RationalAdele

/-- Embed the complete archimedean sector into the global adele space. -/
def embedInfinite : RationalInfiniteAdele →+ GlobalSpace where
  toFun x := (x, 0)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Embed the finite restricted-product sector into the global adele space. -/
def embedFinite : RationalFiniteAdele →+ GlobalSpace where
  toFun x := (0, x)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Projection from the global adele space to the archimedean sector. -/
def projectInfinite : GlobalSpace →+ RationalInfiniteAdele where
  toFun x := x.1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Projection from the global adele space to the finite restricted-product sector. -/
def projectFinite : GlobalSpace →+ RationalFiniteAdele where
  toFun x := x.2
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem projectInfinite_embedInfinite (x : RationalInfiniteAdele) :
    projectInfinite (embedInfinite x) = x := rfl

@[simp]
theorem projectFinite_embedFinite (x : RationalFiniteAdele) :
    projectFinite (embedFinite x) = x := rfl

@[simp]
theorem projectFinite_embedInfinite (x : RationalInfiniteAdele) :
    projectFinite (embedInfinite x) = 0 := rfl

@[simp]
theorem projectInfinite_embedFinite (x : RationalFiniteAdele) :
    projectInfinite (embedFinite x) = 0 := rfl

/-- G1a: the archimedean sector is genuinely embedded in the global carrier. -/
theorem embedInfinite_injective : Function.Injective embedInfinite := by
  intro x y h
  exact congrArg (fun z : GlobalSpace => z.1) h

/-- G1a: the finite restricted-product sector is genuinely embedded in the global carrier. -/
theorem embedFinite_injective : Function.Injective embedFinite := by
  intro x y h
  exact congrArg (fun z : GlobalSpace => z.2) h

/-- Every global adele splits into its archimedean and finite embedded pieces. -/
theorem global_decomposition (a : GlobalSpace) :
    embedInfinite a.1 + embedFinite a.2 = a := by
  rcases a with ⟨a∞, af⟩
  simp [embedInfinite, embedFinite]

/-! ## Arithmetic scaling

Before constructing a continuous logarithmic flow, there is already a canonical
arithmetic scaling action: multiplication by a nonzero rational number.  We write
it componentwise so compatibility with the product definition of the adele ring
is transparent to Lean.
-/

/-- Rational scaling on the archimedean sector. -/
def infiniteScale (u : ℚˣ) (x : RationalInfiniteAdele) : RationalInfiniteAdele :=
  (algebraMap ℚ RationalInfiniteAdele (u : ℚ)) * x

/-- Rational scaling on the finite restricted-product sector. -/
def finiteScale (u : ℚˣ) (x : RationalFiniteAdele) : RationalFiniteAdele :=
  (algebraMap ℚ RationalFiniteAdele (u : ℚ)) * x

/-- Rational scaling on the full adele space, component by component. -/
def globalScale (u : ℚˣ) (a : GlobalSpace) : GlobalSpace :=
  (infiniteScale u a.1, finiteScale u a.2)

@[simp]
theorem infiniteScale_one (x : RationalInfiniteAdele) :
    infiniteScale (1 : ℚˣ) x = x := by
  simp [infiniteScale]

@[simp]
theorem finiteScale_one (x : RationalFiniteAdele) :
    finiteScale (1 : ℚˣ) x = x := by
  simp [finiteScale]

@[simp]
theorem globalScale_one (a : GlobalSpace) :
    globalScale (1 : ℚˣ) a = a := by
  rcases a with ⟨a∞, af⟩
  simp [globalScale]

/-- Rational scalings compose according to multiplication in `ℚˣ`. -/
theorem infiniteScale_mul (u v : ℚˣ) (x : RationalInfiniteAdele) :
    infiniteScale (u * v) x = infiniteScale u (infiniteScale v x) := by
  simp [infiniteScale, mul_assoc]

/-- Rational scalings compose according to multiplication in `ℚˣ`. -/
theorem finiteScale_mul (u v : ℚˣ) (x : RationalFiniteAdele) :
    finiteScale (u * v) x = finiteScale u (finiteScale v x) := by
  simp [finiteScale, mul_assoc]

/-- The componentwise global scaling is a genuine multiplicative action law. -/
theorem globalScale_mul (u v : ℚˣ) (a : GlobalSpace) :
    globalScale (u * v) a = globalScale u (globalScale v a) := by
  rcases a with ⟨a∞, af⟩
  simp [globalScale, infiniteScale_mul, finiteScale_mul]

/-- G1b: the archimedean embedding intertwines local rational scaling with the
same global arithmetic scaling. -/
theorem embedInfinite_intertwines_scale (u : ℚˣ) (x : RationalInfiniteAdele) :
    embedInfinite (infiniteScale u x) = globalScale u (embedInfinite x) := by
  simp [embedInfinite, globalScale, finiteScale]

/-- G1b: the finite restricted-product embedding intertwines local rational
scaling with the same global arithmetic scaling. -/
theorem embedFinite_intertwines_scale (u : ℚˣ) (x : RationalFiniteAdele) :
    embedFinite (finiteScale u x) = globalScale u (embedFinite x) := by
  simp [embedFinite, globalScale, infiniteScale]

/-- The exact G1 carrier result: both local sectors embed injectively, reconstruct
every global adele additively, and are compatible with principal rational scaling.
This is intentionally weaker than existence of the desired continuous Hilbert--Pólya
flow; no such flow is asserted here. -/
theorem G1_local_to_global_embedding :
    Function.Injective embedInfinite ∧
    Function.Injective embedFinite ∧
    (∀ a : GlobalSpace, embedInfinite a.1 + embedFinite a.2 = a) ∧
    (∀ u : ℚˣ, ∀ x : RationalInfiniteAdele,
      embedInfinite (infiniteScale u x) = globalScale u (embedInfinite x)) ∧
    (∀ u : ℚˣ, ∀ x : RationalFiniteAdele,
      embedFinite (finiteScale u x) = globalScale u (embedFinite x)) := by
  refine ⟨embedInfinite_injective, embedFinite_injective, ?_, ?_, ?_⟩
  · exact global_decomposition
  · exact embedInfinite_intertwines_scale
  · exact embedFinite_intertwines_scale

/-- Boundary for the next stage.  The eventual continuous logarithmic flow must
restrict to local flows through the proven embeddings.  This structure records
that dynamical obligation without assuming that such a flow exists. -/
structure G1ContinuousFlowBoundary where
  globalFlow : ℝ → GlobalSpace → GlobalSpace
  infiniteFlow : ℝ → RationalInfiniteAdele → RationalInfiniteAdele
  finiteFlow : ℝ → RationalFiniteAdele → RationalFiniteAdele

  global_zero : ∀ a, globalFlow 0 a = a
  infinite_zero : ∀ x, infiniteFlow 0 x = x
  finite_zero : ∀ x, finiteFlow 0 x = x

  global_add : ∀ s t a, globalFlow (s + t) a = globalFlow s (globalFlow t a)
  infinite_add : ∀ s t x, infiniteFlow (s + t) x = infiniteFlow s (infiniteFlow t x)
  finite_add : ∀ s t x, finiteFlow (s + t) x = finiteFlow s (finiteFlow t x)

  infinite_intertwining : ∀ t x,
    embedInfinite (infiniteFlow t x) = globalFlow t (embedInfinite x)
  finite_intertwining : ∀ t x,
    embedFinite (finiteFlow t x) = globalFlow t (embedFinite x)

end RiemannHypothesis.AdelicFlow
