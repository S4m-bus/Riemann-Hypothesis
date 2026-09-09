import Mathlib.NumberTheory.NumberField.AdeleRing
import RiemannHypothesis.AdelicFlow.LocalBoundaries

noncomputable section

namespace RiemannHypothesis.AdelicFlow

/-!
# G1: the global arithmetic carrier and local-to-global embeddings

Mathlib defines `NumberField.AdeleRing ℤ ℚ` as the product of the infinite
adele ring and the finite restricted adele ring.  For the G1 proofs we expose
that product directly, avoiding reducibility issues while retaining the same
mathematical carrier.
-/

abbrev RationalInfiniteAdele : Type := NumberField.InfiniteAdeleRing ℚ
abbrev RationalFiniteAdele : Type := IsDedekindDomain.FiniteAdeleRing ℤ ℚ
abbrev RationalAdele : Type := NumberField.AdeleRing ℤ ℚ
abbrev GlobalSpace : Type := RationalInfiniteAdele × RationalFiniteAdele

def embedInfinite (x : RationalInfiniteAdele) : GlobalSpace := (x, 0)
def embedFinite (x : RationalFiniteAdele) : GlobalSpace := (0, x)
def projectInfinite (x : GlobalSpace) : RationalInfiniteAdele := x.1
def projectFinite (x : GlobalSpace) : RationalFiniteAdele := x.2

@[simp] theorem projectInfinite_embedInfinite (x : RationalInfiniteAdele) :
    projectInfinite (embedInfinite x) = x := rfl
@[simp] theorem projectFinite_embedFinite (x : RationalFiniteAdele) :
    projectFinite (embedFinite x) = x := rfl
@[simp] theorem projectFinite_embedInfinite (x : RationalInfiniteAdele) :
    projectFinite (embedInfinite x) = 0 := rfl
@[simp] theorem projectInfinite_embedFinite (x : RationalFiniteAdele) :
    projectInfinite (embedFinite x) = 0 := rfl

theorem embedInfinite_injective : Function.Injective embedInfinite := by
  intro x y h
  simpa [embedInfinite] using congrArg (fun z : GlobalSpace => z.1) h

theorem embedFinite_injective : Function.Injective embedFinite := by
  intro x y h
  simpa [embedFinite] using congrArg (fun z : GlobalSpace => z.2) h

theorem global_decomposition (a : GlobalSpace) :
    embedInfinite a.1 + embedFinite a.2 = a := by
  rcases a with ⟨ainf, afin⟩
  simp [embedInfinite, embedFinite]

/-! ## Principal rational scaling -/

def infiniteScale (u : ℚˣ) (x : RationalInfiniteAdele) : RationalInfiniteAdele :=
  (algebraMap ℚ RationalInfiniteAdele (u : ℚ)) * x

def finiteScale (u : ℚˣ) (x : RationalFiniteAdele) : RationalFiniteAdele :=
  (algebraMap ℚ RationalFiniteAdele (u : ℚ)) * x

def globalScale (u : ℚˣ) (a : GlobalSpace) : GlobalSpace :=
  (infiniteScale u a.1, finiteScale u a.2)

@[simp] theorem infiniteScale_one (x : RationalInfiniteAdele) :
    infiniteScale (1 : ℚˣ) x = x := by
  simp [infiniteScale]

@[simp] theorem finiteScale_one (x : RationalFiniteAdele) :
    finiteScale (1 : ℚˣ) x = x := by
  simp [finiteScale]

@[simp] theorem globalScale_one (a : GlobalSpace) :
    globalScale (1 : ℚˣ) a = a := by
  apply Prod.ext
  · simp [globalScale]
  · simp [globalScale]

theorem infiniteScale_mul (u v : ℚˣ) (x : RationalInfiniteAdele) :
    infiniteScale (u * v) x = infiniteScale u (infiniteScale v x) := by
  simp [infiniteScale, mul_assoc]

theorem finiteScale_mul (u v : ℚˣ) (x : RationalFiniteAdele) :
    finiteScale (u * v) x = finiteScale u (finiteScale v x) := by
  simp [finiteScale, mul_assoc]

theorem globalScale_mul (u v : ℚˣ) (a : GlobalSpace) :
    globalScale (u * v) a = globalScale u (globalScale v a) := by
  apply Prod.ext
  · exact infiniteScale_mul u v a.1
  · exact finiteScale_mul u v a.2

theorem embedInfinite_intertwines_scale (u : ℚˣ) (x : RationalInfiniteAdele) :
    embedInfinite (infiniteScale u x) = globalScale u (embedInfinite x) := by
  apply Prod.ext
  · rfl
  · simp [embedInfinite, globalScale, finiteScale]

theorem embedFinite_intertwines_scale (u : ℚˣ) (x : RationalFiniteAdele) :
    embedFinite (finiteScale u x) = globalScale u (embedFinite x) := by
  apply Prod.ext
  · simp [embedFinite, globalScale, infiniteScale]
  · rfl

theorem G1_local_to_global_embedding :
    Function.Injective embedInfinite ∧
    Function.Injective embedFinite ∧
    (∀ a : GlobalSpace, embedInfinite a.1 + embedFinite a.2 = a) ∧
    (∀ u : ℚˣ, ∀ x : RationalInfiniteAdele,
      embedInfinite (infiniteScale u x) = globalScale u (embedInfinite x)) ∧
    (∀ u : ℚˣ, ∀ x : RationalFiniteAdele,
      embedFinite (finiteScale u x) = globalScale u (embedFinite x)) := by
  exact ⟨embedInfinite_injective, embedFinite_injective, global_decomposition,
    embedInfinite_intertwines_scale, embedFinite_intertwines_scale⟩

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
