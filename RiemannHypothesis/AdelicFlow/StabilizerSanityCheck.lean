import RiemannHypothesis.AdelicFlow.ScalingSiteBoundary

noncomputable section

namespace RiemannHypothesis.AdelicFlow

/-!
# G3 stabilizer sanity check

Before proving the full closed-orbit classification, we test the proposed
criterion against the singular archimedean stratum.

The naive statement

    cyclic stabilizer  <->  exactly one finite zero

is missing a necessary hypothesis: the infinite component must be nonzero.
Indeed, if the infinite component is zero, archimedean scaling fixes the point
for every real time, even when the finite zero set consists of exactly one
prime.  Hence the stabilizer is all of `ℝ`, not a discrete cyclic lattice.
-/

/-- Finite adele which is zero at exactly `v0` and one at every other finite
place. -/
def singleZeroFiniteAdele (v0 : RationalFinitePlace) : RationalFiniteAdele := by
  classical
  refine ⟨fun v => if v = v0 then 0 else 1, ?_⟩
  exact Filter.Eventually.of_forall fun v => by
    by_cases h : v = v0
    · simp [h]
    · simp [h]

/-- Its zero support is the singleton `{v0}`. -/
theorem singleZeroFiniteAdele_eq_zero_iff
    (v0 v : RationalFinitePlace) :
    singleZeroFiniteAdele v0 v = 0 ↔ v = v0 := by
  classical
  by_cases h : v = v0
  · subst v
    simp [singleZeroFiniteAdele]
  · simp [singleZeroFiniteAdele, h]

/-- A global adele with zero archimedean component and exactly one finite zero. -/
def archZeroSingleFiniteZero (v0 : RationalFinitePlace) : GlobalSpace :=
  (0, singleZeroFiniteAdele v0)

/-- Because the infinite component is zero, the global archimedean flow fixes
this point at every real time. -/
theorem archZeroSingleFiniteZero_fixed
    (v0 : RationalFinitePlace) (t : ℝ) :
    archimedeanGlobalFlow t (archZeroSingleFiniteZero v0) =
      archZeroSingleFiniteZero v0 := by
  apply Prod.ext
  · simp [archimedeanGlobalFlow, rationalInfiniteRealFlow,
      archZeroSingleFiniteZero]
  · rfl

/-- The corresponding point of the actual scaling-site quotient. -/
def archZeroSingleFiniteZeroSitePoint
    (v0 : RationalFinitePlace) : ScalingSiteQuotient :=
  toScalingSiteQuotient
    (toPrincipalQuotient (archZeroSingleFiniteZero v0))

/-- The descended scaling-site flow likewise fixes this point for every time. -/
theorem archZeroSingleFiniteZeroSitePoint_fixed
    (v0 : RationalFinitePlace) (t : ℝ) :
    scalingSiteFlow t (archZeroSingleFiniteZeroSitePoint v0) =
      archZeroSingleFiniteZeroSitePoint v0 := by
  change toScalingSiteQuotient
      (toPrincipalQuotient
        (archimedeanGlobalFlow t (archZeroSingleFiniteZero v0))) =
    toScalingSiteQuotient
      (toPrincipalQuotient (archZeroSingleFiniteZero v0))
  rw [archZeroSingleFiniteZero_fixed]

/-- A point fixed by every real time cannot have stabilizer `Tℤ` for any
positive `T`.  We use the return time `T/2`, which cannot be an integral
multiple of `T`. -/
theorem archZeroSingleFiniteZero_not_cyclic
    (v0 : RationalFinitePlace) :
    ¬ LiesOnClosedPrimitiveOrbit actualScalingSiteQuotientBoundary
        (archZeroSingleFiniteZeroSitePoint v0) := by
  rintro ⟨T, hT, hperiod⟩
  have hfix :
      actualScalingSiteQuotientBoundary.flow (T / 2)
          (archZeroSingleFiniteZeroSitePoint v0) =
        archZeroSingleFiniteZeroSitePoint v0 := by
    exact archZeroSingleFiniteZeroSitePoint_fixed v0 (T / 2)
  rcases (hperiod (T / 2)).1 hfix with ⟨n, hn⟩
  rw [zsmul_eq_mul] at hn
  have hnHalf : (n : ℝ) = (1 / 2 : ℝ) := by
    apply mul_right_cancel₀ hT.ne'
    calc
      (n : ℝ) * T = T / 2 := hn
      _ = (1 / 2 : ℝ) * T := by ring
  have hcases : n ≤ 0 ∨ 1 ≤ n := by omega
  rcases hcases with hn0 | hn1
  · have hn0' : (n : ℝ) ≤ 0 := by exact_mod_cast hn0
    linarith
  · have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith

/-- Kernel-level falsification of the unqualified singleton-zero criterion:
there exists a representative with exactly one finite zero whose scaling-site
stabilizer is not a nonzero cyclic lattice. -/
theorem singleton_finite_zero_alone_not_sufficient :
    ∃ (v0 : RationalFinitePlace) (a : GlobalSpace),
      (∀ v : RationalFinitePlace, a.2 v = 0 ↔ v = v0) ∧
      ¬ LiesOnClosedPrimitiveOrbit actualScalingSiteQuotientBoundary
          (toScalingSiteQuotient (toPrincipalQuotient a)) := by
  let v0 : RationalFinitePlace :=
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm
      ⟨2, Nat.prime_two⟩
  refine ⟨v0, archZeroSingleFiniteZero v0, ?_, ?_⟩
  · intro v
    exact singleZeroFiniteAdele_eq_zero_iff v0 v
  · exact archZeroSingleFiniteZero_not_cyclic v0

end RiemannHypothesis.AdelicFlow
