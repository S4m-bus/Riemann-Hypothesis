import RiemannHypothesis.AdelicFlow.IIIScaledCoordinate
import Mathlib.Analysis.Fourier.LpSpace

noncomputable section

open MeasureTheory
open scoped LinearPMap FourierTransform

namespace RiemannHypothesis.AdelicFlow

/-!
# Number III: Fourier transport to the logarithmic generator

With mathlib's Fourier normalization,

  F(f')(ξ) = 2π i ξ F(f)(ξ).

Hence the self-adjoint momentum operator `-i ∂q` is the unitary conjugate of
`2π Q`, where `Q` is maximal multiplication by the real coordinate.
-/

/-- Plancherel Fourier transform on the logarithmic Hilbert space.

This remains the exact unitary Fourier transform.  The later domain equivalence
is only its restriction to the maximal unbounded-operator domains. -/
def logFourierUnitary : LogHilbert ≃ₗᵢ[ℂ] LogHilbert :=
  MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ

/-- Maximal domain of the Fourier-transported generator. -/
def logGeneratorDomain : Submodule ℂ LogHilbert :=
  scaledCoordinateOperator.domain.comap logFourierUnitary.toLinearMap

/-- The exact Fourier transform restricted to the two maximal domains.

This is not a replacement of Fourier by an arbitrary linear map: it is the
restriction of `logFourierUnitary.toLinearEquiv` supplied by mathlib's native
`LinearEquiv.ofSubmodule'` construction. -/
def logGeneratorFourierDomainEquiv :
    logGeneratorDomain ≃ₗ[ℂ] scaledCoordinateOperator.domain := by
  change (scaledCoordinateOperator.domain.comap logFourierUnitary.toLinearMap) ≃ₗ[ℂ]
    scaledCoordinateOperator.domain
  exact logFourierUnitary.toLinearEquiv.ofSubmodule' scaledCoordinateOperator.domain

/-- Linear-map view of the restricted Fourier domain equivalence. -/
def logGeneratorFourierDomainMap :
    logGeneratorDomain →ₗ[ℂ] scaledCoordinateOperator.domain :=
  logGeneratorFourierDomainEquiv.toLinearMap

@[simp]
theorem logGeneratorFourierDomainMap_coe (f : logGeneratorDomain) :
    (logGeneratorFourierDomainMap f : LogHilbert) =
      logFourierUnitary (f : LogHilbert) := by
  simp only [logGeneratorFourierDomainMap, logGeneratorFourierDomainEquiv,
    LinearEquiv.ofSubmodule'_apply]

/-- The maximal logarithmic generator, defined by exact unitary conjugation
`F⁻¹ (2π Q) F`. -/
def logGenerator : LogHilbert →ₗ.[ℂ] LogHilbert where
  domain := logGeneratorDomain
  toFun := logFourierUnitary.symm.toLinearMap.comp
    (scaledCoordinateOperator.toFun.comp logGeneratorFourierDomainMap)

@[simp]
theorem logGenerator_domain : logGenerator.domain = logGeneratorDomain := by
  rfl

@[simp]
theorem logGenerator_apply (f : logGenerator.domain) :
    logGenerator f = logFourierUnitary.symm
      (scaledCoordinateOperator (logGeneratorFourierDomainMap f)) := by
  rfl

/-- Applying Fourier after the transported generator recovers `2π Q`. -/
@[simp]
theorem fourier_logGenerator (f : logGenerator.domain) :
    logFourierUnitary (logGenerator f) =
      scaledCoordinateOperator (logGeneratorFourierDomainMap f) := by
  simp [logGenerator_apply]

/-- The maximal transported domain is dense because Fourier is an open
homeomorphism and the Fourier-side maximal domain is dense. -/
theorem logGeneratorDomain_dense :
    Dense (logGenerator.domain : Set LogHilbert) := by
  change Dense (logGeneratorDomain : Set LogHilbert)
  have h := scaledCoordinateDomain_dense.preimage logFourierUnitary.toHomeomorph.isOpenMap
  simpa [logGeneratorDomain] using h

/-- Unitary transport preserves symmetry. -/
theorem logGenerator_isFormalAdjoint :
    logGenerator.IsFormalAdjoint logGenerator := by
  intro f g
  have hA := scaledCoordinateOperator_isFormalAdjoint
    (logGeneratorFourierDomainMap f) (logGeneratorFourierDomainMap g)
  calc
    inner ℂ (logGenerator f) (g : LogHilbert) =
        inner ℂ (logFourierUnitary (logGenerator f))
          (logFourierUnitary (g : LogHilbert)) := by
            symm
            exact logFourierUnitary.inner_map_map _ _
    _ = inner ℂ
        (scaledCoordinateOperator (logGeneratorFourierDomainMap f))
        (logGeneratorFourierDomainMap g : LogHilbert) := by
          rw [fourier_logGenerator]
          rfl
    _ = inner ℂ
        (logGeneratorFourierDomainMap f : LogHilbert)
        (scaledCoordinateOperator (logGeneratorFourierDomainMap g)) := hA
    _ = inner ℂ (logFourierUnitary (f : LogHilbert))
        (logFourierUnitary (logGenerator g)) := by
          rw [fourier_logGenerator]
          rfl
    _ = inner ℂ (f : LogHilbert) (logGenerator g) := by
          exact logFourierUnitary.inner_map_map _ _

/-- If `y` belongs to the adjoint domain of the transported operator, then its
Fourier transform belongs to the adjoint domain of `2π Q`. -/
theorem fourier_mem_scaledAdjoint_of_mem_logAdjoint {y : LogHilbert}
    (hy : y ∈ (logGenerator†).domain) :
    logFourierUnitary y ∈ (scaledCoordinateOperator†).domain := by
  let yAdj : (logGenerator†).domain := ⟨y, hy⟩
  apply LinearPMap.mem_adjoint_domain_of_exists
  refine ⟨logFourierUnitary (logGenerator† yAdj), ?_⟩
  intro x
  let xLog : logGeneratorDomain := logGeneratorFourierDomainEquiv.symm x
  have hxMap : logGeneratorFourierDomainMap xLog = x := by
    simpa [logGeneratorFourierDomainMap, xLog] using
      logGeneratorFourierDomainEquiv.apply_symm_apply x
  have hxFourier : logFourierUnitary (xLog : LogHilbert) = (x : LogHilbert) := by
    rw [← logGeneratorFourierDomainMap_coe xLog, hxMap]
  have hAdj := LinearPMap.adjoint_isFormalAdjoint logGeneratorDomain_dense yAdj xLog
  calc
    inner ℂ (logFourierUnitary (logGenerator† yAdj)) (x : LogHilbert) =
        inner ℂ (logFourierUnitary (logGenerator† yAdj))
          (logFourierUnitary (xLog : LogHilbert)) := by rw [hxFourier]
    _ = inner ℂ (logGenerator† yAdj) (xLog : LogHilbert) := by
          exact logFourierUnitary.inner_map_map _ _
    _ = inner ℂ y (logGenerator xLog) := hAdj
    _ = inner ℂ (logFourierUnitary y)
        (logFourierUnitary (logGenerator xLog)) := by
          symm
          exact logFourierUnitary.inner_map_map _ _
    _ = inner ℂ (logFourierUnitary y)
        (scaledCoordinateOperator x) := by
          rw [fourier_logGenerator, hxMap]

/-- The adjoint of the transported generator has no larger domain. -/
theorem logGeneratorAdjoint_domain_le :
    (logGenerator†).domain ≤ logGenerator.domain := by
  intro y hy
  have hFourierAdj :
      logFourierUnitary y ∈ (scaledCoordinateOperator†).domain :=
    fourier_mem_scaledAdjoint_of_mem_logAdjoint hy
  have hscaledEq : scaledCoordinateOperator† = scaledCoordinateOperator :=
    LinearPMap.isSelfAdjoint_def.mp scaledCoordinateOperator_selfAdjoint
  rw [hscaledEq] at hFourierAdj
  change logFourierUnitary y ∈ scaledCoordinateOperator.domain
  exact hFourierAdj

/-- Symmetry plus density embeds the transported operator in its adjoint. -/
theorem logGenerator_le_adjoint : logGenerator ≤ logGenerator† := by
  exact logGenerator_isFormalAdjoint.le_adjoint logGeneratorDomain_dense

/-- The exact Fourier-transported logarithmic generator is self-adjoint. -/
theorem logGenerator_selfAdjoint : IsSelfAdjoint logGenerator := by
  have hdom : logGenerator.domain = (logGenerator†).domain := by
    apply le_antisymm
    · exact logGenerator_le_adjoint.1
    · exact logGeneratorAdjoint_domain_le
  rw [LinearPMap.isSelfAdjoint_def]
  exact (LinearPMap.eq_of_le_of_domain_eq logGenerator_le_adjoint hdom).symm

/-- Number III is complete for the local logarithmic generator defined by
Fourier conjugation. -/
theorem logGenerator_numberIII : NumberIII logGenerator := by
  exact (numberIII_iff_isSelfAdjoint logGenerator).2 logGenerator_selfAdjoint

end RiemannHypothesis.AdelicFlow
