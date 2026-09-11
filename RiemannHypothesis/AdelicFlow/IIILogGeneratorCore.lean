import RiemannHypothesis.AdelicFlow.IIIFourierGenerator
import Mathlib.Analysis.Distribution.FourierMultiplier

noncomputable section

open MeasureTheory
open scoped LinearPMap FourierTransform SchwartzMap
open LineDeriv

namespace RiemannHypothesis.AdelicFlow

/-!
# Number III: identification with `-i ∂q` on the Schwartz test domain

The operator `logGenerator` was defined abstractly by the exact unitary conjugation
`F⁻¹ (2π Q) F`.  Here we identify that operator on the dense Schwartz test domain
with the differential expression `-i d/dq`.
-/

/-- The Schwartz-space momentum expression `-i ∂q`. -/
def logMomentumSchwartz (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (-Complex.I) • (∂_{(1 : ℝ)} f)

/-- On ordinary functions this is exactly `-i` times the derivative. -/
@[simp]
theorem logMomentumSchwartz_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    logMomentumSchwartz f x = -Complex.I * deriv f x := by
  simp [logMomentumSchwartz, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    smul_eq_mul]

/-- Schwartz `L²` vectors belong to the actual `LinearPMap` domain of `Q`. -/
theorem schwartz_toLp_mem_coordinateOperatorDomain (f : SchwartzMap ℝ ℂ) :
    f.toLp 2 volume ∈ coordinateOperator.domain := by
  change f.toLp 2 volume ∈ coordinateDomain
  exact schwartz_toLp_mem_coordinateDomain f

/-- Coordinate multiplication on a Schwartz vector agrees with the maximal `L²`
multiplication operator. -/
theorem coordinateOperator_schwartz (f : SchwartzMap ℝ ℂ) :
    coordinateOperator
        ⟨f.toLp 2 volume, schwartz_toLp_mem_coordinateOperatorDomain f⟩ =
      (coordinateSchwartz f).toLp 2 volume := by
  let fCoord : coordinateDomain :=
    ⟨f.toLp 2 volume, schwartz_toLp_mem_coordinateDomain f⟩
  change coordinateApply fCoord = (coordinateSchwartz f).toLp 2 volume
  rw [Lp.ext_iff]
  filter_upwards [coordinateApply_ae fCoord,
    f.coeFn_toLp 2 volume,
    (coordinateSchwartz f).coeFn_toLp 2 volume] with x hQ hf hcoord
  rw [hQ, hcoord, coordinateSchwartz_apply]
  simp [coordinateWeighted, fCoord, hf]

/-- The project name `logFourierUnitary` is exactly mathlib's Plancherel Fourier
transform on a Schwartz `L²` vector. -/
@[simp]
theorem logFourierUnitary_schwartz_toLp (f : SchwartzMap ℝ ℂ) :
    logFourierUnitary (f.toLp 2 volume) = (𝓕 f).toLp 2 volume := by
  change (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) (f.toLp 2 volume) =
    (𝓕 f).toLp 2 volume
  exact SchwartzMap.toLp_fourier_eq f

/-- Every Schwartz `L²` vector belongs to the explicit transported submodule. -/
theorem schwartz_toLp_mem_logGeneratorSubmodule (f : SchwartzMap ℝ ℂ) :
    f.toLp 2 volume ∈ logGeneratorDomain := by
  change logFourierUnitary (f.toLp 2 volume) ∈ scaledCoordinateOperator.domain
  rw [logFourierUnitary_schwartz_toLp]
  rw [scaledCoordinateOperator_domain]
  change (𝓕 f).toLp 2 volume ∈ coordinateDomain
  exact schwartz_toLp_mem_coordinateDomain (𝓕 f)

/-- Every Schwartz `L²` vector belongs to the maximal domain of the transported
logarithmic generator. -/
theorem schwartz_toLp_mem_logGeneratorDomain (f : SchwartzMap ℝ ℂ) :
    f.toLp 2 volume ∈ logGenerator.domain := by
  change f.toLp 2 volume ∈ logGeneratorDomain
  exact schwartz_toLp_mem_logGeneratorSubmodule f

/-- A packaged Schwartz vector in the explicit maximal transported domain.
Since `logGenerator.domain` is definitionally `logGeneratorDomain`, this same
vector is accepted by the unbounded operator while retaining the native domain
type expected by the restricted Fourier equivalence. -/
def schwartzLogGeneratorVector (f : SchwartzMap ℝ ℂ) : logGeneratorDomain :=
  ⟨f.toLp 2 volume, schwartz_toLp_mem_logGeneratorSubmodule f⟩

@[simp]
theorem schwartzLogGeneratorVector_coe (f : SchwartzMap ℝ ℂ) :
    (schwartzLogGeneratorVector f : LogHilbert) = f.toLp 2 volume := by
  rfl

/-- Fourier transform of `-i ∂q f` is exactly multiplication by `2π ξ`. -/
theorem fourier_logMomentumSchwartz (f : SchwartzMap ℝ ℂ) :
    𝓕 (logMomentumSchwartz f) = fourierScale • coordinateSchwartz (𝓕 f) := by
  rw [logMomentumSchwartz, FourierTransform.fourier_smul,
    SchwartzMap.fourier_lineDerivOp_eq]
  have hg : (fun x : ℝ => inner ℝ x (1 : ℝ)).HasTemperateGrowth := by
    fun_prop
  ext x
  simp only [smul_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply hg]
  simp [coordinateSchwartz_apply, fourierScale, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The restricted Fourier-domain map sends a packaged Schwartz vector to the
Fourier-transformed Schwartz vector in the multiplier domain. -/
theorem logGeneratorFourierDomainMap_schwartz (f : SchwartzMap ℝ ℂ) :
    (logGeneratorFourierDomainMap (schwartzLogGeneratorVector f) : LogHilbert) =
      (𝓕 f).toLp 2 volume := by
  rw [logGeneratorFourierDomainMap_coe]
  rw [schwartzLogGeneratorVector_coe]
  exact logFourierUnitary_schwartz_toLp f

/-- Exact theorem-level identification of the abstract self-adjoint generator
with `-i d/dq` on Schwartz functions. -/
theorem logGenerator_eq_negI_deriv_on_schwartz (f : SchwartzMap ℝ ℂ) :
    logGenerator (schwartzLogGeneratorVector f) =
      (logMomentumSchwartz f).toLp 2 volume := by
  apply logFourierUnitary.injective
  rw [fourier_logGenerator (schwartzLogGeneratorVector f)]
  rw [logFourierUnitary_schwartz_toLp]

  have hFmem : (𝓕 f).toLp 2 volume ∈ scaledCoordinateOperator.domain := by
    rw [scaledCoordinateOperator_domain]
    change (𝓕 f).toLp 2 volume ∈ coordinateDomain
    exact schwartz_toLp_mem_coordinateDomain (𝓕 f)
  have hMap :
      logGeneratorFourierDomainMap (schwartzLogGeneratorVector f) =
        ⟨(𝓕 f).toLp 2 volume, hFmem⟩ := by
    apply Subtype.ext
    exact logGeneratorFourierDomainMap_schwartz f
  rw [hMap]
  rw [scaledCoordinateOperator_apply]

  have hQ : coordinateOperator
      ⟨(𝓕 f).toLp 2 volume, by simpa using hFmem⟩ =
      (coordinateSchwartz (𝓕 f)).toLp 2 volume := by
    simpa using coordinateOperator_schwartz (𝓕 f)
  rw [hQ, fourier_logMomentumSchwartz]
  rfl

/-- The local Number III operator is self-adjoint and has the expected
`-i ∂q` action on the dense Schwartz test domain. -/
theorem logGenerator_local_boundary_sealed :
    IsSelfAdjoint logGenerator ∧
      (∀ f : SchwartzMap ℝ ℂ,
        logGenerator (schwartzLogGeneratorVector f) =
          (logMomentumSchwartz f).toLp 2 volume) := by
  exact ⟨logGenerator_selfAdjoint, logGenerator_eq_negI_deriv_on_schwartz⟩

end RiemannHypothesis.AdelicFlow
