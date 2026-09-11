import RiemannHypothesis.AdelicFlow.IIIFourierGenerator
import Mathlib.Analysis.Distribution.FourierMultiplier

noncomputable section

open MeasureTheory
open scoped LinearPMap FourierTransform SchwartzMap
open LineDeriv

namespace RiemannHypothesis.AdelicFlow

/-!
# Number III: identification with `-i ∂q` on the Schwartz core

The operator `logGenerator` was defined abstractly by the exact unitary conjugation
`F⁻¹ (2π Q) F`.  Here we identify that operator on the dense Schwartz core with
the differential expression `-i d/dq`.
-/

/-- The Schwartz-space momentum expression `-i ∂q`. -/
def logMomentumSchwartz (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (-Complex.I) • (∂_{(1 : ℝ)} f)

/-- On ordinary functions this is exactly `-i` times the derivative. -/
@[simp]
theorem logMomentumSchwartz_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    logMomentumSchwartz f x = -Complex.I * deriv f x := by
  simp [logMomentumSchwartz, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    fderiv_apply_one_eq_deriv, smul_eq_mul]

/-- Coordinate multiplication on a Schwartz vector agrees with the maximal `L²`
multiplication operator. -/
theorem coordinateOperator_schwartz (f : SchwartzMap ℝ ℂ) :
    coordinateOperator
        ⟨f.toLp 2 volume, schwartz_toLp_mem_coordinateDomain f⟩ =
      (coordinateSchwartz f).toLp 2 volume := by
  rw [coordinateOperator_apply, Lp.ext_iff]
  filter_upwards [coordinateApply_ae
      ⟨f.toLp 2 volume, schwartz_toLp_mem_coordinateDomain f⟩,
    f.coeFn_toLp 2 volume,
    (coordinateSchwartz f).coeFn_toLp 2 volume] with x hQ hf hcoord
  rw [hQ, hcoord, coordinateSchwartz_apply]
  simp [coordinateWeighted, hf]

/-- Every Schwartz `L²` vector belongs to the maximal domain of the transported
logarithmic generator. -/
theorem schwartz_toLp_mem_logGeneratorDomain (f : SchwartzMap ℝ ℂ) :
    f.toLp 2 volume ∈ logGenerator.domain := by
  change logFourierUnitary (f.toLp 2 volume) ∈ scaledCoordinateOperator.domain
  rw [SchwartzMap.toLp_fourier_eq]
  simpa [scaledCoordinateOperator] using schwartz_toLp_mem_coordinateDomain (𝓕 f)

/-- Fourier transform of `-i ∂q f` is exactly multiplication by `2π ξ`. -/
theorem fourier_logMomentumSchwartz (f : SchwartzMap ℝ ℂ) :
    𝓕 (logMomentumSchwartz f) = fourierScale • coordinateSchwartz (𝓕 f) := by
  rw [logMomentumSchwartz, FourierTransform.fourier_smul,
    SchwartzMap.fourier_lineDerivOp_eq]
  have hg : (fun x : ℝ => inner ℝ x (1 : ℝ)).HasTemperateGrowth := by
    fun_prop
  ext x
  simp [SchwartzMap.smulLeftCLM_apply_apply hg, coordinateSchwartz_apply,
    fourierScale, smul_eq_mul]
  ring

/-- Exact theorem-level identification of the abstract self-adjoint generator
with `-i d/dq` on Schwartz functions. -/
theorem logGenerator_eq_negI_deriv_on_schwartz (f : SchwartzMap ℝ ℂ) :
    logGenerator
        ⟨f.toLp 2 volume, schwartz_toLp_mem_logGeneratorDomain f⟩ =
      (logMomentumSchwartz f).toLp 2 volume := by
  apply logFourierUnitary.injective
  rw [fourier_logGenerator]
  rw [SchwartzMap.toLp_fourier_eq]

  have hFmem : (𝓕 f).toLp 2 volume ∈ scaledCoordinateOperator.domain := by
    simpa [scaledCoordinateOperator] using schwartz_toLp_mem_coordinateDomain (𝓕 f)
  have hMap :
      logGeneratorFourierDomainMap
          ⟨f.toLp 2 volume, schwartz_toLp_mem_logGeneratorDomain f⟩ =
        ⟨(𝓕 f).toLp 2 volume, hFmem⟩ := by
    apply Subtype.ext
    exact SchwartzMap.toLp_fourier_eq f
  rw [hMap]

  change fourierScale • coordinateOperator
      ⟨(𝓕 f).toLp 2 volume, by simpa [scaledCoordinateOperator] using hFmem⟩ =
    (𝓕 (logMomentumSchwartz f)).toLp 2 volume
  rw [coordinateOperator_schwartz, fourier_logMomentumSchwartz]
  rfl

/-- The local Number III operator is therefore self-adjoint and has the expected
`-i ∂q` action on a dense Schwartz core. -/
theorem logGenerator_local_boundary_sealed :
    IsSelfAdjoint logGenerator ∧
      (∀ f : SchwartzMap ℝ ℂ,
        logGenerator
            ⟨f.toLp 2 volume, schwartz_toLp_mem_logGeneratorDomain f⟩ =
          (logMomentumSchwartz f).toLp 2 volume) := by
  exact ⟨logGenerator_selfAdjoint, logGenerator_eq_negI_deriv_on_schwartz⟩

end RiemannHypothesis.AdelicFlow
