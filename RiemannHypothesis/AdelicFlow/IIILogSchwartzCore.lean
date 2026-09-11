import RiemannHypothesis.AdelicFlow.IIIScaledSchwartzCore

noncomputable section

open MeasureTheory
open scoped LinearPMap FourierTransform SchwartzMap

namespace RiemannHypothesis.AdelicFlow

/-!
# Number III-A: Fourier transport of the Schwartz graph core

The coordinate and scaled-coordinate graph-core theorems are already sealed.
This file performs only the final transport through the Plancherel Fourier
unitary, from `2π Q` to the local logarithmic generator
`F⁻¹ (2π Q) F`.
-/

/-- Fourier transform preserves the Schwartz `L²` submodule. -/
theorem logFourierUnitary_mem_logSchwartzSubmodule
    {u : LogHilbert} (hu : u ∈ logSchwartzSubmodule) :
    logFourierUnitary u ∈ logSchwartzSubmodule := by
  change u ∈ LinearMap.range
    (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 volume).toLinearMap at hu
  rcases hu with ⟨f, rfl⟩
  simp only [SchwartzMap.toLpCLM_apply]
  rw [logFourierUnitary_schwartz_toLp]
  change (𝓕 f).toLp 2 volume ∈ LinearMap.range
    (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 volume).toLinearMap
  exact ⟨𝓕 f, rfl⟩

/-- Inverse Fourier transform preserves the Schwartz `L²` submodule. -/
theorem logFourierUnitary_symm_mem_logSchwartzSubmodule
    {u : LogHilbert} (hu : u ∈ logSchwartzSubmodule) :
    logFourierUnitary.symm u ∈ logSchwartzSubmodule := by
  change u ∈ LinearMap.range
    (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 volume).toLinearMap at hu
  rcases hu with ⟨f, rfl⟩
  simp only [SchwartzMap.toLpCLM_apply]
  have hInv :
      logFourierUnitary.symm (f.toLp 2 volume) =
        (𝓕⁻ f).toLp 2 volume := by
    change (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm
        (f.toLp 2 volume) = (𝓕⁻ f).toLp 2 volume
    exact SchwartzMap.toLp_fourierInv_eq f
  rw [hInv]
  change (𝓕⁻ f).toLp 2 volume ∈ LinearMap.range
    (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 volume).toLinearMap
  exact ⟨𝓕⁻ f, rfl⟩

/-- Fourier transform applied componentwise to graph space. -/
def logFourierGraphEquiv :
    (LogHilbert × LogHilbert) ≃L[ℂ] (LogHilbert × LogHilbert) :=
  logFourierUnitary.toContinuousLinearEquiv.prodCongr
    logFourierUnitary.toContinuousLinearEquiv

/-- Inverse Fourier transform applied componentwise to graph space. -/
def logFourierInvGraphEquiv :
    (LogHilbert × LogHilbert) ≃L[ℂ] (LogHilbert × LogHilbert) :=
  logFourierUnitary.symm.toContinuousLinearEquiv.prodCongr
    logFourierUnitary.symm.toContinuousLinearEquiv

@[simp]
theorem logFourierGraphEquiv_apply (u v : LogHilbert) :
    logFourierGraphEquiv (u, v) =
      (logFourierUnitary u, logFourierUnitary v) := by
  rfl

@[simp]
theorem logFourierInvGraphEquiv_apply (u v : LogHilbert) :
    logFourierInvGraphEquiv (u, v) =
      (logFourierUnitary.symm u, logFourierUnitary.symm v) := by
  rfl

@[simp]
theorem logFourierInvGraphEquiv_logFourierGraphEquiv
    (z : LogHilbert × LogHilbert) :
    logFourierInvGraphEquiv (logFourierGraphEquiv z) = z := by
  rcases z with ⟨u, v⟩
  simp

/-- Fourier carries the graph of the local logarithmic generator to the graph
of the exact Fourier-side operator `2π Q`. -/
theorem logFourierGraphEquiv_mem_scaledGraph
    {z : LogHilbert × LogHilbert} (hz : z ∈ logGenerator.graph) :
    logFourierGraphEquiv z ∈ scaledCoordinateOperator.graph := by
  rw [LinearPMap.mem_graph_iff'] at hz ⊢
  rcases hz with ⟨u, rfl⟩
  refine ⟨logGeneratorFourierDomainMap u, ?_⟩
  rw [logFourierGraphEquiv_apply]
  apply Prod.ext
  · exact logGeneratorFourierDomainMap_coe u
  · exact (fourier_logGenerator u).symm

/-- Inverse Fourier carries a scaled Schwartz graph point to a Schwartz graph
point of the logarithmic generator. -/
theorem logFourierInvGraphEquiv_mem_logSchwartzGraph
    {z : LogHilbert × LogHilbert}
    (hz : z ∈ scaledCoordinateOperatorSchwartzRestriction.graph) :
    logFourierInvGraphEquiv z ∈ logGeneratorSchwartzRestriction.graph := by
  rw [LinearPMap.mem_graph_iff'] at hz ⊢
  rcases hz with ⟨s, rfl⟩
  have hsS : (s : LogHilbert) ∈ logSchwartzSubmodule := s.property.1
  have hsScaled : (s : LogHilbert) ∈ scaledCoordinateOperator.domain := s.property.2
  let sd : scaledCoordinateOperator.domain := ⟨(s : LogHilbert), hsScaled⟩
  have hScaledRestr :
      scaledCoordinateOperatorSchwartzRestriction s =
        scaledCoordinateOperator sd := by
    exact LinearPMap.domRestrict_apply rfl
  let u : logGenerator.domain := logGeneratorFourierDomainEquiv.symm sd
  have hMap : logGeneratorFourierDomainMap u = sd := by
    simpa [logGeneratorFourierDomainMap, u] using
      logGeneratorFourierDomainEquiv.apply_symm_apply sd
  have hFu : logFourierUnitary (u : LogHilbert) = (s : LogHilbert) := by
    rw [← logGeneratorFourierDomainMap_coe u, hMap]
    rfl
  have hInvU : logFourierUnitary.symm (s : LogHilbert) = (u : LogHilbert) := by
    rw [← hFu]
  have huS : (u : LogHilbert) ∈ logSchwartzSubmodule := by
    rw [← hInvU]
    exact logFourierUnitary_symm_mem_logSchwartzSubmodule hsS
  let ur : logGeneratorSchwartzRestriction.domain :=
    ⟨(u : LogHilbert), by
      change (u : LogHilbert) ∈ logSchwartzSubmodule ⊓ logGenerator.domain
      exact ⟨huS, u.property⟩⟩
  have hLogRestr :
      logGeneratorSchwartzRestriction ur = logGenerator u := by
    exact LinearPMap.domRestrict_apply rfl
  have hLog :
      logGenerator u =
        logFourierUnitary.symm (scaledCoordinateOperator sd) := by
    rw [logGenerator_apply, hMap]
  refine ⟨ur, ?_⟩
  rw [logFourierInvGraphEquiv_apply, hScaledRestr, hLogRestr]
  apply Prod.ext
  · exact hInvU.symm
  · exact hLog

/-- The maximal logarithmic-generator graph lies in the closure of the Schwartz
restricted graph.  This is the exact missing reverse graph-closure inclusion. -/
theorem logGenerator_graph_le_schwartzGraphClosure :
    logGenerator.graph ≤
      logGeneratorSchwartzRestriction.graph.topologicalClosure := by
  intro z hz
  have hFgraph : logFourierGraphEquiv z ∈ scaledCoordinateOperator.graph :=
    logFourierGraphEquiv_mem_scaledGraph hz
  have hScaledSub :
      logFourierGraphEquiv z ∈
        scaledCoordinateOperatorSchwartzRestriction.graph.topologicalClosure :=
    scaledCoordinateOperator_graph_le_schwartzGraphClosure hFgraph
  have hScaledSet :
      logFourierGraphEquiv z ∈
        closure (scaledCoordinateOperatorSchwartzRestriction.graph :
          Set (LogHilbert × LogHilbert)) := by
    change logFourierGraphEquiv z ∈
      (scaledCoordinateOperatorSchwartzRestriction.graph.topologicalClosure :
        Set (LogHilbert × LogHilbert)) at hScaledSub
    rw [Submodule.topologicalClosure_coe] at hScaledSub
    exact hScaledSub
  have hInvImage :
      logFourierInvGraphEquiv (logFourierGraphEquiv z) ∈
        closure (logFourierInvGraphEquiv ''
          (scaledCoordinateOperatorSchwartzRestriction.graph :
            Set (LogHilbert × LogHilbert))) := by
    apply image_closure_subset_closure_image logFourierInvGraphEquiv.continuous
    exact ⟨logFourierGraphEquiv z, hScaledSet, rfl⟩
  have hsubset :
      logFourierInvGraphEquiv ''
          (scaledCoordinateOperatorSchwartzRestriction.graph :
            Set (LogHilbert × LogHilbert)) ⊆
        (logGeneratorSchwartzRestriction.graph :
          Set (LogHilbert × LogHilbert)) := by
    rintro _ ⟨w, hw, rfl⟩
    exact logFourierInvGraphEquiv_mem_logSchwartzGraph hw
  have hzSet :
      logFourierInvGraphEquiv (logFourierGraphEquiv z) ∈
        closure (logGeneratorSchwartzRestriction.graph :
          Set (LogHilbert × LogHilbert)) :=
    closure_mono hsubset hInvImage
  rw [logFourierInvGraphEquiv_logFourierGraphEquiv] at hzSet
  change z ∈
    (logGeneratorSchwartzRestriction.graph.topologicalClosure :
      Set (LogHilbert × LogHilbert))
  rw [Submodule.topologicalClosure_coe]
  exact hzSet

/-- The maximal local logarithmic generator is contained in the closure of its
Schwartz restriction. -/
theorem logGenerator_le_logGeneratorSchwartzClosure :
    logGenerator ≤ logGeneratorSchwartzRestriction.closure := by
  apply LinearPMap.le_of_le_graph
  rw [← logGeneratorSchwartzRestriction_isClosable.graph_closure_eq_closure_graph]
  exact logGenerator_graph_le_schwartzGraphClosure

/-- Exact closure equality for the Schwartz restriction. -/
theorem logGeneratorSchwartzClosure_eq_logGenerator :
    logGeneratorSchwartzRestriction.closure = logGenerator := by
  exact le_antisymm logGeneratorSchwartzClosure_le_logGenerator
    logGenerator_le_logGeneratorSchwartzClosure

/-- Schwartz functions are a graph core for the local self-adjoint logarithmic
generator.  This seals the remaining local Number III-A core obligation. -/
theorem logGenerator_hasSchwartzCore :
    logGenerator.HasCore logSchwartzSubmodule := by
  exact (logGenerator_hasSchwartzCore_iff).2
    logGeneratorSchwartzClosure_eq_logGenerator

/-- Consolidated local III-A boundary: self-adjointness, the exact differential
action on Schwartz functions, and the graph-core theorem all hold together. -/
theorem logGenerator_local_IIIA_sealed :
    IsSelfAdjoint logGenerator ∧
      logGenerator.HasCore logSchwartzSubmodule ∧
      (∀ f : SchwartzMap ℝ ℂ,
        logGenerator (schwartzLogGeneratorVector f) =
          (logMomentumSchwartz f).toLp 2 volume) := by
  exact ⟨logGenerator_selfAdjoint, logGenerator_hasSchwartzCore,
    logGenerator_eq_negI_deriv_on_schwartz⟩

end RiemannHypothesis.AdelicFlow
