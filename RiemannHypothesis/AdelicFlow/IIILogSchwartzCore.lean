import RiemannHypothesis.AdelicFlow.IIISchwartzCore

noncomputable section

open MeasureTheory
open scoped LinearPMap FourierTransform SchwartzMap

namespace RiemannHypothesis.AdelicFlow

/-!
# Number III-A: transport of the Schwartz graph core

`IIISchwartzCore` proves the graph-core theorem for the maximal coordinate
operator `Q`.  This file transports that result first through the nonzero real
scalar `2π`, then through the Plancherel Fourier unitary.  The target is the
exact reverse graph-closure inclusion for the local logarithmic generator.
-/

/-- Restriction of the Fourier-normalized coordinate operator `2π Q` to
Schwartz `L²` vectors. -/
def scaledCoordinateOperatorSchwartzRestriction : LogHilbert →ₗ.[ℂ] LogHilbert :=
  scaledCoordinateOperator.domRestrict logSchwartzSubmodule

/-- The scaled Schwartz restriction is contained in the maximal scaled operator. -/
theorem scaledCoordinateOperatorSchwartzRestriction_le :
    scaledCoordinateOperatorSchwartzRestriction ≤ scaledCoordinateOperator := by
  exact LinearPMap.domRestrict_le

/-- Continuous map carrying a graph point `(u, Qu)` to `(u, 2π Qu)`. -/
def coordinateToScaledGraphCLM :
    (LogHilbert × LogHilbert) →L[ℂ] (LogHilbert × LogHilbert) :=
  (ContinuousLinearMap.fst ℂ LogHilbert LogHilbert).prod
    (fourierScale • ContinuousLinearMap.snd ℂ LogHilbert LogHilbert)

@[simp]
theorem coordinateToScaledGraphCLM_apply (u v : LogHilbert) :
    coordinateToScaledGraphCLM (u, v) = (u, fourierScale • v) := by
  simp [coordinateToScaledGraphCLM]

/-- Coordinate graph points are carried to graph points of `2π Q`. -/
theorem coordinateToScaledGraphCLM_mem_scaledGraph
    {z : LogHilbert × LogHilbert} (hz : z ∈ coordinateOperator.graph) :
    coordinateToScaledGraphCLM z ∈ scaledCoordinateOperator.graph := by
  rw [LinearPMap.mem_graph_iff'] at hz ⊢
  rcases hz with ⟨u, rfl⟩
  let su : scaledCoordinateOperator.domain :=
    ⟨(u : LogHilbert), by simpa using u.property⟩
  refine ⟨su, ?_⟩
  rw [coordinateToScaledGraphCLM_apply]
  apply Prod.ext
  · rfl
  · rw [scaledCoordinateOperator_apply]
    rfl

/-- The graph map also carries the coordinate Schwartz graph into the scaled
Schwartz graph. -/
theorem coordinateToScaledGraphCLM_mem_scaledSchwartzGraph
    {z : LogHilbert × LogHilbert}
    (hz : z ∈ coordinateOperatorSchwartzRestriction.graph) :
    coordinateToScaledGraphCLM z ∈
      scaledCoordinateOperatorSchwartzRestriction.graph := by
  rw [LinearPMap.mem_graph_iff'] at hz ⊢
  rcases hz with ⟨u, rfl⟩
  have huS : (u : LogHilbert) ∈ logSchwartzSubmodule := by
    exact u.property.1
  have huQ : (u : LogHilbert) ∈ coordinateOperator.domain := by
    exact u.property.2
  have huScaled : (u : LogHilbert) ∈ scaledCoordinateOperator.domain := by
    simpa using huQ
  let su : scaledCoordinateOperatorSchwartzRestriction.domain :=
    ⟨(u : LogHilbert), by
      change (u : LogHilbert) ∈
        logSchwartzSubmodule ⊓ scaledCoordinateOperator.domain
      exact ⟨huS, huScaled⟩⟩
  refine ⟨su, ?_⟩
  rw [coordinateToScaledGraphCLM_apply]
  apply Prod.ext
  · rfl
  · change fourierScale • coordinateOperator
        ⟨(u : LogHilbert), huQ⟩ =
      scaledCoordinateOperator
        ⟨(u : LogHilbert), huScaled⟩
    rw [scaledCoordinateOperator_apply]
    rfl

/-- The maximal graph of `2π Q` lies in the closure of its Schwartz-restricted
graph.  This is the coordinate core theorem transported by the continuous
output-scaling map. -/
theorem scaledCoordinateOperator_graph_le_schwartzGraphClosure :
    scaledCoordinateOperator.graph ≤
      scaledCoordinateOperatorSchwartzRestriction.graph.topologicalClosure := by
  intro z hz
  rw [LinearPMap.mem_graph_iff'] at hz
  rcases hz with ⟨u, rfl⟩
  let q : coordinateOperator.domain :=
    ⟨(u : LogHilbert), by simpa using u.property⟩
  have hqSub :
      ((q : LogHilbert), coordinateOperator q) ∈
        coordinateOperatorSchwartzRestriction.graph.topologicalClosure :=
    coordinateOperator_graph_le_schwartzGraphClosure
      (by
        rw [LinearPMap.mem_graph_iff']
        exact ⟨q, rfl⟩)
  have hqSet :
      ((q : LogHilbert), coordinateOperator q) ∈
        closure (coordinateOperatorSchwartzRestriction.graph :
          Set (LogHilbert × LogHilbert)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hqSub
  have hImage :
      coordinateToScaledGraphCLM ((q : LogHilbert), coordinateOperator q) ∈
        closure (coordinateToScaledGraphCLM ''
          (coordinateOperatorSchwartzRestriction.graph :
            Set (LogHilbert × LogHilbert))) := by
    apply image_closure_subset_closure_image coordinateToScaledGraphCLM.continuous
    exact ⟨((q : LogHilbert), coordinateOperator q), hqSet, rfl⟩
  have hsubset :
      coordinateToScaledGraphCLM ''
          (coordinateOperatorSchwartzRestriction.graph :
            Set (LogHilbert × LogHilbert)) ⊆
        (scaledCoordinateOperatorSchwartzRestriction.graph :
          Set (LogHilbert × LogHilbert)) := by
    rintro _ ⟨w, hw, rfl⟩
    exact coordinateToScaledGraphCLM_mem_scaledSchwartzGraph hw
  have hScaledSet :
      coordinateToScaledGraphCLM ((q : LogHilbert), coordinateOperator q) ∈
        closure (scaledCoordinateOperatorSchwartzRestriction.graph :
          Set (LogHilbert × LogHilbert)) :=
    closure_mono hsubset hImage
  have hMap :
      coordinateToScaledGraphCLM ((q : LogHilbert), coordinateOperator q) =
        ((u : LogHilbert), scaledCoordinateOperator u) := by
    rw [coordinateToScaledGraphCLM_apply, scaledCoordinateOperator_apply]
    rfl
  rw [hMap] at hScaledSet
  change ((u : LogHilbert), scaledCoordinateOperator u) ∈
    (scaledCoordinateOperatorSchwartzRestriction.graph.topologicalClosure :
      Set (LogHilbert × LogHilbert))
  rw [Submodule.topologicalClosure_coe]
  exact hScaledSet

/-- The scaled Schwartz restriction is closable because `2π Q` is self-adjoint. -/
theorem scaledCoordinateOperatorSchwartzRestriction_isClosable :
    scaledCoordinateOperatorSchwartzRestriction.IsClosable := by
  exact scaledCoordinateOperator_selfAdjoint.isClosed.isClosable.leIsClosable
    scaledCoordinateOperatorSchwartzRestriction_le

/-- The maximal scaled operator lies in the closure of its Schwartz restriction. -/
theorem scaledCoordinateOperator_le_schwartzClosure :
    scaledCoordinateOperator ≤ scaledCoordinateOperatorSchwartzRestriction.closure := by
  apply LinearPMap.le_of_le_graph
  rw [← scaledCoordinateOperatorSchwartzRestriction_isClosable.graph_closure_eq_closure_graph]
  exact scaledCoordinateOperator_graph_le_schwartzGraphClosure

/-- The Fourier transform preserves the Schwartz `L²` submodule. -/
theorem logFourierUnitary_mem_logSchwartzSubmodule
    {u : LogHilbert} (hu : u ∈ logSchwartzSubmodule) :
    logFourierUnitary u ∈ logSchwartzSubmodule := by
  change u ∈ LinearMap.range
    (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 volume).toLinearMap at hu
  rcases hu with ⟨f, rfl⟩
  rw [logFourierUnitary_schwartz_toLp]
  change (𝓕 f).toLp 2 volume ∈ LinearMap.range
    (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 volume).toLinearMap
  exact ⟨𝓕 f, rfl⟩

/-- The inverse Fourier transform also preserves the Schwartz `L²` submodule. -/
theorem logFourierUnitary_symm_mem_logSchwartzSubmodule
    {u : LogHilbert} (hu : u ∈ logSchwartzSubmodule) :
    logFourierUnitary.symm u ∈ logSchwartzSubmodule := by
  change u ∈ LinearMap.range
    (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 volume).toLinearMap at hu
  rcases hu with ⟨f, rfl⟩
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

@[simp]
theorem logFourierGraphEquiv_apply (u v : LogHilbert) :
    logFourierGraphEquiv (u, v) =
      (logFourierUnitary u, logFourierUnitary v) := by
  rfl

/-- Fourier carries the graph of the local logarithmic generator to the graph
of `2π Q`. -/
theorem logFourierGraphEquiv_mem_scaledGraph
    {z : LogHilbert × LogHilbert} (hz : z ∈ logGenerator.graph) :
    logFourierGraphEquiv z ∈ scaledCoordinateOperator.graph := by
  rw [LinearPMap.mem_graph_iff'] at hz ⊢
  rcases hz with ⟨u, rfl⟩
  refine ⟨logGeneratorFourierDomainMap u, ?_⟩
  rw [logFourierGraphEquiv_apply]
  apply Prod.ext
  · exact (logGeneratorFourierDomainMap_coe u).symm
  · exact fourier_logGenerator u

/-- Inverse Fourier carries a scaled Schwartz graph point to a Schwartz graph
point of the logarithmic generator. -/
theorem logFourierGraphEquiv_symm_mem_logSchwartzGraph
    {z : LogHilbert × LogHilbert}
    (hz : z ∈ scaledCoordinateOperatorSchwartzRestriction.graph) :
    logFourierGraphEquiv.symm z ∈ logGeneratorSchwartzRestriction.graph := by
  rw [LinearPMap.mem_graph_iff'] at hz ⊢
  rcases hz with ⟨s, rfl⟩
  have hsS : (s : LogHilbert) ∈ logSchwartzSubmodule := s.property.1
  have hsScaled : (s : LogHilbert) ∈ scaledCoordinateOperator.domain := s.property.2
  let sd : scaledCoordinateOperator.domain := ⟨(s : LogHilbert), hsScaled⟩
  let u : logGenerator.domain := logGeneratorFourierDomainEquiv.symm sd
  have hMap : logGeneratorFourierDomainMap u = sd := by
    simpa [logGeneratorFourierDomainMap, u] using
      logGeneratorFourierDomainEquiv.apply_symm_apply sd
  have hFu : logFourierUnitary (u : LogHilbert) = (s : LogHilbert) := by
    rw [← logGeneratorFourierDomainMap_coe u, hMap]
    rfl
  have hInvU : logFourierUnitary.symm (s : LogHilbert) = (u : LogHilbert) := by
    apply logFourierUnitary.injective
    simp [hFu]
  have huS : (u : LogHilbert) ∈ logSchwartzSubmodule := by
    rw [← hInvU]
    exact logFourierUnitary_symm_mem_logSchwartzSubmodule hsS
  let ur : logGeneratorSchwartzRestriction.domain :=
    ⟨(u : LogHilbert), by
      change (u : LogHilbert) ∈ logSchwartzSubmodule ⊓ logGenerator.domain
      exact ⟨huS, u.property⟩⟩
  refine ⟨ur, ?_⟩
  rw [ContinuousLinearEquiv.prodCongr_symm]
  change
    (logFourierUnitary.symm (s : LogHilbert),
      logFourierUnitary.symm
        (scaledCoordinateOperator
          ⟨(s : LogHilbert), hsScaled⟩)) =
      ((ur : LogHilbert), logGeneratorSchwartzRestriction ur)
  apply Prod.ext
  · exact hInvU
  · change logFourierUnitary.symm (scaledCoordinateOperator sd) = logGenerator u
    rw [logGenerator_apply, hMap]

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
    rw [← Submodule.topologicalClosure_coe]
    exact hScaledSub
  have hInvImage :
      logFourierGraphEquiv.symm (logFourierGraphEquiv z) ∈
        closure (logFourierGraphEquiv.symm ''
          (scaledCoordinateOperatorSchwartzRestriction.graph :
            Set (LogHilbert × LogHilbert))) := by
    apply image_closure_subset_closure_image logFourierGraphEquiv.symm.continuous
    exact ⟨logFourierGraphEquiv z, hScaledSet, rfl⟩
  have hsubset :
      logFourierGraphEquiv.symm ''
          (scaledCoordinateOperatorSchwartzRestriction.graph :
            Set (LogHilbert × LogHilbert)) ⊆
        (logGeneratorSchwartzRestriction.graph :
          Set (LogHilbert × LogHilbert)) := by
    rintro _ ⟨w, hw, rfl⟩
    exact logFourierGraphEquiv_symm_mem_logSchwartzGraph hw
  have hzSet :
      logFourierGraphEquiv.symm (logFourierGraphEquiv z) ∈
        closure (logGeneratorSchwartzRestriction.graph :
          Set (LogHilbert × LogHilbert)) :=
    closure_mono hsubset hInvImage
  rw [logFourierGraphEquiv.symm_apply_apply] at hzSet
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
