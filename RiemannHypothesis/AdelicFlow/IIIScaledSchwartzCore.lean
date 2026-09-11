import RiemannHypothesis.AdelicFlow.IIISchwartzCore

noncomputable section

open MeasureTheory
open scoped LinearPMap

namespace RiemannHypothesis.AdelicFlow

/-!
# Number III-A: transport of the Schwartz graph core to `2π Q`

The difficult graph-density step has already been proved for the maximal
coordinate operator `Q`.  Here we transport it through the nonzero scalar
normalization used by mathlib's Fourier convention.
-/

/-- Restriction of the Fourier-normalized coordinate operator to Schwartz vectors. -/
def scaledCoordinateOperatorSchwartzRestriction : LogHilbert →ₗ.[ℂ] LogHilbert :=
  scaledCoordinateOperator.domRestrict logSchwartzSubmodule

/-- The scaled Schwartz restriction is an operator restriction of `2π Q`. -/
theorem scaledCoordinateOperatorSchwartzRestriction_le :
    scaledCoordinateOperatorSchwartzRestriction ≤ scaledCoordinateOperator := by
  exact LinearPMap.domRestrict_le

/-- Reinterpret a maximal `Q`-domain vector as a maximal `2π Q`-domain vector. -/
def coordinateDomainToScaled (u : coordinateOperator.domain) :
    scaledCoordinateOperator.domain :=
  ⟨(u : LogHilbert), by simpa using u.property⟩

@[simp]
theorem coordinateDomainToScaled_coe (u : coordinateOperator.domain) :
    (coordinateDomainToScaled u : LogHilbert) = (u : LogHilbert) := by
  rfl

/-- Reinterpret a maximal `2π Q`-domain vector as a maximal `Q`-domain vector. -/
def scaledDomainToCoordinate (u : scaledCoordinateOperator.domain) :
    coordinateOperator.domain :=
  ⟨(u : LogHilbert), by simpa using u.property⟩

@[simp]
theorem scaledDomainToCoordinate_coe (u : scaledCoordinateOperator.domain) :
    (scaledDomainToCoordinate u : LogHilbert) = (u : LogHilbert) := by
  rfl

/-- The scaled operator really is coordinate multiplication followed by the
Fourier normalization scalar on the identified maximal domain. -/
theorem scaledCoordinateOperator_coordinateDomain (u : coordinateOperator.domain) :
    scaledCoordinateOperator (coordinateDomainToScaled u) =
      fourierScale • coordinateOperator u := by
  rw [scaledCoordinateOperator_apply]
  rfl

/-- Continuous map on graph space implementing `(x,y) ↦ (x, 2π y)`. -/
def coordinateGraphScaleCLM :
    (LogHilbert × LogHilbert) →L[ℂ] (LogHilbert × LogHilbert) :=
  (ContinuousLinearMap.id ℂ LogHilbert).prodMap
    (fourierScale • ContinuousLinearMap.id ℂ LogHilbert)

@[simp]
theorem coordinateGraphScaleCLM_apply (z : LogHilbert × LogHilbert) :
    coordinateGraphScaleCLM z = (z.1, fourierScale • z.2) := by
  rcases z with ⟨x, y⟩
  simp [coordinateGraphScaleCLM]

/-- The graph scaling map sends the Schwartz-restricted graph of `Q` into the
Schwartz-restricted graph of `2π Q`. -/
theorem coordinateGraphScaleCLM_mem_scaledSchwartzGraph
    {z : LogHilbert × LogHilbert}
    (hz : z ∈ coordinateOperatorSchwartzRestriction.graph) :
    coordinateGraphScaleCLM z ∈ scaledCoordinateOperatorSchwartzRestriction.graph := by
  rw [LinearPMap.mem_graph_iff'] at hz
  rcases hz with ⟨u, rfl⟩
  have huS : (u : LogHilbert) ∈ logSchwartzSubmodule := u.property.1
  have huQ : (u : LogHilbert) ∈ coordinateOperator.domain := u.property.2
  have huA : (u : LogHilbert) ∈ scaledCoordinateOperator.domain := by
    simpa using huQ
  let uq : coordinateOperator.domain := ⟨(u : LogHilbert), huQ⟩
  let us : scaledCoordinateOperatorSchwartzRestriction.domain :=
    ⟨(u : LogHilbert), by
      change (u : LogHilbert) ∈ logSchwartzSubmodule ⊓ scaledCoordinateOperator.domain
      exact ⟨huS, huA⟩⟩
  rw [LinearPMap.mem_graph_iff']
  refine ⟨us, ?_⟩
  rw [coordinateGraphScaleCLM_apply]
  apply Prod.ext
  · rfl
  · have hQ : coordinateOperatorSchwartzRestriction u = coordinateOperator uq := by
      exact LinearPMap.domRestrict_apply rfl
    have hA : scaledCoordinateOperatorSchwartzRestriction us =
        scaledCoordinateOperator ⟨(us : LogHilbert), us.property.2⟩ := by
      exact LinearPMap.domRestrict_apply rfl
    rw [hQ, hA]
    have hscaled := scaledCoordinateOperator_coordinateDomain uq
    rw [← hscaled]
    congr 2

/-- On a maximal scaled-domain vector, graph scaling of the corresponding `Q`
graph point is exactly the scaled graph point. -/
theorem coordinateGraphScaleCLM_on_scaledDomain
    (u : scaledCoordinateOperator.domain) :
    coordinateGraphScaleCLM
        ((scaledDomainToCoordinate u : LogHilbert),
          coordinateOperator (scaledDomainToCoordinate u)) =
      ((u : LogHilbert), scaledCoordinateOperator u) := by
  rw [coordinateGraphScaleCLM_apply, scaledCoordinateOperator_apply]
  apply Prod.ext
  · rfl
  · congr 2

/-- The maximal graph of `2π Q` lies in the closure of its Schwartz-restricted graph. -/
theorem scaledCoordinateOperator_graph_le_schwartzGraphClosure :
    scaledCoordinateOperator.graph ≤
      scaledCoordinateOperatorSchwartzRestriction.graph.topologicalClosure := by
  intro z hz
  rw [LinearPMap.mem_graph_iff'] at hz
  rcases hz with ⟨u, rfl⟩
  let q : coordinateOperator.domain := scaledDomainToCoordinate u
  have hqGraph :
      ((q : LogHilbert), coordinateOperator q) ∈ coordinateOperator.graph := by
    rw [LinearPMap.mem_graph_iff']
    exact ⟨q, rfl⟩
  have hqClosure := coordinateOperator_graph_le_schwartzGraphClosure hqGraph
  have hqSet :
      ((q : LogHilbert), coordinateOperator q) ∈
        closure (coordinateOperatorSchwartzRestriction.graph :
          Set (LogHilbert × LogHilbert)) := by
    change ((q : LogHilbert), coordinateOperator q) ∈
      (coordinateOperatorSchwartzRestriction.graph.topologicalClosure :
        Set (LogHilbert × LogHilbert)) at hqClosure
    rw [Submodule.topologicalClosure_coe] at hqClosure
    exact hqClosure
  have hImage :
      coordinateGraphScaleCLM ((q : LogHilbert), coordinateOperator q) ∈
        closure (coordinateGraphScaleCLM ''
          (coordinateOperatorSchwartzRestriction.graph :
            Set (LogHilbert × LogHilbert))) := by
    apply image_closure_subset_closure_image coordinateGraphScaleCLM.continuous
    exact ⟨((q : LogHilbert), coordinateOperator q), hqSet, rfl⟩
  have hsubset :
      coordinateGraphScaleCLM ''
          (coordinateOperatorSchwartzRestriction.graph :
            Set (LogHilbert × LogHilbert)) ⊆
        (scaledCoordinateOperatorSchwartzRestriction.graph :
          Set (LogHilbert × LogHilbert)) := by
    rintro _ ⟨w, hw, rfl⟩
    exact coordinateGraphScaleCLM_mem_scaledSchwartzGraph hw
  have hImage' :
      coordinateGraphScaleCLM ((q : LogHilbert), coordinateOperator q) ∈
        closure (scaledCoordinateOperatorSchwartzRestriction.graph :
          Set (LogHilbert × LogHilbert)) :=
    closure_mono hsubset hImage
  have hparam := coordinateGraphScaleCLM_on_scaledDomain u
  change coordinateGraphScaleCLM ((q : LogHilbert), coordinateOperator q) =
      ((u : LogHilbert), scaledCoordinateOperator u) at hparam
  rw [hparam] at hImage'
  change ((u : LogHilbert), scaledCoordinateOperator u) ∈
    (scaledCoordinateOperatorSchwartzRestriction.graph.topologicalClosure :
      Set (LogHilbert × LogHilbert))
  rw [Submodule.topologicalClosure_coe]
  exact hImage'

/-- The scaled Schwartz restriction is closable because `2π Q` is self-adjoint. -/
theorem scaledCoordinateOperatorSchwartzRestriction_isClosable :
    scaledCoordinateOperatorSchwartzRestriction.IsClosable := by
  exact scaledCoordinateOperator_selfAdjoint.isClosed.isClosable.leIsClosable
    scaledCoordinateOperatorSchwartzRestriction_le

/-- The self-adjoint maximal operator `2π Q` is equal to its own closure. -/
theorem scaledCoordinateOperator_closure_eq :
    scaledCoordinateOperator.closure = scaledCoordinateOperator := by
  apply LinearPMap.eq_of_eq_graph
  have hc : scaledCoordinateOperator.IsClosable :=
    scaledCoordinateOperator_selfAdjoint.isClosed.isClosable
  rw [← hc.graph_closure_eq_closure_graph]
  exact scaledCoordinateOperator_selfAdjoint.isClosed.submodule_topologicalClosure_eq

/-- The closure of the Schwartz restriction cannot exceed maximal `2π Q`. -/
theorem scaledCoordinateOperatorSchwartzClosure_le :
    scaledCoordinateOperatorSchwartzRestriction.closure ≤ scaledCoordinateOperator := by
  have h :=
    (scaledCoordinateOperator_selfAdjoint.isClosed.isClosable).closure_mono
      scaledCoordinateOperatorSchwartzRestriction_le
  rw [scaledCoordinateOperator_closure_eq] at h
  exact h

/-- Graph density gives the reverse operator inclusion. -/
theorem scaledCoordinateOperator_le_SchwartzClosure :
    scaledCoordinateOperator ≤ scaledCoordinateOperatorSchwartzRestriction.closure := by
  apply LinearPMap.le_of_le_graph
  rw [← scaledCoordinateOperatorSchwartzRestriction_isClosable.graph_closure_eq_closure_graph]
  exact scaledCoordinateOperator_graph_le_schwartzGraphClosure

/-- Schwartz functions form a graph core for the exact Fourier-side operator `2π Q`. -/
theorem scaledCoordinateOperator_hasSchwartzCore :
    scaledCoordinateOperator.HasCore logSchwartzSubmodule := by
  refine ⟨?_, ?_⟩
  · intro u hu
    have hQ : u ∈ coordinateOperator.domain :=
      logSchwartzSubmodule_le_coordinateOperatorDomain hu
    simpa using hQ
  · have hEq :
        scaledCoordinateOperatorSchwartzRestriction.closure = scaledCoordinateOperator :=
      le_antisymm scaledCoordinateOperatorSchwartzClosure_le
        scaledCoordinateOperator_le_SchwartzClosure
    simpa [scaledCoordinateOperatorSchwartzRestriction] using hEq

end RiemannHypothesis.AdelicFlow
