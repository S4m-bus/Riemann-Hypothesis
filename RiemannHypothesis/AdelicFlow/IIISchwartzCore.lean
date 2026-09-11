import RiemannHypothesis.AdelicFlow.IIILogGeneratorCore
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Distribution.TemperateGrowth

noncomputable section

open MeasureTheory
open scoped LinearPMap FourierTransform SchwartzMap

namespace RiemannHypothesis.AdelicFlow

/-!
# Number III: Schwartz graph-core boundary

The local generator itself is now sealed: it is self-adjoint and agrees with
`-i ∂q` on Schwartz functions.  The next operator-theoretic obligation is the
stronger statement that Schwartz functions form a graph core.

This file packages the exact Schwartz `L²` submodule, proves that it lies in the
maximal domain and is dense in the ambient Hilbert space, and isolates the
remaining core equality in mathlib's native `LinearPMap.HasCore` language.
-/

/-- The complex-linear submodule of `L²(ℝ)` represented by Schwartz functions. -/
def logSchwartzSubmodule : Submodule ℂ LogHilbert :=
  LinearMap.range
    (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 volume).toLinearMap

/-- Every Schwartz `L²` vector lies in the maximal logarithmic-generator domain. -/
theorem logSchwartzSubmodule_le_logGeneratorDomain :
    logSchwartzSubmodule ≤ logGenerator.domain := by
  intro u hu
  change u ∈ LinearMap.range
    (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 volume).toLinearMap at hu
  rcases hu with ⟨f, rfl⟩
  change f.toLp 2 volume ∈ logGenerator.domain
  exact schwartz_toLp_mem_logGeneratorDomain f

/-- Schwartz vectors are dense in the ambient logarithmic Hilbert space.  This
is ordinary Hilbert-space density; the stronger graph-density statement is the
remaining core obligation below. -/
theorem logSchwartzSubmodule_dense :
    Dense (logSchwartzSubmodule : Set LogHilbert) := by
  have hd :
      DenseRange (SchwartzMap.toLpCLM ℝ (E := ℝ) ℂ 2 volume) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  apply hd.mono
  rintro u ⟨f, rfl⟩
  change f.toLp 2 volume ∈ logSchwartzSubmodule
  change f.toLp 2 volume ∈ LinearMap.range
    (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 volume).toLinearMap
  exact ⟨f, rfl⟩

/-! ## Bounded resolvent package for graph-density

The coordinate resolvent `(Q+i)⁻¹` has already been constructed pointwise in
`IIIResolvent`.  For the graph-core proof we also need its bounded-operator
realization on `L²`, so that ordinary density can be transported continuously
into the graph of the unbounded operator.
-/

/-- The multiplier `(x+i)⁻¹`, bundled as an `L∞` vector. -/
def plusResolventLpInf : MeasureTheory.Lp ℂ ⊤ (volume : Measure ℝ) :=
  plusResolventMultiplier_memLp_top.toLp plusResolventMultiplier

/-- Almost-everywhere representative of the bundled `L∞` resolvent multiplier. -/
theorem plusResolventLpInf_ae :
    (plusResolventLpInf : ℝ → ℂ) =ᵐ[volume] plusResolventMultiplier := by
  exact MemLp.coeFn_toLp plusResolventMultiplier_memLp_top

/-- Multiplication by `(x+i)⁻¹` as a bounded operator `L² → L²`. -/
def plusResolventCLM : LogHilbert →L[ℂ] LogHilbert :=
  ((ContinuousLinearMap.lsmul ℂ ℂ).holderL (volume : Measure ℝ) ⊤ 2 2)
    plusResolventLpInf

/-- The bounded resolvent package has the expected pointwise representative. -/
theorem plusResolventCLM_ae (g : LogHilbert) :
    (plusResolventCLM g : ℝ → ℂ) =ᵐ[volume] plusResolventWeighted g := by
  have hmul :=
    (ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder
      (r := (2 : ENNReal)) plusResolventLpInf g
  have h :
      ((ContinuousLinearMap.lsmul ℂ ℂ).holder (2 : ENNReal)
          plusResolventLpInf g : ℝ → ℂ) =ᵐ[volume]
        plusResolventWeighted g := by
    filter_upwards [hmul, plusResolventLpInf_ae] with x hx hres
    rw [hx, hres]
    simp [plusResolventWeighted, smul_eq_mul]
  simpa [plusResolventCLM] using h

/-- The new bounded resolvent is exactly the previously constructed resolvent vector. -/
theorem plusResolventCLM_eq_plusResolventVector (g : LogHilbert) :
    plusResolventCLM g = plusResolventVector g := by
  rw [Lp.ext_iff]
  exact (plusResolventCLM_ae g).trans (plusResolventVector_ae g).symm

/-- The rational resolvent multiplier has temperate growth.  We use the identity
`(x+i)⁻¹ = (1+x²)⁻¹ (x-i)`: mathlib already knows temperate growth of the
Bessel weight `(1+‖x‖²)^r`, so no all-orders rational-derivative estimate is
left implicit here. -/
theorem plusResolventMultiplier_hasTemperateGrowth :
    Function.HasTemperateGrowth plusResolventMultiplier := by
  have hweight :
      Function.HasTemperateGrowth
        (fun x : ℝ => (1 + ‖x‖ ^ 2) ^ (-1 : ℝ)) :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (-1)
  have haff :
      Function.HasTemperateGrowth (fun x : ℝ => (x : ℂ) - Complex.I) := by
    fun_prop
  have hprod :
      Function.HasTemperateGrowth
        (fun x : ℝ =>
          ((1 + ‖x‖ ^ 2) ^ (-1 : ℝ)) • ((x : ℂ) - Complex.I)) := by
    exact (ContinuousLinearMap.lsmul ℝ ℂ).bilinear_hasTemperateGrowth hweight haff
  convert hprod using 1
  funext x
  rw [plusResolventMultiplier, Complex.inv_def, normSq_plusDenom]
  simp [plusDenom, Real.rpow_neg_one, Real.norm_eq_abs, sq_abs, Complex.real_smul]
  ring

/-- Resolvent multiplication preserves Schwartz space. -/
def plusResolventSchwartz (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ plusResolventMultiplier f

@[simp]
theorem plusResolventSchwartz_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    plusResolventSchwartz f x = plusResolventMultiplier x * f x := by
  rw [plusResolventSchwartz]
  rw [SchwartzMap.smulLeftCLM_apply_apply plusResolventMultiplier_hasTemperateGrowth]
  simp [smul_eq_mul]

/-- On Schwartz input, the bounded `L²` resolvent is represented by the
Schwartz resolvent multiplier above. -/
theorem plusResolventCLM_schwartz_toLp (f : SchwartzMap ℝ ℂ) :
    plusResolventCLM (f.toLp 2 volume) =
      (plusResolventSchwartz f).toLp 2 volume := by
  rw [Lp.ext_iff]
  filter_upwards [plusResolventCLM_ae (f.toLp 2 volume),
    f.coeFn_toLp 2 volume,
    (plusResolventSchwartz f).coeFn_toLp 2 volume] with x hR hf hS
  rw [hR, hS]
  simp [plusResolventWeighted, plusResolventSchwartz_apply, hf]

/-! ## Coordinate graph parametrization

The bounded resolvent gives a continuous parametrization of the graph of `Q`:
`g ↦ (R₊ g, g - i R₊ g)`.  The next lemmas make both directions explicit.
-/

/-- Schwartz `L²` vectors also lie in the maximal coordinate domain. -/
theorem logSchwartzSubmodule_le_coordinateOperatorDomain :
    logSchwartzSubmodule ≤ coordinateOperator.domain := by
  intro u hu
  change u ∈ LinearMap.range
    (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 volume).toLinearMap at hu
  rcases hu with ⟨f, rfl⟩
  exact schwartz_toLp_mem_coordinateOperatorDomain f

/-- Restriction of the coordinate operator to Schwartz `L²` vectors. -/
def coordinateOperatorSchwartzRestriction : LogHilbert →ₗ.[ℂ] LogHilbert :=
  coordinateOperator.domRestrict logSchwartzSubmodule

/-- The coordinate Schwartz restriction is an operator restriction of `Q`. -/
theorem coordinateOperatorSchwartzRestriction_le_coordinateOperator :
    coordinateOperatorSchwartzRestriction ≤ coordinateOperator := by
  exact LinearPMap.domRestrict_le

/-- Continuous graph parametrization associated with the positive resolvent. -/
def coordinateGraphResolventCLM :
    LogHilbert →L[ℂ] (LogHilbert × LogHilbert) :=
  plusResolventCLM.prod
    ((ContinuousLinearMap.id ℂ LogHilbert) - Complex.I • plusResolventCLM)

@[simp]
theorem coordinateGraphResolventCLM_apply (g : LogHilbert) :
    coordinateGraphResolventCLM g =
      (plusResolventCLM g, g - Complex.I • plusResolventCLM g) := by
  simp [coordinateGraphResolventCLM]

/-- Applying the explicit bounded resolvent to `(Q+i)u` returns `u`.  This is
proved directly on `L²` representatives, so no hidden injectivity argument for
an unbounded shift is used. -/
theorem plusResolventCLM_coordinate_plus_I (u : coordinateOperator.domain) :
    plusResolventCLM
        (coordinateOperator u + Complex.I • (u : LogHilbert)) =
      (u : LogHilbert) := by
  rw [Lp.ext_iff]
  filter_upwards [
      plusResolventCLM_ae
        (coordinateOperator u + Complex.I • (u : LogHilbert)),
      coordinateApply_ae u,
      Lp.coeFn_add (coordinateOperator u) (Complex.I • (u : LogHilbert)),
      Lp.coeFn_smul Complex.I (u : LogHilbert)] with x hR hQ hAdd hSmul
  rw [hR]
  simp only [plusResolventWeighted]
  rw [hAdd]
  simp only [Pi.add_apply]
  rw [hSmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [coordinateOperator_apply, hQ]
  simp only [coordinateWeighted]
  change plusResolventMultiplier x *
      ((x : ℂ) * (u : LogHilbert) x + Complex.I * (u : LogHilbert) x) =
    (u : LogHilbert) x
  calc
    plusResolventMultiplier x *
        ((x : ℂ) * (u : LogHilbert) x + Complex.I * (u : LogHilbert) x) =
        (plusResolventMultiplier x * plusDenom x) * (u : LogHilbert) x := by
          simp [plusDenom]
          ring
    _ = (u : LogHilbert) x := by
      rw [mul_comm (plusResolventMultiplier x) (plusDenom x),
        plusDenom_mul_resolvent]
      simp

/-- The graph parametrization is onto the maximal coordinate graph. -/
theorem coordinateGraphResolventCLM_on_coordinateDomain
    (u : coordinateOperator.domain) :
    coordinateGraphResolventCLM
        (coordinateOperator u + Complex.I • (u : LogHilbert)) =
      ((u : LogHilbert), coordinateOperator u) := by
  rw [coordinateGraphResolventCLM_apply, plusResolventCLM_coordinate_plus_I]
  simp

/-- Restriction of the maximal self-adjoint generator to Schwartz `L²` vectors. -/
def logGeneratorSchwartzRestriction : LogHilbert →ₗ.[ℂ] LogHilbert :=
  logGenerator.domRestrict logSchwartzSubmodule

/-- The Schwartz restriction is an operator restriction of the maximal generator. -/
theorem logGeneratorSchwartzRestriction_le_logGenerator :
    logGeneratorSchwartzRestriction ≤ logGenerator := by
  exact LinearPMap.domRestrict_le

/-- The Schwartz restriction is closable because it has the closed self-adjoint
maximal generator as an extension. -/
theorem logGeneratorSchwartzRestriction_isClosable :
    logGeneratorSchwartzRestriction.IsClosable := by
  exact logGenerator_selfAdjoint.isClosed.isClosable.leIsClosable
    logGeneratorSchwartzRestriction_le_logGenerator

/-- A self-adjoint maximal generator is already equal to its operator closure. -/
theorem logGenerator_closure_eq :
    logGenerator.closure = logGenerator := by
  apply LinearPMap.eq_of_eq_graph
  have hc : logGenerator.IsClosable := logGenerator_selfAdjoint.isClosed.isClosable
  rw [← hc.graph_closure_eq_closure_graph]
  exact logGenerator_selfAdjoint.isClosed.submodule_topologicalClosure_eq

/-- Closing the Schwartz restriction cannot produce anything outside the maximal
self-adjoint logarithmic generator. -/
theorem logGeneratorSchwartzClosure_le_logGenerator :
    logGeneratorSchwartzRestriction.closure ≤ logGenerator := by
  have h :=
    (logGenerator_selfAdjoint.isClosed.isClosable).closure_mono
      logGeneratorSchwartzRestriction_le_logGenerator
  rw [logGenerator_closure_eq] at h
  exact h

/-- The exact remaining graph-core obligation.  Since containment in the maximal
domain is already proved above, `HasCore` is now equivalent to the single closure
equality for the Schwartz restriction. -/
theorem logGenerator_hasSchwartzCore_iff :
    logGenerator.HasCore logSchwartzSubmodule ↔
      logGeneratorSchwartzRestriction.closure = logGenerator := by
  constructor
  · intro hcore
    simpa [logGeneratorSchwartzRestriction] using hcore.closure_eq
  · intro hclosure
    refine ⟨logSchwartzSubmodule_le_logGeneratorDomain, ?_⟩
    simpa [logGeneratorSchwartzRestriction] using hclosure

end RiemannHypothesis.AdelicFlow
