/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.GeometryOfNumbers.Measure.IntegralDualCovolume
public import ArakelovGeometry.NumberTheory.NumberField.Archimedean.Covolume
public import ArakelovGeometry.NumberTheory.NumberField.TraceDual.OrdinaryNorm
import Mathlib.Topology.Sheaves.Init

/-! # Reciprocal ordinary covolume of the actual integral trace dual -/

@[expose] public section

noncomputable section
open NumberField MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldTraceDualCovolume

open AdelicStructure NumberFieldArchimedeanVectorDiagonal NumberFieldArchimedeanEuclidean
  NumberFieldArchimedeanTracePairing NumberFieldOrdinaryTraceDualNorm GeometryOfNumbers

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- The inner product compatible with the independently defined ordinary trace-dual
norm. The original norm and real module are retained, and no global instance is installed. -/
@[instance_reducible]
def ordinaryTraceDualInnerProduct
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    letI := ordinaryTraceDualNormedAddCommGroup ξ
    letI := ordinaryTraceDualNormedSpace ξ
    InnerProductSpace ℝ (CompletedVectorProduct K (Module.Dual K E)) := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct hξ
  let := ordinaryTraceDualNormedAddCommGroup ξ
  let := ordinaryTraceDualNormedSpace ξ
  let := strongDualInnerProduct (E := CompletedVectorProduct K E)
  apply InnerProductSpace.ofNorm ℝ
  intro f g
  have h := parallelogram_law_with_norm ℝ
    (ordinaryTraceDualIsometry hξ f) (ordinaryTraceDualIsometry hξ g)
  simpa only [← map_add, ← map_sub, LinearIsometryEquiv.norm_map, pow_two] using h

/-- The original integer-valued algebraic real dual and the actual continuous integral
dual are literally equal after the canonical algebraic-to-continuous equivalence. -/
theorem integralRealDual_eq_integralDual
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (M : Submodule (𝓞 K) E) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    letI := euclideanInnerProduct hξ
    (integralRealDual M).map
      ((LinearMap.toContinuousLinearMap : Module.Dual ℝ (CompletedVectorProduct K E) ≃ₗ[ℝ]
        StrongDual ℝ (CompletedVectorProduct K E)).toLinearMap.restrictScalars ℤ) =
      integralDual (diagonalLattice M) := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct hξ
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩ x hx
    obtain ⟨m, rfl⟩ := hx
    exact hg m
  · intro hf
    refine ⟨f.toLinearMap, ?_, ?_⟩
    · intro m
      exact hf _ ⟨m, rfl⟩
    · ext x
      rfl

/-- The ordinary trace isometry maps the actual integral trace-dual diagonal onto the
canonical integer dual of the original diagonal lattice. -/
theorem ordinaryTraceDualIsometry_integralDual_image
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    letI := euclideanInnerProduct hξ
    letI := ordinaryTraceDualNormedAddCommGroup ξ
    letI := ordinaryTraceDualNormedSpace ξ
    (diagonalLattice (NumberFieldIntegralTraceDual.integralTraceDual M)).map
      ((ordinaryTraceDualIsometry hξ).toLinearEquiv.toLinearMap.restrictScalars ℤ) =
        integralDual (diagonalLattice M) := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct hξ
  let := ordinaryTraceDualNormedAddCommGroup ξ
  let := ordinaryTraceDualNormedSpace ξ
  rw [ordinaryTraceDualIsometry_integral_image hξ M hfg hspan,
    integralRealDual_eq_integralDual hξ M]

/-- Actual ordinary covolume of the literal integral trace-dual diagonal, using the
canonical volume of its independently defined trace-dual norm. -/
def ordinaryTraceDualCovolume
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (M : Submodule (𝓞 K) E) : ℝ := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := ordinaryTraceDualNormedAddCommGroup ξ
  let := ordinaryTraceDualNormedSpace ξ
  let := ordinaryTraceDualInnerProduct hξ
  let : MeasurableSpace (CompletedVectorProduct K (Module.Dual K E)) := borel _
  let : BorelSpace (CompletedVectorProduct K (Module.Dual K E)) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K (Module.Dual K E))
  exact ZLattice.covolume (diagonalLattice (NumberFieldIntegralTraceDual.integralTraceDual M))

/-- The actual integral trace-dual diagonal has reciprocal ordinary covolume, for the
canonical measures of the independently defined ordinary primal and trace-dual norms. -/
theorem ordinaryTraceDualCovolume_eq_inv
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    ordinaryTraceDualCovolume ξ hξ M =
      (NumberFieldArchimedeanCovolume.euclideanCovolume ξ hξ M)⁻¹ := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct hξ
  let : MeasurableSpace (CompletedVectorProduct K E) := borel _
  let : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
  let := ordinaryTraceDualNormedAddCommGroup ξ
  let := ordinaryTraceDualNormedSpace ξ
  let := ordinaryTraceDualInnerProduct hξ
  let : MeasurableSpace (CompletedVectorProduct K (Module.Dual K E)) := borel _
  let : BorelSpace (CompletedVectorProduct K (Module.Dual K E)) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K (Module.Dual K E))
  let := strongDualInnerProduct (E := CompletedVectorProduct K E)
  let : MeasurableSpace (StrongDual ℝ (CompletedVectorProduct K E)) := borel _
  let : BorelSpace (StrongDual ℝ (CompletedVectorProduct K E)) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := StrongDual ℝ (CompletedVectorProduct K E))
  let := euclidean_discrete_diagonalLattice ξ M hfg hspan
  let := euclidean_isZLattice_diagonalLattice ξ M hfg hspan
  let := integralDual_discrete (diagonalLattice M)
  let := integralDual_isZLattice (diagonalLattice M)
  let e := ordinaryTraceDualIsometry hξ
  have hmap := ordinaryTraceDualIsometry_integralDual_image hξ M hfg hspan
  have hcomap : ZLattice.comap ℝ (integralDual (diagonalLattice M))
      e.toLinearEquiv.toLinearMap =
        diagonalLattice (NumberFieldIntegralTraceDual.integralTraceDual M) := by
    change (integralDual (diagonalLattice M)).comap
      (e.toLinearEquiv.toLinearMap.restrictScalars ℤ) = _
    have hk : (e.toLinearEquiv.toLinearMap.restrictScalars ℤ).ker = ⊥ :=
      LinearMap.ker_eq_bot.mpr e.injective
    rw [← hmap, Submodule.comap_map_eq, hk, sup_bot_eq]
  have hmeasure : MeasurePreserving e := e.measurePreserving
  have hcov := ZLattice.covolume_comap (integralDual (diagonalLattice M)) volume volume
    (e := e.toContinuousLinearEquiv) hmeasure
  change ZLattice.covolume (ZLattice.comap ℝ (integralDual (diagonalLattice M))
    e.toLinearEquiv.toLinearMap) volume = _ at hcov
  rw [hcomap] at hcov
  change ZLattice.covolume (diagonalLattice
    (NumberFieldIntegralTraceDual.integralTraceDual M)) volume =
      (ZLattice.covolume (diagonalLattice M) volume)⁻¹
  exact hcov.trans (integralDual_covolume (diagonalLattice M))

end ArakelovGeometry.NumberFieldTraceDualCovolume
