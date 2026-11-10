/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Tensor.Hermitian
public import ArakelovGeometry.NumberTheory.NumberField.TraceDual.DualizingLine.Basic
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import Mathlib.Topology.Sheaves.Init

/-! # Prescribed completed tensor metrics for the original projective trace dual -/

@[expose] public section

noncomputable section
open NumberField MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldProjectiveTraceDualMetric

open AdelicStructure NumberFieldArchimedeanVectorDiagonal NumberFieldTraceDualizingLine
  NumberFieldProjectiveTraceDual NumberFieldCodifferentDual NumberFieldOrdinaryTraceDualNorm
attribute [local instance 2000] Algebra.toModule Algebra.toSMul

universe u

variable {K : Type u} [Field K] [NumberField K]
  {E : Type u} [AddCommGroup E] [Module K E]

omit [NumberField K] in
/-- Canonical completed tensor-unit insertion is the actual completed pure tensor
with scalar generator one after the canonical distribution equivalence. -/
theorem tensorUnitBaseChange_symm
    (L : Type*) [Field L] [Algebra K L] (z : L ⊗[K] E) :
    (LinearEquiv.baseChange K L _ _ (TensorProduct.rid K E).symm) z =
      (TensorProduct.AlgebraTensorModule.distribBaseChange K L E K).symm
        (z ⊗ₜ[L] ((1 : L) ⊗ₜ[K] (1 : K))) := by
  apply (TensorProduct.AlgebraTensorModule.distribBaseChange K L E K).injective
  rw [LinearEquiv.apply_symm_apply]
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
      rw [LinearEquiv.baseChange_tmul, TensorProduct.rid_symm_apply,
        TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
  | add z t hz ht => simp only [map_add, TensorProduct.add_tmul, hz, ht]

variable [FiniteDimensional K E]

/-- The actual prescribed orthogonal tensor norm with the actual trace-dualizing line
is local-degree scaling under canonical completed tensor-unit contraction. -/
theorem dualizingTensor_norm_infinite
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (w : InfinitePlace K) (z : CompletedCoefficient w ⊗[K] E) :
    (ξ.orthogonalTensorPair (dualizingLine K).toNormFamily
      normalizedNumberFieldArchimedeanCompletions hξ (dualizingLine_isHermitian K)).norm
        (normalizedInfinitePlacePoint w)
        (LinearEquiv.baseChange K (CompletedCoefficient w) _ _ (TensorProduct.rid K E).symm z) =
          (w.mult : ℝ) * ξ.norm (normalizedInfinitePlacePoint w) z := by
  rw [tensorUnitBaseChange_symm]
  calc
    _ = ξ.norm (normalizedInfinitePlacePoint w) z *
        (dualizingLine K).norm (normalizedInfinitePlacePoint w)
          ((1 : CompletedCoefficient w) ⊗ₜ[K] (1 : K)) :=
      NormFamily.orthogonalTensorPair_norm_tmul_completed ξ (dualizingLine K).toNormFamily
        normalizedNumberFieldArchimedeanCompletions hξ (dualizingLine_isHermitian K) _ _ _
    _ = _ := by rw [dualizingLine_norm_generator, mul_comm]

/-- The prescribed actual Hermitian dual tensor norm on the ordinary generic tensor space. -/
def prescribedTraceDualFamily
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    NormFamily (normalizedNumberFieldAdelicStructure K) (Module.Dual K E ⊗[K] K) :=
  ξ.dual.orthogonalTensorPair (dualizingLine K).toNormFamily
    normalizedNumberFieldArchimedeanCompletions hξ.dual (dualizingLine_isHermitian K)

omit [FiniteDimensional K E] in
/-- Literal coordinatewise completed tensor-unit contraction, with the existing real actions. -/
def tensorUnitProductEquiv :
    CompletedVectorProduct K (E ⊗[K] K) ≃ₗ[ℝ] CompletedVectorProduct K E :=
  LinearEquiv.piCongrRight (fun w =>
    (LinearEquiv.baseChange K (CompletedCoefficient w) _ _
      (TensorProduct.rid K E)).restrictScalars ℝ)

/-- The prescribed completed dual-tensor metric agrees with the independently defined
ordinary trace-dual metric under the canonical tensor-unit equivalence. -/
def prescribedTraceDualIsometry
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    letI := NumberFieldArchimedeanEuclidean.euclideanNormedAddCommGroup
      (prescribedTraceDualFamily hξ)
    letI := NumberFieldArchimedeanEuclidean.euclideanNormedSpace (prescribedTraceDualFamily hξ)
    letI := ordinaryTraceDualNormedAddCommGroup ξ
    letI := ordinaryTraceDualNormedSpace ξ
    CompletedVectorProduct K (Module.Dual K E ⊗[K] K) ≃ₗᵢ[ℝ]
      CompletedVectorProduct K (Module.Dual K E) := by
  let := NumberFieldArchimedeanEuclidean.euclideanNormedAddCommGroup
    (prescribedTraceDualFamily hξ)
  let := NumberFieldArchimedeanEuclidean.euclideanNormedSpace (prescribedTraceDualFamily hξ)
  let := ordinaryTraceDualNormedAddCommGroup ξ
  let := ordinaryTraceDualNormedSpace ξ
  refine { tensorUnitProductEquiv (K := K) (E := Module.Dual K E) with norm_map' := ?_ }
  intro z
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [ordinaryTraceDual_norm_sq, NumberFieldArchimedeanEuclidean.euclidean_norm_sq]
  apply Finset.sum_congr rfl
  intro w _
  let e := LinearEquiv.baseChange K (CompletedCoefficient w) _ _
    (TensorProduct.rid K (Module.Dual K E))
  have h := dualizingTensor_norm_infinite ξ.dual hξ.dual w (e (z w))
  change (prescribedTraceDualFamily hξ).norm (normalizedInfinitePlacePoint w)
    (e.symm (e (z w))) =
      (w.mult : ℝ) * ξ.dual.norm (normalizedInfinitePlacePoint w) (e (z w)) at h
  rw [e.symm_apply_apply] at h
  exact congrArg (fun r : ℝ => r ^ 2) h.symm

end ArakelovGeometry.NumberFieldProjectiveTraceDualMetric
