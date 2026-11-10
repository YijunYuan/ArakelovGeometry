/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NumberFieldProjectiveTraceDualMetric
import Mathlib.LinearAlgebra.Contraction

/-! # Canonical generic transport of the original projective trace-dual tensor -/

noncomputable section
open NumberField
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldProjectiveTraceDualGeneric

open AdelicStructure NumberFieldCodifferentDual NumberFieldTraceDualizingLine
  NumberFieldProjectiveTraceDual NumberFieldProjectiveTraceDualMetric
attribute [local instance 2000] Algebra.toModule Algebra.toSMul

universe u

variable {K : Type u} [Field K] [NumberField K]
  (M : Type u) [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

private def dualHomEquiv :
    K ⊗[𝓞 K] Module.Dual (𝓞 K) M ≃ₗ[𝓞 K] (M →ₗ[𝓞 K] K) :=
  (TensorProduct.comm (𝓞 K) _ _).trans (dualTensorHomEquiv (𝓞 K) M K)

omit [NumberField K] in
private theorem dualHomEquiv_smul (c : K)
    (z : K ⊗[𝓞 K] Module.Dual (𝓞 K) M) :
    dualHomEquiv M (c • z) = c • dualHomEquiv M z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a φ =>
      ext m
      change (φ m) • (c * a) = c * ((φ m) • a)
      simp only [Algebra.smul_def]
      ring
  | add z t hz ht => simp only [smul_add, map_add, hz, ht]

/-- The canonical finite-projective generic dual base-change equivalence, without
assuming the original integral module is free. -/
def genericDualEquiv :
    K ⊗[𝓞 K] Module.Dual (𝓞 K) M ≃ₗ[K] Module.Dual K (K ⊗[𝓞 K] M) :=
  ({ (dualHomEquiv M).toAddEquiv with map_smul' := dualHomEquiv_smul M } :
    K ⊗[𝓞 K] Module.Dual (𝓞 K) M ≃ₗ[K] (M →ₗ[𝓞 K] K)).trans
      (LinearMap.liftBaseChangeEquiv K)

omit [NumberField K] in
@[simp]
theorem genericDualEquiv_tmul_apply
    (c d : K) (φ : Module.Dual (𝓞 K) M) (m : M) :
    genericDualEquiv M (c ⊗ₜ[𝓞 K] φ) (d ⊗ₜ[𝓞 K] m) =
      c * d * algebraMap (𝓞 K) K (φ m) := by
  change d * ((φ m) • c) = c * d * algebraMap (𝓞 K) K (φ m)
  rw [Algebra.smul_def]
  ring

/-- Scalar extension of the original codifferent tensor, distributed into the
actual generic dual and the actual scalar model of the dualizing line. -/
def traceTensorGenericPairEquiv :
    K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) ≃ₗ[K]
      Module.Dual K (K ⊗[𝓞 K] M) ⊗[K] K :=
  (TensorProduct.AlgebraTensorModule.distribBaseChange (𝓞 K) K
    (codifferentModule K) (Module.Dual (𝓞 K) M)).trans
      ((TensorProduct.congr (codifferentGenericEquiv K) (genericDualEquiv M)).trans
        (TensorProduct.comm K _ _))

@[simp]
theorem traceTensorGenericPairEquiv_tmul
    (c : K) (a : codifferentModule K) (φ : Module.Dual (𝓞 K) M) :
    traceTensorGenericPairEquiv M (c ⊗ₜ[𝓞 K] (a ⊗ₜ[𝓞 K] φ)) =
      genericDualEquiv M ((1 : K) ⊗ₜ[𝓞 K] φ) ⊗ₜ[K] (c * (a : K)) := by
  simp only [traceTensorGenericPairEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
    TensorProduct.congr_tmul, codifferentGenericEquiv_tmul, TensorProduct.comm_tmul]

/-- Canonical tensor-unit contraction of the generic original trace tensor is
the literal accepted original trace inclusion, extended linearly to K. -/
theorem traceTensorGenericPairEquiv_contract
    (c : K) (z : codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) :
    TensorProduct.rid K (Module.Dual K (K ⊗[𝓞 K] M))
      (traceTensorGenericPairEquiv M (c ⊗ₜ[𝓞 K] z)) =
        c • traceTensorInclusion (K := K) M z := by
  induction z using TensorProduct.induction_on with
  | zero =>
      simp only [TensorProduct.tmul_zero, map_zero, smul_zero]
      rfl
  | tmul a φ =>
      rw [traceTensorGenericPairEquiv_tmul, TensorProduct.rid_tmul]
      apply TensorProduct.AlgebraTensorModule.ext
      intro d m
      let f : K ⊗[𝓞 K] M →ₗ[K] K :=
        traceTensorInclusion (K := K) M (a ⊗ₜ[𝓞 K] φ)
      have hf1 : f ((1 : K) ⊗ₜ[𝓞 K] m) =
          algebraMap (𝓞 K) K (φ m) * (a : K) :=
        traceTensorInclusion_tmul_apply (K := K) M a φ m
      have hf : f (d ⊗ₜ[𝓞 K] m) =
          d * (algebraMap (𝓞 K) K (φ m) * (a : K)) := by
        calc
          f (d ⊗ₜ[𝓞 K] m) = f (d • ((1 : K) ⊗ₜ[𝓞 K] m)) := by
            congr 1
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          _ = d * f ((1 : K) ⊗ₜ[𝓞 K] m) := f.map_smul d _
          _ = _ := congrArg (d * ·) hf1
      change (c * (a : K)) *
        genericDualEquiv M ((1 : K) ⊗ₜ[𝓞 K] φ) (d ⊗ₜ[𝓞 K] m) =
          c * f (d ⊗ₜ[𝓞 K] m)
      rw [genericDualEquiv_tmul_apply, one_mul, hf]
      ring
  | add z t hz ht =>
      simp only [TensorProduct.tmul_add, map_add, smul_add, hz, ht]
      rfl

attribute [local instance] NumberFieldProjectiveGeneric.genericFiniteDimensional

/-- Prescribed tensor norms on the actual generic fibre of the original
codifferent tensor, transported through canonical distribution and dual base change. -/
def originalPrescribedTraceDualFamily
    {η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)}
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    NormFamily (normalizedNumberFieldAdelicStructure K)
      (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)) :=
  (prescribedTraceDualFamily hη).pullback (traceTensorGenericPairEquiv M).toLinearMap
    (traceTensorGenericPairEquiv M).injective

/-- Completed canonical distribution followed by tensor-unit contraction on the
literal generic fibre of the original codifferent tensor. -/
def originalTraceTensorProductEquiv :
    NumberFieldArchimedeanVectorDiagonal.CompletedVectorProduct K
      (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)) ≃ₗ[ℝ]
      NumberFieldArchimedeanVectorDiagonal.CompletedVectorProduct K
        (Module.Dual K (K ⊗[𝓞 K] M)) :=
  LinearEquiv.piCongrRight (fun w =>
    (LinearEquiv.baseChange K (NumberFieldArchimedeanVectorDiagonal.CompletedCoefficient w)
      _ _ ((traceTensorGenericPairEquiv M).trans
        (TensorProduct.rid K (Module.Dual K (K ⊗[𝓞 K] M))))).restrictScalars ℝ)

/-- The prescribed metric on the original projective codifferent tensor agrees
with the independent ordinary trace-dual metric under the canonical original map. -/
def originalPrescribedTraceDualIsometry
    {η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)}
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    letI := NumberFieldArchimedeanEuclidean.euclideanNormedAddCommGroup
      (originalPrescribedTraceDualFamily M hη)
    letI := NumberFieldArchimedeanEuclidean.euclideanNormedSpace
      (originalPrescribedTraceDualFamily M hη)
    letI := NumberFieldOrdinaryTraceDualNorm.ordinaryTraceDualNormedAddCommGroup η
    letI := NumberFieldOrdinaryTraceDualNorm.ordinaryTraceDualNormedSpace η
    NumberFieldArchimedeanVectorDiagonal.CompletedVectorProduct K
      (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)) ≃ₗᵢ[ℝ]
      NumberFieldArchimedeanVectorDiagonal.CompletedVectorProduct K
        (Module.Dual K (K ⊗[𝓞 K] M)) := by
  let := NumberFieldArchimedeanEuclidean.euclideanNormedAddCommGroup
    (originalPrescribedTraceDualFamily M hη)
  let := NumberFieldArchimedeanEuclidean.euclideanNormedSpace
    (originalPrescribedTraceDualFamily M hη)
  let := NumberFieldOrdinaryTraceDualNorm.ordinaryTraceDualNormedAddCommGroup η
  let := NumberFieldOrdinaryTraceDualNorm.ordinaryTraceDualNormedSpace η
  refine { originalTraceTensorProductEquiv M with norm_map' := ?_ }
  intro z
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [NumberFieldOrdinaryTraceDualNorm.ordinaryTraceDual_norm_sq,
    NumberFieldArchimedeanEuclidean.euclidean_norm_sq]
  apply Finset.sum_congr rfl
  intro w _
  let e := LinearEquiv.baseChange K (NumberFieldArchimedeanVectorDiagonal.CompletedCoefficient w)
    _ _ (TensorProduct.rid K (Module.Dual K (K ⊗[𝓞 K] M)))
  let t := (LinearEquiv.baseChange K
    (NumberFieldArchimedeanVectorDiagonal.CompletedCoefficient w) _ _
      (traceTensorGenericPairEquiv M)) (z w)
  have h := dualizingTensor_norm_infinite η.dual hη.dual w (e t)
  change (prescribedTraceDualFamily hη).norm (normalizedInfinitePlacePoint w)
      (e.symm (e t)) =
    (w.mult : ℝ) * η.dual.norm (normalizedInfinitePlacePoint w) (e t) at h
  rw [e.symm_apply_apply] at h
  change ((w.mult : ℝ) * η.dual.norm (normalizedInfinitePlacePoint w)
    ((LinearEquiv.baseChange K (NumberFieldArchimedeanVectorDiagonal.CompletedCoefficient w)
      _ _ ((traceTensorGenericPairEquiv M).trans
        (TensorProduct.rid K (Module.Dual K (K ⊗[𝓞 K] M))))) (z w))) ^ 2 =
      ((prescribedTraceDualFamily hη).norm (normalizedInfinitePlacePoint w) t) ^ 2
  rw [LinearEquiv.baseChange_trans]
  exact congrArg (fun r : ℝ => r ^ 2) h.symm

/-- The actual original tensor diagonal is carried to the literal accepted
trace-integral diagonal, in the same completed generic dual fibres. -/
theorem originalTraceTensorProductEquiv_diagonal
    (z : codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) :
    originalTraceTensorProductEquiv (K := K) M
      (NumberFieldArchimedeanVectorDiagonal.vectorDiagonalMap (K := K)
        ((1 : K) ⊗ₜ[𝓞 K] z)) = traceTensorDiagonalMap (K := K) M z := by
  ext w
  change (LinearEquiv.baseChange K (NumberFieldArchimedeanVectorDiagonal.CompletedCoefficient w)
    _ _ (TensorProduct.rid K (Module.Dual K (K ⊗[𝓞 K] M))))
      ((LinearEquiv.baseChange K
        (NumberFieldArchimedeanVectorDiagonal.CompletedCoefficient w) _ _
        (traceTensorGenericPairEquiv M))
          ((1 : NumberFieldArchimedeanVectorDiagonal.CompletedCoefficient w) ⊗ₜ[K]
            ((1 : K) ⊗ₜ[𝓞 K] z))) = _
  rw [LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul,
    traceTensorGenericPairEquiv_contract, one_smul]
  rfl

/-- The prescribed norm on an actual original tensor is the local trace factor
times the actual dual norm of its literal original trace representative. -/
theorem originalPrescribedTraceDualFamily_norm_original
    {η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)}
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (w : InfinitePlace K)
    (z : codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) :
    (originalPrescribedTraceDualFamily M hη).norm (normalizedInfinitePlacePoint w)
      ((1 : NumberFieldArchimedeanVectorDiagonal.CompletedCoefficient w) ⊗ₜ[K]
        ((1 : K) ⊗ₜ[𝓞 K] z)) =
      (w.mult : ℝ) * η.dual.norm (normalizedInfinitePlacePoint w)
        ((1 : NumberFieldArchimedeanVectorDiagonal.CompletedCoefficient w) ⊗ₜ[K]
          traceTensorInclusion (K := K) M z) := by
  have hp : traceTensorGenericPairEquiv M ((1 : K) ⊗ₜ[𝓞 K] z) =
      (TensorProduct.rid K (Module.Dual K (K ⊗[𝓞 K] M))).symm
        (traceTensorInclusion (K := K) M z) := by
    apply (TensorProduct.rid K (Module.Dual K (K ⊗[𝓞 K] M))).eq_symm_apply.mpr
    simpa only [one_smul] using traceTensorGenericPairEquiv_contract M 1 z
  change (prescribedTraceDualFamily hη).norm (normalizedInfinitePlacePoint w)
    ((1 : NumberFieldArchimedeanVectorDiagonal.CompletedCoefficient w) ⊗ₜ[K]
      traceTensorGenericPairEquiv M ((1 : K) ⊗ₜ[𝓞 K] z)) = _
  rw [hp]
  exact dualizingTensor_norm_infinite η.dual hη.dual w
    ((1 : NumberFieldArchimedeanVectorDiagonal.CompletedCoefficient w) ⊗ₜ[K]
      traceTensorInclusion (K := K) M z)

/-- The actual prescribed original tensor metric carries the source integer
functional to the completed ordinary trace pairing on the original module. -/
theorem originalPrescribedTraceDualIsometry_original
    {η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)}
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (z : codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) (m : M) :
    NumberFieldOrdinaryTraceDualNorm.ordinaryTraceDualIsometry hη
      (originalPrescribedTraceDualIsometry M hη
        (NumberFieldArchimedeanVectorDiagonal.vectorDiagonalMap (K := K)
          ((1 : K) ⊗ₜ[𝓞 K] z)))
      (NumberFieldProjectiveGeneric.originalDiagonalMap (K := K) M m) =
        (integerTensorEquiv (K := K) M z m : ℝ) := by
  change NumberFieldOrdinaryTraceDualNorm.ordinaryTraceDualIsometry hη
    (originalTraceTensorProductEquiv (K := K) M
      (NumberFieldArchimedeanVectorDiagonal.vectorDiagonalMap (K := K)
        ((1 : K) ⊗ₜ[𝓞 K] z))) _ = _
  rw [originalTraceTensorProductEquiv_diagonal]
  exact traceTensorDiagonalMap_original (K := K) M η hη z m

end ArakelovGeometry.NumberFieldProjectiveTraceDualGeneric
