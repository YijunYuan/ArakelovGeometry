/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Model.GenericFibre.Projective
public import ArakelovGeometry.NumberTheory.NumberField.TraceDual.Codifferent.TensorDual
public import ArakelovGeometry.NumberTheory.NumberField.TraceDual.Covolume

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import Mathlib.Topology.Sheaves.Init

/-! # The original projective codifferent tensor in its literal trace-dual image -/

@[expose] public section

noncomputable section
open NumberField MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldProjectiveTraceDual

open AdelicStructure NumberFieldCodifferentDual NumberFieldIntegralTraceDual
  NumberFieldArchimedeanVectorDiagonal NumberFieldOrdinaryTraceDualNorm
attribute [local instance 2000] integralVectorModule

variable {K : Type*} [Field K] [NumberField K]
  (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- The original codifferent tensor identifies with the actual trace-integral dual
of the literal original generic image. -/
def traceTensorEquiv :
    codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M ≃ₗ[𝓞 K]
      integralTraceDual (NumberFieldInvertibleGeneric.genericImage (K := K) M) :=
  (TensorProduct.congr (LinearEquiv.refl (𝓞 K) (codifferentModule K))
    (NumberFieldProjectiveGeneric.genericImageEquiv (K := K) M).symm.dualMap).trans
      (NumberFieldCodifferentTensorDual.traceTensorEquiv _
        (NumberFieldProjectiveGeneric.genericImage_fg (K := K) M)
        (NumberFieldInvertibleGeneric.genericImage_fullSpan (K := K) M))

/-- Pure tensor evaluation takes place on the literal original generic inclusion. -/
@[simp]
theorem traceTensorEquiv_tmul_apply
    (a : codifferentModule K) (φ : Module.Dual (𝓞 K) M) (m : M) :
    (traceTensorEquiv (K := K) M (a ⊗ₜ[𝓞 K] φ)).1
      (NumberFieldInvertibleGeneric.genericInclusion (K := K) M m) =
        algebraMap (𝓞 K) K (φ m) * (a : K) := by
  change (NumberFieldCodifferentTensorDual.traceTensorEquiv _
    (NumberFieldProjectiveGeneric.genericImage_fg (K := K) M)
    (NumberFieldInvertibleGeneric.genericImage_fullSpan (K := K) M)
    (a ⊗ₜ[𝓞 K] (NumberFieldProjectiveGeneric.genericImageEquiv (K := K) M).symm.dualMap φ)).1
      ((NumberFieldProjectiveGeneric.genericImageEquiv (K := K) M m :
        NumberFieldInvertibleGeneric.genericImage (K := K) M) : K ⊗[𝓞 K] M) = _
  rw [NumberFieldCodifferentTensorDual.traceTensorEquiv_tmul_apply]
  simp

/-- Trace restriction gives the actual integer dual of the original abstract module. -/
def integerTensorEquiv :
    codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M ≃ₗ[ℤ] Module.Dual ℤ M := by
  exact ((traceTensorEquiv (K := K) M).restrictScalars ℤ).trans
    ((integralTraceEquiv _
      (NumberFieldInvertibleGeneric.genericImage_fullSpan (K := K) M)).trans
        ((NumberFieldProjectiveGeneric.genericImageEquiv (K := K) M).restrictScalars ℤ).dualMap)

/-- Original integer duality is evaluation of the actual rational trace representative. -/
@[simp]
theorem integerTensorEquiv_apply
    (z : codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) (m : M) :
    (integerTensorEquiv (K := K) M z m : ℚ) =
      Algebra.trace ℚ K ((traceTensorEquiv (K := K) M z).1
        (NumberFieldInvertibleGeneric.genericInclusion (K := K) M m)) := by
  exact integralTraceEquiv_apply _
    (NumberFieldInvertibleGeneric.genericImage_fullSpan (K := K) M)
    (traceTensorEquiv (K := K) M z)
    (NumberFieldProjectiveGeneric.genericImageEquiv (K := K) M m)

/-- The original tensor trace formula, with no replacement of the test module. -/
@[simp]
theorem integerTensorEquiv_tmul_apply
    (a : codifferentModule K) (φ : Module.Dual (𝓞 K) M) (m : M) :
    (integerTensorEquiv (K := K) M (a ⊗ₜ[𝓞 K] φ) m : ℚ) =
      Algebra.trace ℚ K (algebraMap (𝓞 K) K (φ m) * (a : K)) := by
  rw [integerTensorEquiv_apply, traceTensorEquiv_tmul_apply]

/-- The literal inclusion of the original tensor in the original generic K-linear dual. -/
def traceTensorInclusion :
    codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M →ₗ[𝓞 K]
      Module.Dual K (K ⊗[𝓞 K] M) :=
  (integralTraceDual (NumberFieldInvertibleGeneric.genericImage (K := K) M)).subtype.comp
    (traceTensorEquiv (K := K) M).toLinearMap

@[simp]
theorem traceTensorInclusion_tmul_apply
    (a : codifferentModule K) (φ : Module.Dual (𝓞 K) M) (m : M) :
    traceTensorInclusion (K := K) M (a ⊗ₜ[𝓞 K] φ)
      (NumberFieldInvertibleGeneric.genericInclusion (K := K) M m) =
        algebraMap (𝓞 K) K (φ m) * (a : K) :=
  traceTensorEquiv_tmul_apply (K := K) M a φ m

theorem traceTensorInclusion_injective :
    Function.Injective (traceTensorInclusion (K := K) M) :=
  Subtype.val_injective.comp (traceTensorEquiv (K := K) M).injective

theorem traceTensorInclusion_range :
    (traceTensorInclusion (K := K) M).range =
      integralTraceDual (NumberFieldInvertibleGeneric.genericImage (K := K) M) := by
  rw [traceTensorInclusion, (traceTensorEquiv (K := K) M).range_comp]
  exact Submodule.range_subtype _

/-- The original codifferent tensor diagonal in the literal completed generic dual. -/
def traceTensorDiagonalMap :
    codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M →ₗ[ℤ]
      CompletedVectorProduct K (Module.Dual K (K ⊗[𝓞 K] M)) :=
  (vectorDiagonalMap (K := K)).restrictScalars ℤ |>.comp
    ((traceTensorInclusion (K := K) M).restrictScalars ℤ)

@[simp]
theorem traceTensorDiagonalMap_apply
    (z : codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) (w : InfinitePlace K) :
    traceTensorDiagonalMap (K := K) M z w =
      (1 : CompletedCoefficient w) ⊗ₜ[K] traceTensorInclusion (K := K) M z := rfl

theorem traceTensorDiagonalMap_injective :
    Function.Injective (traceTensorDiagonalMap (K := K) M) :=
  NumberFieldArchimedeanCovolume.vectorDiagonalMap_injective.comp
    (traceTensorInclusion_injective (K := K) M)

/-- Equality of the original tensor and intrinsic trace-dual diagonal submodules
inside the same actual completed product. -/
theorem traceTensorDiagonalMap_range :
    (traceTensorDiagonalMap (K := K) M).range =
      diagonalLattice (integralTraceDual
        (NumberFieldInvertibleGeneric.genericImage (K := K) M)) := by
  have he : traceTensorDiagonalMap (K := K) M =
      (latticeDiagonalMap (integralTraceDual
        (NumberFieldInvertibleGeneric.genericImage (K := K) M))).comp
          ((traceTensorEquiv (K := K) M).restrictScalars ℤ).toLinearMap := rfl
  rw [he, ((traceTensorEquiv (K := K) M).restrictScalars ℤ).range_comp]
  rfl

/-- The completed ordinary trace isometry evaluates on original module vectors as
the actual original integer functional. -/
theorem traceTensorDiagonalMap_original
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    [hη : η.IsHermitian]
    (z : codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) (m : M) :
    ordinaryTraceDualIsometry (ξ := η) (traceTensorDiagonalMap (K := K) M z)
      (NumberFieldProjectiveGeneric.originalDiagonalMap (K := K) M m) =
        (integerTensorEquiv (K := K) M z m : ℝ) := by
  change ordinaryTraceDualIsometry (ξ := η)
    (vectorDiagonalMap (K := K) (traceTensorInclusion (K := K) M z))
    (vectorDiagonalMap (K := K) (NumberFieldInvertibleGeneric.genericInclusion (K := K) M m)) = _
  rw [ordinaryTraceDualIsometry_original]
  exact_mod_cast (integerTensorEquiv_apply (K := K) M z m).symm

theorem traceTensorDiagonalMap_integral
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    [hη : η.IsHermitian]
    (z : codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) (m : M) :
    ordinaryTraceDualIsometry (ξ := η) (traceTensorDiagonalMap (K := K) M z)
      (NumberFieldProjectiveGeneric.originalDiagonalMap (K := K) M m) ∈
        LinearMap.range (Algebra.linearMap ℤ ℝ) := by
  exact ⟨integerTensorEquiv (K := K) M z m,
    (traceTensorDiagonalMap_original (K := K) M η z m).symm⟩

/-- The ordinary trace isometry maps the original projective tensor diagonal onto
the actual continuous integer dual of the original projective module diagonal. -/
theorem traceTensorDiagonalMap_integralDual_image
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    [hη : η.IsHermitian] :
    letI := NumberFieldArchimedeanEuclidean.euclideanNormedAddCommGroup η
    letI := NumberFieldArchimedeanEuclidean.euclideanNormedSpace η
    letI := NumberFieldArchimedeanEuclidean.euclideanInnerProduct (ξ := η)
    letI := ordinaryTraceDualNormedAddCommGroup η
    letI := ordinaryTraceDualNormedSpace η
    (traceTensorDiagonalMap (K := K) M).range.map
      ((ordinaryTraceDualIsometry (ξ := η)).toLinearEquiv.toLinearMap.restrictScalars ℤ) =
        GeometryOfNumbers.integralDual
          (NumberFieldProjectiveGeneric.originalDiagonalMap (K := K) M).range := by
  let := NumberFieldArchimedeanEuclidean.euclideanNormedAddCommGroup η
  let := NumberFieldArchimedeanEuclidean.euclideanNormedSpace η
  let := NumberFieldArchimedeanEuclidean.euclideanInnerProduct (ξ := η)
  let := ordinaryTraceDualNormedAddCommGroup η
  let := ordinaryTraceDualNormedSpace η
  rw [traceTensorDiagonalMap_range, NumberFieldProjectiveGeneric.originalDiagonalMap_range]
  exact NumberFieldTraceDualCovolume.ordinaryTraceDualIsometry_integralDual_image _
    (NumberFieldProjectiveGeneric.genericImage_fg (K := K) M)
    (NumberFieldInvertibleGeneric.genericImage_fullSpan (K := K) M)

/-- Reciprocal ordinary covolume for the literal original tensor diagonal. The dual
completed metric here is the independently defined ordinary trace-dual metric. -/
theorem traceTensorDiagonalMap_covolume
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    [hη : η.IsHermitian] :
    letI := NumberFieldArchimedeanEuclidean.euclideanNormedAddCommGroup η
    letI := NumberFieldArchimedeanEuclidean.euclideanNormedSpace η
    letI := ordinaryTraceDualNormedAddCommGroup η
    letI := ordinaryTraceDualNormedSpace η
    letI := NumberFieldTraceDualCovolume.ordinaryTraceDualInnerProduct (ξ := η)
    letI : MeasurableSpace
      (CompletedVectorProduct K (Module.Dual K (K ⊗[𝓞 K] M))) := borel _
    letI : BorelSpace
      (CompletedVectorProduct K (Module.Dual K (K ⊗[𝓞 K] M))) := ⟨rfl⟩
    letI := measureSpaceOfInnerProductSpace
      (E := CompletedVectorProduct K (Module.Dual K (K ⊗[𝓞 K] M)))
    ZLattice.covolume (traceTensorDiagonalMap (K := K) M).range =
      (NumberFieldArchimedeanCovolume.euclideanCovolume η
        (NumberFieldInvertibleGeneric.genericImage (K := K) M))⁻¹ := by
  let := NumberFieldArchimedeanEuclidean.euclideanNormedAddCommGroup η
  let := NumberFieldArchimedeanEuclidean.euclideanNormedSpace η
  let := ordinaryTraceDualNormedAddCommGroup η
  let := ordinaryTraceDualNormedSpace η
  let := NumberFieldTraceDualCovolume.ordinaryTraceDualInnerProduct (ξ := η)
  let : MeasurableSpace
    (CompletedVectorProduct K (Module.Dual K (K ⊗[𝓞 K] M))) := borel _
  let : BorelSpace
    (CompletedVectorProduct K (Module.Dual K (K ⊗[𝓞 K] M))) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace
    (E := CompletedVectorProduct K (Module.Dual K (K ⊗[𝓞 K] M)))
  rw [traceTensorDiagonalMap_range]
  exact NumberFieldTraceDualCovolume.ordinaryTraceDualCovolume_eq_inv η _
    (NumberFieldProjectiveGeneric.genericImage_fg (K := K) M)
    (NumberFieldInvertibleGeneric.genericImage_fullSpan (K := K) M)

end ArakelovGeometry.NumberFieldProjectiveTraceDual
