/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Model.TraceDual.Projective.Generic

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import Mathlib.Topology.Sheaves.Init

/-! # Reciprocal covolume of the original projective trace tensor in its prescribed metric -/

@[expose] public section

noncomputable section
open NumberField MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldProjectiveTraceDualOriginalCovolume

open AdelicStructure NumberFieldCodifferentDual NumberFieldTraceDualizingLine
  NumberFieldProjectiveTraceDual NumberFieldProjectiveTraceDualGeneric
  NumberFieldArchimedeanVectorDiagonal NumberFieldArchimedeanEuclidean
  NumberFieldOrdinaryTraceDualNorm NumberFieldTraceDualCovolume
attribute [local instance 2000] Algebra.toModule Algebra.toSMul

universe u

variable {K : Type u} [Field K] [NumberField K]
  (M : Type u) [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- The trace-dual generic fibre is finite-dimensional over the number field. -/
local instance originalGenericFiniteDimensional :
    FiniteDimensional K
      (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)) :=
  (traceTensorGenericPairEquiv (K := K) M).symm.finiteDimensional

private theorem comap_of_map_equiv
    {V W : Type*} [AddCommGroup V] [Module ℤ V] [AddCommGroup W] [Module ℤ W]
    (e : V ≃ₗ[ℤ] W) (L : Submodule ℤ V) (D : Submodule ℤ W)
    (h : L.map e.toLinearMap = D) : D.comap e.toLinearMap = L := by
  exact (congrArg (Submodule.comap e.toLinearMap) h.symm).trans
    (Submodule.comap_map_eq_of_injective e.injective L)

private theorem covolume_isometry
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
    (e : V ≃ₗᵢ[ℝ] W) (L : Submodule ℤ V) (D : Submodule ℤ W)
    [DiscreteTopology D] [IsZLattice ℝ D]
    (h : L.map (e.toLinearEquiv.toLinearMap.restrictScalars ℤ) = D) :
    letI := measureSpaceOfInnerProductSpace (E := V)
    letI := measureSpaceOfInnerProductSpace (E := W)
    ZLattice.covolume L volume = ZLattice.covolume D volume := by
  let := measureSpaceOfInnerProductSpace (E := V)
  let := measureSpaceOfInnerProductSpace (E := W)
  have hc : ZLattice.comap ℝ D e.toLinearEquiv.toLinearMap = L :=
    comap_of_map_equiv (e.toLinearEquiv.restrictScalars ℤ) L D h
  have ht := ZLattice.covolume_comap D volume volume
    (e := e.toContinuousLinearEquiv) e.measurePreserving
  exact (congrArg (fun P : Submodule ℤ V => ZLattice.covolume P volume) hc.symm).trans ht

/-- Hermitianity of the actual prescribed source tensor norms, without changing
their scalar actions or finite-place norms. -/
theorem originalPrescribedTraceDualFamily_isHermitian
    {η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)}
    [hη : η.IsHermitian] :
    (originalPrescribedTraceDualFamily M (η := η)).IsHermitian
      := by
  unfold originalPrescribedTraceDualFamily
  apply NormFamily.IsHermitian.pullback
  have hline : (dualizingLine K).toNormFamily.IsHermitian
      := dualizingLine_isHermitian K
  exact NormFamily.orthogonalTensorPair_isHermitian η.dual
    (dualizingLine K).toNormFamily (hξ := hη.dual) (hη := hline)

/-- The actual source diagonal maps onto the previously proved literal original
trace-integral diagonal, under the proved canonical source equivalence. -/
theorem originalTensorDiagonalMap_transport :
    (NumberFieldProjectiveGeneric.originalDiagonalMap (K := K)
        (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)).range.map
      ((originalTraceTensorProductEquiv (K := K) M).toLinearMap.restrictScalars ℤ) =
        (traceTensorDiagonalMap (K := K) M).range := by
  have hcomp :
      ((originalTraceTensorProductEquiv (K := K) M).toLinearMap.restrictScalars ℤ).comp
        (NumberFieldProjectiveGeneric.originalDiagonalMap (K := K)
        (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)) = traceTensorDiagonalMap (K := K) M := by
    apply LinearMap.ext
    intro z
    exact originalTraceTensorProductEquiv_diagonal M z
  exact (LinearMap.range_comp _ _).symm.trans (congrArg LinearMap.range hcomp)

/-- Canonical ordinary Euclidean covolume of the literal original M-sharp diagonal,
using the actual prescribed tensor norm and its compatible inner-product volume. -/
def originalTensorCovolume
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    [hη : η.IsHermitian] : ℝ := by
  let := euclideanNormedAddCommGroup (originalPrescribedTraceDualFamily M (η := η))
  let := euclideanNormedSpace (originalPrescribedTraceDualFamily M (η := η))
  let := euclideanInnerProduct (hξ := (originalPrescribedTraceDualFamily_isHermitian M (η := η)))
  let : MeasurableSpace (CompletedVectorProduct K
      (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M))) := borel _
  let : BorelSpace (CompletedVectorProduct K
      (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M))) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K
    (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)))
  exact ZLattice.covolume
    (E := CompletedVectorProduct K
      (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)))
    (NumberFieldProjectiveGeneric.originalDiagonalMap (K := K)
      (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)).range volume

private theorem traceTensorLattice_properties
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    [hη : η.IsHermitian] :
    letI := euclideanNormedAddCommGroup η
    letI := euclideanNormedSpace η
    letI := ordinaryTraceDualNormedAddCommGroup η
    letI := ordinaryTraceDualNormedSpace η
    let L : Submodule ℤ (CompletedVectorProduct K (Module.Dual K (K ⊗[𝓞 K] M))) :=
      (traceTensorDiagonalMap (K := K) M).range
    DiscreteTopology L ∧
      Submodule.span ℝ (L : Set (CompletedVectorProduct K (Module.Dual K (K ⊗[𝓞 K] M)))) = ⊤ := by
  let := euclideanNormedAddCommGroup η
  let := euclideanNormedSpace η
  let := euclideanInnerProduct (hξ := hη)
  let := ordinaryTraceDualNormedAddCommGroup η
  let := ordinaryTraceDualNormedSpace η
  let := ordinaryTraceDualInnerProduct (hξ := hη)
  let := GeometryOfNumbers.strongDualInnerProduct
    (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
  let := euclidean_discrete_diagonalLattice η
    (NumberFieldInvertibleGeneric.genericImage (K := K) M)
    (NumberFieldProjectiveGeneric.genericImage_fg (K := K) M)
    (NumberFieldInvertibleGeneric.genericImage_fullSpan (K := K) M)
  let := euclidean_isZLattice_diagonalLattice η
    (NumberFieldInvertibleGeneric.genericImage (K := K) M)
    (NumberFieldProjectiveGeneric.genericImage_fg (K := K) M)
    (NumberFieldInvertibleGeneric.genericImage_fullSpan (K := K) M)
  let := GeometryOfNumbers.integralDual_discrete
    (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
    (diagonalLattice (K := K) (E := K ⊗[𝓞 K] M)
      (NumberFieldInvertibleGeneric.genericImage (K := K) M))
  let := GeometryOfNumbers.integralDual_isZLattice
    (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
    (diagonalLattice (K := K) (E := K ⊗[𝓞 K] M)
      (NumberFieldInvertibleGeneric.genericImage (K := K) M))
  let t := ordinaryTraceDualIsometry (hξ := hη)
  have hmapt := traceTensorDiagonalMap_integralDual_image M η (hη := hη)
  rw [NumberFieldProjectiveGeneric.originalDiagonalMap_range] at hmapt
  have hcomapt : ZLattice.comap ℝ
      (GeometryOfNumbers.integralDual
        (diagonalLattice (K := K) (E := K ⊗[𝓞 K] M)
      (NumberFieldInvertibleGeneric.genericImage (K := K) M)))
      t.toLinearEquiv.toLinearMap = (traceTensorDiagonalMap (K := K) M).range := by
    change (GeometryOfNumbers.integralDual
      (diagonalLattice (K := K) (E := K ⊗[𝓞 K] M)
      (NumberFieldInvertibleGeneric.genericImage (K := K) M))).comap
        (t.toLinearEquiv.toLinearMap.restrictScalars ℤ) = _
    exact comap_of_map_equiv (t.toLinearEquiv.restrictScalars ℤ)
      (traceTensorDiagonalMap (K := K) M).range _ hmapt
  let L : Submodule ℤ (CompletedVectorProduct K (Module.Dual K (K ⊗[𝓞 K] M))) :=
    (traceTensorDiagonalMap (K := K) M).range
  let D : Submodule ℤ (StrongDual ℝ (CompletedVectorProduct K (K ⊗[𝓞 K] M))) :=
    GeometryOfNumbers.integralDual
      (diagonalLattice (K := K) (E := K ⊗[𝓞 K] M)
        (NumberFieldInvertibleGeneric.genericImage (K := K) M))
  have hL : ZLattice.comap ℝ D t.toLinearEquiv.toLinearMap = L := hcomapt
  let hd : DiscreteTopology (ZLattice.comap ℝ D t.toLinearEquiv.toLinearMap) :=
    ZLattice.comap_discreteTopology ℝ D (e := t.toLinearEquiv.toLinearMap)
      t.continuous t.injective
  let hz : IsZLattice ℝ (ZLattice.comap ℝ D t.toLinearEquiv.toLinearMap) := by
    refine ⟨ZLattice.comap_span_top ℝ D
      (IsZLattice.span_top (K := ℝ) (L := D)) ?_⟩
    intro x _
    exact t.surjective x
  let : DiscreteTopology L := hL ▸ hd
  let : IsZLattice ℝ L := by
    refine ⟨?_⟩
    have hs := hz.span_top
    exact (congrArg
      (fun P : Submodule ℤ (CompletedVectorProduct K (Module.Dual K (K ⊗[𝓞 K] M))) =>
        Submodule.span ℝ (P : Set (CompletedVectorProduct K (Module.Dual K (K ⊗[𝓞 K] M)))))
      hL).symm.trans hs
  exact ⟨inferInstance, IsZLattice.span_top (K := ℝ) (L := L)⟩

/-- The literal original projective trace tensor, with its actual prescribed
tensor metric and canonical ordinary Euclidean volume, has reciprocal covolume. -/
theorem originalTensorCovolume_eq_inv
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    [hη : η.IsHermitian] :
    originalTensorCovolume M η =
      (NumberFieldArchimedeanCovolume.euclideanCovolume η
        (NumberFieldInvertibleGeneric.genericImage (K := K) M))⁻¹ := by
  let := euclideanNormedAddCommGroup (originalPrescribedTraceDualFamily M (η := η))
  let := euclideanNormedSpace (originalPrescribedTraceDualFamily M (η := η))
  let := euclideanInnerProduct (hξ := (originalPrescribedTraceDualFamily_isHermitian M (η := η)))
  let : MeasurableSpace (CompletedVectorProduct K
      (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M))) := borel _
  let : BorelSpace (CompletedVectorProduct K
      (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M))) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K
    (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)))
  let := euclideanNormedAddCommGroup η
  let := euclideanNormedSpace η
  let := euclideanInnerProduct (ξ := η)
  let := ordinaryTraceDualNormedAddCommGroup η
  let := ordinaryTraceDualNormedSpace η
  let := ordinaryTraceDualInnerProduct (ξ := η)
  let : MeasurableSpace (CompletedVectorProduct K (Module.Dual K (K ⊗[𝓞 K] M))) := borel _
  let : BorelSpace (CompletedVectorProduct K (Module.Dual K (K ⊗[𝓞 K] M))) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace
    (E := CompletedVectorProduct K (Module.Dual K (K ⊗[𝓞 K] M)))
  let L : Submodule ℤ (CompletedVectorProduct K (Module.Dual K (K ⊗[𝓞 K] M))) :=
    (traceTensorDiagonalMap (K := K) M).range
  have hprops := traceTensorLattice_properties M η
  let : DiscreteTopology L := hprops.1
  let : IsZLattice ℝ L := ⟨hprops.2⟩
  have ht := covolume_isometry (originalPrescribedTraceDualIsometry M (η := η))
    (NumberFieldProjectiveGeneric.originalDiagonalMap (K := K)
      (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)).range L
    (originalTensorDiagonalMap_transport M)
  exact ht.trans (traceTensorDiagonalMap_covolume M η (hη := hη))

end ArakelovGeometry.NumberFieldProjectiveTraceDualOriginalCovolume
