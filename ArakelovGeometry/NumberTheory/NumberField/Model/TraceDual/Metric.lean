/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Model.TraceDual.Basic
public import ArakelovGeometry.NumberTheory.NumberField.Model.TraceDual.Projective.Generic
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.NumberTheory.NumberField.Minkowski.PolarVolume
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Topology.Sheaves.Init

/-! # Infinite-place metric compatibility of the actual original trace bidual -/

@[expose] public section

noncomputable section
open NumberField
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldClassicalTraceDualMetric

open AdelicStructure NumberFieldArchimedeanVectorDiagonal NumberFieldArchimedeanEuclidean
  NumberFieldOrdinaryTraceDualNorm NumberFieldProjectiveTraceDual
  NumberFieldProjectiveTraceDualGeneric NumberFieldCodifferentDual NumberFieldProjectiveGeneric
  NumberFieldClassicalTraceDual NumberFieldArithmeticPolarVolume

attribute [local instance] traceTensor_finite traceTensor_projective

private theorem pairing_eq_of_spanning
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (e₁ : Y ≃ₗᵢ[ℝ] StrongDual ℝ X) (e₂ : Z ≃ₗᵢ[ℝ] StrongDual ℝ Y)
    (b : Z →ₗ[ℝ] X) {S : Set Z} {T : Set Y}
    (hS : Submodule.span ℝ S = ⊤) (hT : Submodule.span ℝ T = ⊤)
    (hpair : ∀ t ∈ S, ∀ z ∈ T, e₂ t z = e₁ z (b t)) (t : Z) (z : Y) :
    e₂ t z = e₁ z (b t) := by
  let F : Z →ₗ[ℝ] StrongDual ℝ Y :=
    { toFun := fun t => (NormedSpace.inclusionInDoubleDual ℝ X (b t)).comp
        (e₁ : Y →L[ℝ] StrongDual ℝ X)
      map_add' := by
        intro x₁ x₂
        ext y
        change e₁ y (b (x₁ + x₂)) = e₁ y (b x₁) + e₁ y (b x₂)
        rw [map_add, map_add]
      map_smul' := by
        intro c x
        ext y
        change e₁ y (b (c • x)) = c * e₁ y (b x)
        simp only [map_smul, smul_eq_mul] }
  have he : e₂.toLinearEquiv.toLinearMap = F := by
    apply LinearMap.ext_on hS
    intro t ht
    have hy : (e₂ t).toLinearMap = (F t).toLinearMap :=
      LinearMap.ext_on hT (fun z hz => hpair t ht z hz)
    exact ContinuousLinearMap.ext fun y => LinearMap.congr_fun hy y
  exact congrArg (fun f : Z →ₗ[ℝ] StrongDual ℝ Y => f t z) he

universe u
variable {K : Type u} [Field K] [NumberField K]
  (M : Type u) [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- The prescribed original trace-dual tensor family is Hermitian. -/
theorem originalPrescribedTraceDualFamily_isHermitian
    {η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)}
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    (originalPrescribedTraceDualFamily M hη).IsHermitian
      normalizedNumberFieldArchimedeanCompletions :=
  (prescribedTraceDualFamily_isHermitian hη).pullback
    (traceTensorGenericPairEquiv (K := K) M).toLinearMap
    (traceTensorGenericPairEquiv (K := K) M).injective

/-- The actual original trace tensor is isometric to the native real continuous dual. -/
def originalTraceDualRealIsometry
    {η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)}
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    letI : NormedAddCommGroup (CompletedVectorProduct K (K ⊗[𝓞 K] M)) :=
      euclideanNormedAddCommGroup η
    letI : NormedSpace ℝ (CompletedVectorProduct K (K ⊗[𝓞 K] M)) :=
      euclideanNormedSpace η
    letI : NormedAddCommGroup (CompletedVectorProduct K
        (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M))) :=
      euclideanNormedAddCommGroup (originalPrescribedTraceDualFamily M hη)
    letI : NormedSpace ℝ (CompletedVectorProduct K
        (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M))) :=
      euclideanNormedSpace (originalPrescribedTraceDualFamily M hη)
    CompletedVectorProduct K
      (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)) ≃ₗᵢ[ℝ]
      StrongDual ℝ (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := by
  let : NormedAddCommGroup (CompletedVectorProduct K (K ⊗[𝓞 K] M)) :=
    euclideanNormedAddCommGroup η
  let : NormedSpace ℝ (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := euclideanNormedSpace η
  let : NormedAddCommGroup (CompletedVectorProduct K
      (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M))) :=
    euclideanNormedAddCommGroup (originalPrescribedTraceDualFamily M hη)
  let : NormedSpace ℝ (CompletedVectorProduct K
      (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M))) :=
    euclideanNormedSpace (originalPrescribedTraceDualFamily M hη)
  let : NormedAddCommGroup (CompletedVectorProduct K (Module.Dual K (K ⊗[𝓞 K] M))) :=
    ordinaryTraceDualNormedAddCommGroup η
  let : NormedSpace ℝ (CompletedVectorProduct K (Module.Dual K (K ⊗[𝓞 K] M))) :=
    ordinaryTraceDualNormedSpace η
  let e₁ : CompletedVectorProduct K
      (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)) ≃ₗᵢ[ℝ]
        CompletedVectorProduct K (Module.Dual K (K ⊗[𝓞 K] M)) :=
    originalPrescribedTraceDualIsometry M hη
  let e₂ : CompletedVectorProduct K (Module.Dual K (K ⊗[𝓞 K] M)) ≃ₗᵢ[ℝ]
      StrongDual ℝ (CompletedVectorProduct K (K ⊗[𝓞 K] M)) :=
    ordinaryTraceDualIsometry hη
  exact e₁.trans e₂

/-- The actual original real isometry evaluates integral diagonals by integer trace. -/
theorem originalTraceDualRealIsometry_original
    {η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)}
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (z : codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) (m : M) :
    originalTraceDualRealIsometry M hη
      (originalDiagonalMap (K := K)
        (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) z)
      (originalDiagonalMap (K := K) M m) =
        (integerTensorEquiv (K := K) M z m : ℝ) :=
  originalPrescribedTraceDualIsometry_original M hη z m

/-- Scalar extension of the literal original trace-bidual equivalence. -/
def genericTraceBidualEquiv :
    K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K]
      Module.Dual (𝓞 K) (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)) ≃ₗ[K]
        K ⊗[𝓞 K] M :=
  LinearEquiv.baseChange (𝓞 K) K _ _ (traceBidualEquiv (K := K) M)

/-- Componentwise completed scalar extension of the actual original trace bidual. -/
def traceBidualProductEquiv :
    CompletedVectorProduct K (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K]
      Module.Dual (𝓞 K) (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M))) ≃ₗ[ℝ]
        CompletedVectorProduct K (K ⊗[𝓞 K] M) :=
  LinearEquiv.piCongrRight fun w =>
    (LinearEquiv.baseChange K (CompletedCoefficient w) _ _
      (genericTraceBidualEquiv (K := K) M)).restrictScalars ℝ

/-- The completed trace-bidual map retains the literal original integral diagonal. -/
theorem traceBidualProductEquiv_original
    (t : codifferentModule K ⊗[𝓞 K]
      Module.Dual (𝓞 K) (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)) :
    traceBidualProductEquiv (K := K) M
      (originalDiagonalMap (K := K)
        (codifferentModule K ⊗[𝓞 K]
          Module.Dual (𝓞 K) (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)) t) =
      originalDiagonalMap (K := K) M (traceBidualEquiv (K := K) M t) := by
  ext w
  change (LinearEquiv.baseChange K (CompletedCoefficient w) _ _
    (genericTraceBidualEquiv (K := K) M))
      ((1 : CompletedCoefficient w) ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] t)) = _
  simp only [genericTraceBidualEquiv]
  rfl

/-- Original integral diagonals span the literal completed real product. -/
theorem originalDiagonalMap_span
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)) :
    Submodule.span ℝ ((originalDiagonalMap (K := K) M).range :
      Set (CompletedVectorProduct K (K ⊗[𝓞 K] M))) = ⊤ := by
  let : NormedAddCommGroup (CompletedVectorProduct K (K ⊗[𝓞 K] M)) :=
    euclideanNormedAddCommGroup η
  let : NormedSpace ℝ (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := euclideanNormedSpace η
  let : DiscreteTopology (originalDiagonalMap (K := K) M).range :=
    originalDiagonalMap_range_discrete M η
  let : IsZLattice ℝ (originalDiagonalMap (K := K) M).range :=
    originalDiagonalMap_range_isZLattice M η
  exact (inferInstance : IsZLattice ℝ (originalDiagonalMap (K := K) M).range).span_top

/-- The actual trace-bidual pairing identity extends from original integral diagonals
by their real spanning property; it holds on the entire completed products. -/
theorem traceBidualProductEquiv_pairing
    {η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)}
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (t : CompletedVectorProduct K (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K]
      Module.Dual (𝓞 K) (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M))))
    (z : CompletedVectorProduct K
      (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M))) :
    originalTraceDualRealIsometry
      (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)
      (originalPrescribedTraceDualFamily_isHermitian M hη) t z =
        originalTraceDualRealIsometry M hη z (traceBidualProductEquiv (K := K) M t) := by
  let T := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M
  let TT := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) T
  let η₁ := originalPrescribedTraceDualFamily M hη
  let hη₁ := originalPrescribedTraceDualFamily_isHermitian M hη
  let η₂ := originalPrescribedTraceDualFamily T hη₁
  let X := CompletedVectorProduct K (K ⊗[𝓞 K] M)
  let Y := CompletedVectorProduct K (K ⊗[𝓞 K] T)
  let Z := CompletedVectorProduct K (K ⊗[𝓞 K] TT)
  let : NormedAddCommGroup X := euclideanNormedAddCommGroup η
  let : NormedSpace ℝ X := euclideanNormedSpace η
  let : NormedAddCommGroup Y := euclideanNormedAddCommGroup η₁
  let : NormedSpace ℝ Y := euclideanNormedSpace η₁
  let : NormedAddCommGroup Z := euclideanNormedAddCommGroup η₂
  let : NormedSpace ℝ Z := euclideanNormedSpace η₂
  let : NormedAddCommGroup (StrongDual ℝ X) := inferInstance
  let : NormedSpace ℝ (StrongDual ℝ X) := inferInstance
  let : NormedAddCommGroup (StrongDual ℝ Y) :=
    ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Y) (F := ℝ)
  let : NormedSpace ℝ (StrongDual ℝ Y) :=
    ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Y) (F := ℝ)
  let e₁ : Y ≃ₗᵢ[ℝ] StrongDual ℝ X := originalTraceDualRealIsometry M hη
  let e₂ : Z ≃ₗᵢ[ℝ] StrongDual ℝ Y := originalTraceDualRealIsometry T hη₁
  let b : Z ≃ₗ[ℝ] X := traceBidualProductEquiv (K := K) M
  refine pairing_eq_of_spanning e₁ e₂ b.toLinearMap
    (originalDiagonalMap_span TT η₂) (originalDiagonalMap_span T η₁) ?_ t z
  rintro _ ⟨t, rfl⟩ _ ⟨z, rfl⟩
  change originalTraceDualRealIsometry T hη₁
      (originalDiagonalMap (K := K) TT t) (originalDiagonalMap (K := K) T z) =
    originalTraceDualRealIsometry M hη (originalDiagonalMap (K := K) T z)
      (traceBidualProductEquiv (K := K) M (originalDiagonalMap (K := K) TT t))
  rw [traceBidualProductEquiv_original]
  erw [originalTraceDualRealIsometry_original T hη₁ t z,
    originalTraceDualRealIsometry_original M hη z (traceBidualEquiv (K := K) M t)]
  exact congrArg (fun n : ℤ => (n : ℝ))
    (integerTraceBidualEquiv_pairing (K := K) M t z).symm

/-- The literal original trace-bidual map preserves the completed Euclidean product norm. -/
theorem traceBidualProductEquiv_norm
    {η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)}
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (t : CompletedVectorProduct K (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K]
      Module.Dual (𝓞 K) (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)))) :
    letI : NormedAddCommGroup (CompletedVectorProduct K (K ⊗[𝓞 K] M)) :=
      euclideanNormedAddCommGroup η
    letI : NormedAddCommGroup (CompletedVectorProduct K (K ⊗[𝓞 K]
        (codifferentModule K ⊗[𝓞 K]
          Module.Dual (𝓞 K) (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)))) :=
      euclideanNormedAddCommGroup
        (originalPrescribedTraceDualFamily _ (originalPrescribedTraceDualFamily_isHermitian M hη))
    ‖traceBidualProductEquiv (K := K) M t‖ = ‖t‖ := by
  let T := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M
  let TT := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) T
  let η₁ := originalPrescribedTraceDualFamily M hη
  let hη₁ := originalPrescribedTraceDualFamily_isHermitian M hη
  let η₂ := originalPrescribedTraceDualFamily T hη₁
  let X := CompletedVectorProduct K (K ⊗[𝓞 K] M)
  let Y := CompletedVectorProduct K (K ⊗[𝓞 K] T)
  let Z := CompletedVectorProduct K (K ⊗[𝓞 K] TT)
  let : NormedAddCommGroup X := euclideanNormedAddCommGroup η
  let : NormedSpace ℝ X := euclideanNormedSpace η
  let : NormedAddCommGroup Y := euclideanNormedAddCommGroup η₁
  let : NormedSpace ℝ Y := euclideanNormedSpace η₁
  let : NormedAddCommGroup Z := euclideanNormedAddCommGroup η₂
  let : NormedSpace ℝ Z := euclideanNormedSpace η₂
  let : NormedAddCommGroup (StrongDual ℝ X) := inferInstance
  let : NormedSpace ℝ (StrongDual ℝ X) := inferInstance
  let : NormedAddCommGroup (StrongDual ℝ Y) :=
    ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Y) (F := ℝ)
  let : NormedSpace ℝ (StrongDual ℝ Y) :=
    ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Y) (F := ℝ)
  let e₁ : Y ≃ₗᵢ[ℝ] StrongDual ℝ X := originalTraceDualRealIsometry M hη
  let e₂ : Z ≃ₗᵢ[ℝ] StrongDual ℝ Y := originalTraceDualRealIsometry T hη₁
  let b : Z ≃ₗ[ℝ] X := traceBidualProductEquiv (K := K) M
  have he : e₂ t = (NormedSpace.inclusionInDoubleDual ℝ X (b t)).comp
      (e₁ : Y →L[ℝ] StrongDual ℝ X) :=
    ContinuousLinearMap.ext fun z => traceBidualProductEquiv_pairing M hη t z
  calc
    ‖b t‖ = ‖NormedSpace.inclusionInDoubleDual ℝ X (b t)‖ :=
      ((NormedSpace.inclusionInDoubleDualLi ℝ (E := X)).norm_map (b t)).symm
    _ = ‖(NormedSpace.inclusionInDoubleDual ℝ X (b t)).comp
        (e₁ : Y →L[ℝ] StrongDual ℝ X)‖ :=
      (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ e₁).symm
    _ = ‖e₂ t‖ := congrArg norm he.symm
    _ = ‖t‖ := e₂.norm_map t

/-- Every actual infinite-place norm is preserved by completed scalar extension
of the original integer-ring trace-bidual equivalence. -/
theorem traceBidualProductEquiv_norm_infinite
    {η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)}
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (w : InfinitePlace K)
    (z : CompletedCoefficient w ⊗[K] (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K]
      Module.Dual (𝓞 K) (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)))) :
    (originalPrescribedTraceDualFamily _
      (originalPrescribedTraceDualFamily_isHermitian M hη)).norm
        (normalizedInfinitePlacePoint w) z =
      η.norm (normalizedInfinitePlacePoint w)
        (LinearEquiv.baseChange K (CompletedCoefficient w) _ _
          (genericTraceBidualEquiv (K := K) M) z) := by
  classical
  let η₂ := originalPrescribedTraceDualFamily _
    (originalPrescribedTraceDualFamily_isHermitian M hη)
  let y := LinearEquiv.baseChange K (CompletedCoefficient w) _ _
    (genericTraceBidualEquiv (K := K) M) z
  have hs : traceBidualProductEquiv (K := K) M (Pi.single w z) = Pi.single w y := by
    ext v
    simp only [traceBidualProductEquiv, LinearEquiv.piCongrRight_apply,
      LinearEquiv.restrictScalars_apply]
    by_cases hv : v = w
    · subst v
      simp only [Pi.single_eq_same, y]
    · rw [Pi.single_eq_of_ne hv, Pi.single_eq_of_ne hv]
      exact (LinearEquiv.baseChange K (CompletedCoefficient v) _ _
        (genericTraceBidualEquiv (K := K) M)).map_zero
  have h := congrArg (fun r : ℝ => r ^ 2)
    (traceBidualProductEquiv_norm M hη (Pi.single w z))
  rw [hs] at h
  erw [euclidean_norm_sq η, euclidean_norm_sq η₂] at h
  have h₁ : (∑ v, η.norm (normalizedInfinitePlacePoint v)
      ((Pi.single w y : CompletedVectorProduct K (K ⊗[𝓞 K] M)) v) ^ 2) =
      η.norm (normalizedInfinitePlacePoint w) y ^ 2 := by
    rw [Finset.sum_eq_single w]
    · erw [Pi.single_eq_same]
    · intro v _ hv
      erw [Pi.single_eq_of_ne hv]
      simp
    · simp
  have h₂ : (∑ v, η₂.norm (normalizedInfinitePlacePoint v)
      ((Pi.single w z : CompletedVectorProduct K
        (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K]
          Module.Dual (𝓞 K) (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)))) v) ^ 2) =
      η₂.norm (normalizedInfinitePlacePoint w) z ^ 2 := by
    rw [Finset.sum_eq_single w]
    · erw [Pi.single_eq_same]
    · intro v _ hv
      erw [Pi.single_eq_of_ne hv, η₂.norm_zero]
      norm_num
    · simp
  have he : η.norm (normalizedInfinitePlacePoint w) y ^ 2 =
      η₂.norm (normalizedInfinitePlacePoint w) z ^ 2 := h₁.symm.trans (h.trans h₂)
  exact (sq_eq_sq₀ (η₂.norm_nonneg _ _) (η.norm_nonneg _ _)).mp he.symm

/-- The trace-bidual equivalence preserves every original integral-vector norm,
so it preserves the actual effective-section inequalities. -/
theorem traceBidual_norm_original
    {η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)}
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (w : InfinitePlace K)
    (t : codifferentModule K ⊗[𝓞 K]
      Module.Dual (𝓞 K) (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)) :
    (originalPrescribedTraceDualFamily _
      (originalPrescribedTraceDualFamily_isHermitian M hη)).norm
        (normalizedInfinitePlacePoint w)
        ((1 : CompletedCoefficient w) ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] t)) =
      η.norm (normalizedInfinitePlacePoint w)
        ((1 : CompletedCoefficient w) ⊗ₜ[K]
          ((1 : K) ⊗ₜ[𝓞 K] traceBidualEquiv (K := K) M t)) := by
  have h := traceBidualProductEquiv_norm_infinite M hη w
    ((1 : CompletedCoefficient w) ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] t))
  have hmap := congrArg (fun f => f w)
    (traceBidualProductEquiv_original (K := K) M t)
  exact h.trans (congrArg (η.norm (normalizedInfinitePlacePoint w)) hmap)

end ArakelovGeometry.NumberFieldClassicalTraceDualMetric
