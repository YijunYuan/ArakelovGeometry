/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Tensor.Line
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Hermitian.InnerProduct

import ArakelovGeometry.AdelicVectorBundle.NormFamily.Line
import ArakelovGeometry.AdelicVectorBundle.Tensor.Line
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Orthogonal tensor products of adelic vector bundles

The actual Hermitian tensor norm supplies the source tensor-bundle construction
under its norm and dual measurability hypotheses. For line factors the norm
agrees with the already measurable mixed tensor norm, so no new measurability
assumptions are needed.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

universe u v w wι

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {ι : Type wι} [Fintype ι]
  {E : ι → Type w} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)]

namespace NormFamily

/-- On a finite family of lines the orthogonal norm equals the actual
injective norm, by the injective/projective sandwich. -/
theorem orthogonalTensor_eq_injectiveTensor_of_finrank_one
    (ξ : ∀ i, NormFamily S (E i))
    [hS : S.IsArchimedeanNormalized]
    [hξ : ∀ i, (ξ i).IsHermitian] (hr : ∀ i, Module.finrank K (E i) = 1) :
    orthogonalTensor ξ = injectiveTensor ξ := by
  apply NormFamily.ext
  intro ω z
  obtain ⟨hlo, hhi⟩ := orthogonalTensor_norm_bounds ξ ω z
  rw [projectiveTensor_eq_injectiveTensor_of_finrank_one ξ hr] at hhi
  exact le_antisymm hhi hlo

/-- The orthogonal and mixed norms coincide on any finite family of lines. -/
theorem orthogonalTensor_eq_mixedTensor_of_finrank_one
    (ξ : ∀ i, NormFamily S (E i))
    [hS : S.IsArchimedeanNormalized]
    [hξ : ∀ i, (ξ i).IsHermitian] (hr : ∀ i, Module.finrank K (E i) = 1) :
    orthogonalTensor ξ = mixedTensor ξ :=
  (orthogonalTensor_eq_injectiveTensor_of_finrank_one ξ hr).trans
    (mixedTensor_eq_injectiveTensor_of_finrank_one ξ hr).symm

/-- Orthogonal tensor measurability for lines follows from the proved mixed
tensor family, without an additional measurability premise. -/
theorem IsMeasurable.orthogonalTensor_of_finrank_one
    {ξ : ∀ i, NormFamily S (E i)} (hm : ∀ i, (ξ i).IsMeasurable)
    [hS : S.IsArchimedeanNormalized]
    (hξ : ∀ i, (ξ i).IsHermitian) (hr : ∀ i, Module.finrank K (E i) = 1) :
    (orthogonalTensor ξ).IsMeasurable := by
  rw [orthogonalTensor_eq_mixedTensor_of_finrank_one ξ hr]
  exact IsMeasurable.mixedTensor_of_finrank_one hm hr

end NormFamily

namespace AdelicVectorBundle

/-- Source Proposition 4.1.32(4): the actual orthogonal tensor bundle, retaining
exactly its two measurability premises and proving its domination. -/
def orthogonalTensor (V : ∀ i, AdelicVectorBundle S (E i))
    [hS : S.IsArchimedeanNormalized]
    [hV : ∀ i, (V i).IsHermitian]
    [hm : (NormFamily.orthogonalTensor (fun i ↦ (V i).toNormFamily)).IsMeasurable]
    [hdm : (NormFamily.orthogonalTensor (fun i ↦ (V i).toNormFamily)).dual.IsMeasurable] :
    AdelicVectorBundle S (⨂[K] i, E i) where
  toNormFamily := NormFamily.orthogonalTensor (fun i ↦ (V i).toNormFamily)
  isMeasurable := hm
  dual_isMeasurable := hdm
  isDominated := (NormFamily.IsDominated.strong_orthogonalTensor _
    (fun i => (V i).isDominated)).isDominated

@[simp]
theorem orthogonalTensor_toNormFamily (V : ∀ i, AdelicVectorBundle S (E i))
    [hS : S.IsArchimedeanNormalized]
    [hV : ∀ i, (V i).IsHermitian]
    [hm : (NormFamily.orthogonalTensor (fun i ↦ (V i).toNormFamily)).IsMeasurable]
    [hdm : (NormFamily.orthogonalTensor (fun i ↦ (V i).toNormFamily)).dual.IsMeasurable] :
    (orthogonalTensor V).toNormFamily =
      NormFamily.orthogonalTensor (fun i ↦ (V i).toNormFamily) := rfl

/-- The constructed orthogonal tensor bundle is strongly adelic. -/
instance orthogonalTensor_isStronglyAdelic (V : ∀ i, AdelicVectorBundle S (E i))
    [hS : S.IsArchimedeanNormalized]
    [hV : ∀ i, (V i).IsHermitian]
    [(NormFamily.orthogonalTensor (fun i ↦ (V i).toNormFamily)).IsMeasurable]
    [(NormFamily.orthogonalTensor (fun i ↦ (V i).toNormFamily)).dual.IsMeasurable] :
    (orthogonalTensor V).IsStronglyAdelic :=
  NormFamily.IsDominated.strong_orthogonalTensor _ (fun i ↦ (V i).isDominated)

/-- The constructed orthogonal tensor bundle preserves the actual Hermitian property. -/
instance orthogonalTensor_isHermitian (V : ∀ i, AdelicVectorBundle S (E i))
    [hS : S.IsArchimedeanNormalized]
    [hV : ∀ i, (V i).IsHermitian]
    [(NormFamily.orthogonalTensor (fun i ↦ (V i).toNormFamily)).IsMeasurable]
    [(NormFamily.orthogonalTensor (fun i ↦ (V i).toNormFamily)).dual.IsMeasurable] :
    (orthogonalTensor V).IsHermitian :=
  NormFamily.orthogonalTensor_isHermitian _

/-- Source Corollary 4.1.33: the actual orthogonal tensor of adelic lines,
with both measurability clauses proved from the factors. -/
def orthogonalTensorLines (V : ∀ i, AdelicVectorBundle S (E i))
    [hV : ∀ i, (V i).IsLine]
    [hS : S.IsArchimedeanNormalized] :
    AdelicVectorBundle S (⨂[K] i, E i) :=
  orthogonalTensor V (hV := (fun i ↦ (hV i).isHermitian))
    (hm := (NormFamily.IsMeasurable.orthogonalTensor_of_finrank_one (fun i ↦ (V i).isMeasurable)
      (fun i ↦ (hV i).isHermitian) (fun i ↦ (hV i).rank_eq_one)))
    (hdm := (by
      exact (NormFamily.IsMeasurable.orthogonalTensor_of_finrank_one (fun i => (V i).isMeasurable)
        (fun i ↦ (hV i).isHermitian) (fun i ↦ (hV i).rank_eq_one)).dual_of_finrank_one
          (NormFamily.tensor_finrank_one (fun i ↦ (hV i).rank_eq_one))))

@[simp]
theorem orthogonalTensorLines_toNormFamily (V : ∀ i, AdelicVectorBundle S (E i))
    [hV : ∀ i, (V i).IsLine]
    [hS : S.IsArchimedeanNormalized] :
    (orthogonalTensorLines V).toNormFamily =
      NormFamily.orthogonalTensor (fun i ↦ (V i).toNormFamily)
        (hξ := (fun i ↦ (hV i).isHermitian)) := rfl

/-- The constructed orthogonal tensor remains a line, including the empty family. -/
instance orthogonalTensorLines_isLine (V : ∀ i, AdelicVectorBundle S (E i))
    [hV : ∀ i, (V i).IsLine]
    [hS : S.IsArchimedeanNormalized] :
    (orthogonalTensorLines V).IsLine :=
  ⟨NormFamily.tensor_finrank_one (fun i ↦ (hV i).rank_eq_one)⟩

/-- Orthogonal tensor lines are strongly adelic by the actual tensor construction. -/
theorem orthogonalTensorLines_isStronglyAdelic (V : ∀ i, AdelicVectorBundle S (E i))
    [hV : ∀ i, (V i).IsLine]
    [hS : S.IsArchimedeanNormalized] :
    (orthogonalTensorLines V).IsStronglyAdelic :=
  (orthogonalTensorLines_isLine V).isStronglyAdelic

/-- Orthogonal tensor lines are Hermitian for the same completed normalization. -/
theorem orthogonalTensorLines_isHermitian (V : ∀ i, AdelicVectorBundle S (E i))
    [hV : ∀ i, (V i).IsLine]
    [hS : S.IsArchimedeanNormalized] :
    (orthogonalTensorLines V).IsHermitian :=
  (orthogonalTensorLines_isLine V).isHermitian

/-- The actual orthogonal and mixed tensor line bundles are equal. -/
theorem orthogonalTensorLines_eq_tensorLines (V : ∀ i, AdelicVectorBundle S (E i))
    [hV : ∀ i, (V i).IsLine]
    [hS : S.IsArchimedeanNormalized] :
    orthogonalTensorLines V = tensorLines V := by
  apply AdelicVectorBundle.ext
  exact NormFamily.orthogonalTensor_eq_mixedTensor_of_finrank_one _ (fun i ↦ (hV i).rank_eq_one)

/-- The established tensor line bundle carries precisely the orthogonal norm. -/
theorem tensorLines_toNormFamily_eq_orthogonalTensor
    (V : ∀ i, AdelicVectorBundle S (E i)) [hV : ∀ i, (V i).IsLine]
    [hS : S.IsArchimedeanNormalized] :
    (tensorLines V).toNormFamily =
      NormFamily.orthogonalTensor (fun i ↦ (V i).toNormFamily)
        (hξ := (fun i ↦ (hV i).isHermitian)) :=
  (NormFamily.orthogonalTensor_eq_mixedTensor_of_finrank_one _ (fun i ↦ (hV i).rank_eq_one)).symm

end AdelicVectorBundle

end ArakelovGeometry
