/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Basic
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis

import ArakelovGeometry.AdelicVectorBundle.Construction.Countable
import ArakelovGeometry.AdelicVectorBundle.Measurability.InjectiveTensor
import ArakelovGeometry.AdelicVectorBundle.Measurability.OrthogonalTensor
import ArakelovGeometry.AdelicVectorBundle.Tensor.Domination
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Automatic adelic tensor bundles

The discrete or common countable-density alternatives in Remark 4.1.34 prove
the norm and dual measurability premises of the canonical tensor constructors.
Usual Archimedean normalization supplies the finite measure needed for domination.
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

/-- Either source alternative supplies injective tensor measurability. -/
theorem IsMeasurable.injectiveTensor_of_discrete_or_countable
    (ξ : ∀ i, NormFamily S (E i)) (hξ : ∀ i, (ξ i).IsMeasurable)
    [hB : S.HasMeasurableBase] :
    (injectiveTensor ξ).IsMeasurable := by
  rcases hB.discrete_or_countable with hB | hB
  · let := hB
    exact (injectiveTensor ξ).isMeasurable_of_discrete
  · exact IsMeasurable.injectiveTensor_of_common_countable_dense_subfield ξ hξ hB

/-- Either source alternative supplies mixed tensor measurability. -/
theorem IsMeasurable.mixedTensor_of_discrete_or_countable
    (ξ : ∀ i, NormFamily S (E i)) (hξ : ∀ i, (ξ i).IsMeasurable)
    [hB : S.HasMeasurableBase] :
    (mixedTensor ξ).IsMeasurable := by
  rcases hB.discrete_or_countable with hB | hB
  · let := hB
    exact (mixedTensor ξ).isMeasurable_of_discrete
  · exact IsMeasurable.mixedTensor_of_common_countable_dense_subfield ξ hξ hB

/-- Either source alternative supplies actual orthogonal tensor measurability. -/
theorem IsMeasurable.orthogonalTensor_of_discrete_or_countable
    (ξ : ∀ i, NormFamily S (E i))
    [hN : S.IsArchimedeanNormalized]
    (hH : ∀ i, (ξ i).IsHermitian) (hξ : ∀ i, (ξ i).IsMeasurable)
    [hB : S.HasMeasurableBase] :
    (orthogonalTensor ξ).IsMeasurable := by
  rcases hB.discrete_or_countable with hB | hB
  · let := hB
    exact (orthogonalTensor ξ).isMeasurable_of_discrete
  · exact IsMeasurable.orthogonalTensor_of_common_countable_dense_subfield ξ hξ hB

instance instIsMeasurableInjectiveTensor (ξ : ∀ i, NormFamily S (E i))
    [∀ i, (ξ i).IsMeasurable] [S.HasMeasurableBase] :
    (injectiveTensor ξ).IsMeasurable :=
  IsMeasurable.injectiveTensor_of_discrete_or_countable ξ inferInstance

instance instIsMeasurableMixedTensor (ξ : ∀ i, NormFamily S (E i))
    [∀ i, (ξ i).IsMeasurable] [S.HasMeasurableBase] :
    (mixedTensor ξ).IsMeasurable :=
  IsMeasurable.mixedTensor_of_discrete_or_countable ξ inferInstance

instance instIsMeasurableOrthogonalTensor (ξ : ∀ i, NormFamily S (E i))
    [∀ i, (ξ i).IsMeasurable] [S.HasMeasurableBase] [S.IsArchimedeanNormalized]
    [∀ i, (ξ i).IsHermitian] :
    (orthogonalTensor ξ).IsMeasurable :=
  IsMeasurable.orthogonalTensor_of_discrete_or_countable ξ inferInstance inferInstance

end NormFamily

namespace AdelicVectorBundle

/-- The canonical injective tensor bundle with both measurability clauses proved. -/
def injectiveTensorOfMeasurableBase (V : ∀ i, AdelicVectorBundle S (E i))
    [hB : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    AdelicVectorBundle S (⨂[K] i, E i) :=
  injectiveTensor V
    (hm := (NormFamily.IsMeasurable.injectiveTensor_of_discrete_or_countable _
      (fun i ↦ (V i).isMeasurable)))
    (hdm := (by
      exact (NormFamily.IsMeasurable.injectiveTensor_of_discrete_or_countable _
        (fun i ↦ (V i).isMeasurable)).dual_of_discrete_or_countable))
    (S.v_Ωinf_lt_top_of_isRCLike)

@[simp]
theorem injectiveTensorOfMeasurableBase_toNormFamily (V : ∀ i, AdelicVectorBundle S (E i))
    [hB : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (injectiveTensorOfMeasurableBase V).toNormFamily =
      NormFamily.injectiveTensor (fun i => (V i).toNormFamily) := rfl

/-- The automatically measurable injective tensor is strongly adelic. -/
instance injectiveTensorOfMeasurableBase_isStronglyAdelic (V : ∀ i, AdelicVectorBundle S (E i))
    [hB : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (injectiveTensorOfMeasurableBase V).IsStronglyAdelic :=
  injectiveTensor_isStronglyAdelic V _

/-- The canonical mixed tensor bundle with both measurability clauses proved. -/
def mixedTensorOfMeasurableBase (V : ∀ i, AdelicVectorBundle S (E i))
    [hB : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    AdelicVectorBundle S (⨂[K] i, E i) :=
  mixedTensor V
    (hm := (NormFamily.IsMeasurable.mixedTensor_of_discrete_or_countable _
      (fun i ↦ (V i).isMeasurable)))
    (hdm := (by
      exact (NormFamily.IsMeasurable.mixedTensor_of_discrete_or_countable _
        (fun i ↦ (V i).isMeasurable)).dual_of_discrete_or_countable))
    (S.v_Ωinf_lt_top_of_isRCLike)

@[simp]
theorem mixedTensorOfMeasurableBase_toNormFamily (V : ∀ i, AdelicVectorBundle S (E i))
    [hB : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (mixedTensorOfMeasurableBase V).toNormFamily =
      NormFamily.mixedTensor (fun i => (V i).toNormFamily) := rfl

/-- The automatically measurable mixed tensor is strongly adelic. -/
instance mixedTensorOfMeasurableBase_isStronglyAdelic (V : ∀ i, AdelicVectorBundle S (E i))
    [hB : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (mixedTensorOfMeasurableBase V).IsStronglyAdelic :=
  mixedTensor_isStronglyAdelic V _

/-- The canonical orthogonal tensor bundle with automatic norm and dual measurability. -/
def orthogonalTensorOfMeasurableBase (V : ∀ i, AdelicVectorBundle S (E i))
    [hB : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hH : ∀ i, (V i).IsHermitian] : AdelicVectorBundle S (⨂[K] i, E i) :=
  orthogonalTensor V
    (hm := (NormFamily.IsMeasurable.orthogonalTensor_of_discrete_or_countable _ hH
      (fun i ↦ (V i).isMeasurable)))
    (hdm := (by
      exact (NormFamily.IsMeasurable.orthogonalTensor_of_discrete_or_countable _ hH
        (fun i ↦ (V i).isMeasurable)).dual_of_discrete_or_countable))

@[simp]
theorem orthogonalTensorOfMeasurableBase_toNormFamily (V : ∀ i, AdelicVectorBundle S (E i))
    [hB : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hH : ∀ i, (V i).IsHermitian] :
    (orthogonalTensorOfMeasurableBase V).toNormFamily =
      NormFamily.orthogonalTensor (fun i ↦ (V i).toNormFamily) := rfl

/-- The automatically measurable orthogonal tensor is strongly adelic. -/
instance orthogonalTensorOfMeasurableBase_isStronglyAdelic (V : ∀ i, AdelicVectorBundle S (E i))
    [hB : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hH : ∀ i, (V i).IsHermitian] :
    (orthogonalTensorOfMeasurableBase V).IsStronglyAdelic :=
  orthogonalTensor_isStronglyAdelic V

/-- The automatic orthogonal tensor retains the genuine completed Hermitian norms. -/
instance orthogonalTensorOfMeasurableBase_isHermitian (V : ∀ i, AdelicVectorBundle S (E i))
    [hB : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hH : ∀ i, (V i).IsHermitian] :
    (orthogonalTensorOfMeasurableBase V).IsHermitian :=
  orthogonalTensor_isHermitian V

/-- The actual determinant degree reverses the injective-to-mixed norm comparison. -/
theorem degree_mixedTensor_le_injectiveTensor [S.IsProper]
    (V : ∀ i, AdelicVectorBundle S (E i))
    [hB : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (mixedTensorOfMeasurableBase V).degree ≤
      (injectiveTensorOfMeasurableBase V).degree :=
  degree_antitone _ _ (NormFamily.injectiveTensor_norm_le_mixedTensor_norm _)

/-- Orthogonal tensor determinant degree is bounded above by the injective one. -/
theorem degree_orthogonalTensor_le_injectiveTensor [S.IsProper]
    (V : ∀ i, AdelicVectorBundle S (E i))
    [hB : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hH : ∀ i, (V i).IsHermitian] :
    (orthogonalTensorOfMeasurableBase V).degree ≤
      (injectiveTensorOfMeasurableBase V).degree :=
  degree_antitone _ _ (fun ω z =>
    (NormFamily.orthogonalTensor_norm_bounds _ ω z).1)

/-- Orthogonal tensor determinant degree is bounded below by the mixed one. -/
theorem degree_mixedTensor_le_orthogonalTensor [S.IsProper]
    (V : ∀ i, AdelicVectorBundle S (E i))
    [hB : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hH : ∀ i, (V i).IsHermitian] :
    (mixedTensorOfMeasurableBase V).degree ≤
      (orthogonalTensorOfMeasurableBase V).degree := by
  apply degree_antitone _ _
  intro ω z
  change (NormFamily.orthogonalTensor _).norm ω z ≤
    (NormFamily.mixedTensor _).norm ω z
  by_cases hω : ω ∈ S.Ωfin
  · rw [NormFamily.orthogonalTensor_norm_of_finite _ ω hω,
      NormFamily.mixedTensor_norm_of_mem_Ωfin _ ω hω]
  · rw [NormFamily.mixedTensor_norm_of_not_mem_Ωfin _ ω hω]
    exact (NormFamily.orthogonalTensor_norm_bounds _ ω z).2

end AdelicVectorBundle

end ArakelovGeometry
