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
    (hB : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    (injectiveTensor ξ).IsMeasurable := by
  rcases hB with hB | hB
  · let := hB
    exact (injectiveTensor ξ).isMeasurable_of_discrete
  · exact IsMeasurable.injectiveTensor_of_common_countable_dense_subfield ξ hξ hB

/-- Either source alternative supplies mixed tensor measurability. -/
theorem IsMeasurable.mixedTensor_of_discrete_or_countable
    (ξ : ∀ i, NormFamily S (E i)) (hξ : ∀ i, (ξ i).IsMeasurable)
    (hB : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    (mixedTensor ξ).IsMeasurable := by
  rcases hB with hB | hB
  · let := hB
    exact (mixedTensor ξ).isMeasurable_of_discrete
  · exact IsMeasurable.mixedTensor_of_common_countable_dense_subfield ξ hξ hB

/-- Either source alternative supplies actual orthogonal tensor measurability. -/
theorem IsMeasurable.orthogonalTensor_of_discrete_or_countable
    (ξ : ∀ i, NormFamily S (E i))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : ∀ i, (ξ i).IsHermitian hN) (hξ : ∀ i, (ξ i).IsMeasurable)
    (hB : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    (orthogonalTensor ξ hN hH).IsMeasurable := by
  rcases hB with hB | hB
  · let := hB
    exact (orthogonalTensor ξ hN hH).isMeasurable_of_discrete
  · exact IsMeasurable.orthogonalTensor_of_common_countable_dense_subfield ξ hN hH hξ hB

end NormFamily

namespace AdelicVectorBundle

/-- The canonical injective tensor bundle with both measurability clauses proved. -/
def injectiveTensorOfMeasurableBase (V : ∀ i, AdelicVectorBundle S (E i))
    (hB : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    AdelicVectorBundle S (⨂[K] i, E i) :=
  injectiveTensor V
    (NormFamily.IsMeasurable.injectiveTensor_of_discrete_or_countable _
      (fun i => (V i).isMeasurable) hB)
    (by
      exact (NormFamily.IsMeasurable.injectiveTensor_of_discrete_or_countable _
        (fun i => (V i).isMeasurable) hB).dual_of_discrete_or_countable hB)
    (S.v_Ωinf_lt_top_of_isRCLike hN)

@[simp]
theorem injectiveTensorOfMeasurableBase_toNormFamily (V : ∀ i, AdelicVectorBundle S (E i))
    (hB : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (injectiveTensorOfMeasurableBase V hB hN).toNormFamily =
      NormFamily.injectiveTensor (fun i => (V i).toNormFamily) := rfl

/-- The automatically measurable injective tensor is strongly adelic. -/
theorem injectiveTensorOfMeasurableBase_isStronglyAdelic (V : ∀ i, AdelicVectorBundle S (E i))
    (hB : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (injectiveTensorOfMeasurableBase V hB hN).IsStronglyAdelic :=
  injectiveTensor_isStronglyAdelic V _ _ _

/-- The canonical mixed tensor bundle with both measurability clauses proved. -/
def mixedTensorOfMeasurableBase (V : ∀ i, AdelicVectorBundle S (E i))
    (hB : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    AdelicVectorBundle S (⨂[K] i, E i) :=
  mixedTensor V
    (NormFamily.IsMeasurable.mixedTensor_of_discrete_or_countable _
      (fun i => (V i).isMeasurable) hB)
    (by
      exact (NormFamily.IsMeasurable.mixedTensor_of_discrete_or_countable _
        (fun i => (V i).isMeasurable) hB).dual_of_discrete_or_countable hB)
    (S.v_Ωinf_lt_top_of_isRCLike hN)

@[simp]
theorem mixedTensorOfMeasurableBase_toNormFamily (V : ∀ i, AdelicVectorBundle S (E i))
    (hB : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (mixedTensorOfMeasurableBase V hB hN).toNormFamily =
      NormFamily.mixedTensor (fun i => (V i).toNormFamily) := rfl

/-- The automatically measurable mixed tensor is strongly adelic. -/
theorem mixedTensorOfMeasurableBase_isStronglyAdelic (V : ∀ i, AdelicVectorBundle S (E i))
    (hB : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (mixedTensorOfMeasurableBase V hB hN).IsStronglyAdelic :=
  mixedTensor_isStronglyAdelic V _ _ _

/-- The canonical orthogonal tensor bundle with automatic norm and dual measurability. -/
def orthogonalTensorOfMeasurableBase (V : ∀ i, AdelicVectorBundle S (E i))
    (hB : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : ∀ i, (V i).IsHermitian hN) : AdelicVectorBundle S (⨂[K] i, E i) :=
  orthogonalTensor V hN hH
    (NormFamily.IsMeasurable.orthogonalTensor_of_discrete_or_countable _ hN hH
      (fun i => (V i).isMeasurable) hB)
    (by
      exact (NormFamily.IsMeasurable.orthogonalTensor_of_discrete_or_countable _ hN hH
        (fun i => (V i).isMeasurable) hB).dual_of_discrete_or_countable hB)

@[simp]
theorem orthogonalTensorOfMeasurableBase_toNormFamily (V : ∀ i, AdelicVectorBundle S (E i))
    (hB : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : ∀ i, (V i).IsHermitian hN) :
    (orthogonalTensorOfMeasurableBase V hB hN hH).toNormFamily =
      NormFamily.orthogonalTensor (fun i => (V i).toNormFamily) hN hH := rfl

/-- The automatically measurable orthogonal tensor is strongly adelic. -/
theorem orthogonalTensorOfMeasurableBase_isStronglyAdelic (V : ∀ i, AdelicVectorBundle S (E i))
    (hB : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : ∀ i, (V i).IsHermitian hN) :
    (orthogonalTensorOfMeasurableBase V hB hN hH).IsStronglyAdelic :=
  orthogonalTensor_isStronglyAdelic V _ _ _ _

/-- The automatic orthogonal tensor retains the genuine completed Hermitian norms. -/
theorem orthogonalTensorOfMeasurableBase_isHermitian (V : ∀ i, AdelicVectorBundle S (E i))
    (hB : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : ∀ i, (V i).IsHermitian hN) :
    (orthogonalTensorOfMeasurableBase V hB hN hH).IsHermitian hN :=
  orthogonalTensor_isHermitian V _ _ _ _

/-- The actual determinant degree reverses the injective-to-mixed norm comparison. -/
theorem degree_mixedTensor_le_injectiveTensor [S.IsProper]
    (V : ∀ i, AdelicVectorBundle S (E i))
    (hB : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (mixedTensorOfMeasurableBase V hB hN).degree hB hN ≤
      (injectiveTensorOfMeasurableBase V hB hN).degree hB hN :=
  degree_antitone _ _ hB hN (NormFamily.injectiveTensor_norm_le_mixedTensor_norm _)

/-- Orthogonal tensor determinant degree is bounded above by the injective one. -/
theorem degree_orthogonalTensor_le_injectiveTensor [S.IsProper]
    (V : ∀ i, AdelicVectorBundle S (E i))
    (hB : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : ∀ i, (V i).IsHermitian hN) :
    (orthogonalTensorOfMeasurableBase V hB hN hH).degree hB hN ≤
      (injectiveTensorOfMeasurableBase V hB hN).degree hB hN :=
  degree_antitone _ _ hB hN (fun ω z =>
    (NormFamily.orthogonalTensor_norm_bounds _ hN hH ω z).1)

/-- Orthogonal tensor determinant degree is bounded below by the mixed one. -/
theorem degree_mixedTensor_le_orthogonalTensor [S.IsProper]
    (V : ∀ i, AdelicVectorBundle S (E i))
    (hB : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : ∀ i, (V i).IsHermitian hN) :
    (mixedTensorOfMeasurableBase V hB hN).degree hB hN ≤
      (orthogonalTensorOfMeasurableBase V hB hN hH).degree hB hN := by
  apply degree_antitone _ _ hB hN
  intro ω z
  change (NormFamily.orthogonalTensor _ hN hH).norm ω z ≤
    (NormFamily.mixedTensor _).norm ω z
  by_cases hω : ω ∈ S.Ωfin
  · rw [NormFamily.orthogonalTensor_norm_of_finite _ hN hH ω hω,
      NormFamily.mixedTensor_norm_of_mem_Ωfin _ ω hω]
  · rw [NormFamily.mixedTensor_norm_of_not_mem_Ωfin _ ω hω]
    exact (NormFamily.orthogonalTensor_norm_bounds _ hN hH ω z).2

end AdelicVectorBundle

end ArakelovGeometry
