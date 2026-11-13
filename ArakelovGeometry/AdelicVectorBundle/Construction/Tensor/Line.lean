/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Basic
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite

import ArakelovGeometry.AdelicVectorBundle.Tensor.Line
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Tensor products of adelic lines

The actual mixed tensor norm of a finite family of adelic lines is measurable
and dominated by its generator formula. Rank-one duality proves the second
measurability condition, so no tensor measurability or domination is assumed.
The empty family is included. Orthogonal tensor identification remains in the
separate general Hermitian tensor construction.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w wι

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {ι : Type wι} [Fintype ι] {E : ι → Type w}
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)]

/-- Finite tensor products of adelic lines, on their actual rational tensor space. -/
noncomputable abbrev tensorLines (V : ι → AdelicVectorBundle S)
    [hV : ∀ i, (V i).IsLine] : AdelicVectorBundle S :=
  ofLine (NormFamily.mixedTensor (fun i ↦ (V i).toNormFamily))
    (by exact NormFamily.tensor_finrank_one (fun i ↦ (hV i).rank_eq_one))
    (hm := by
      exact NormFamily.IsMeasurable.mixedTensor_of_finrank_one
        (fun i ↦ (V i).isMeasurable) (fun i ↦ (hV i).rank_eq_one))
    (hd := by
      exact NormFamily.IsDominated.mixedTensor_of_finrank_one
        (fun i ↦ (V i).isDominated) (fun i ↦ (hV i).rank_eq_one))

@[simp]
theorem tensorLines_toNormFamily (V : ι → AdelicVectorBundle S)
    [hV : ∀ i, (V i).IsLine] :
    (tensorLines V).toNormFamily = NormFamily.mixedTensor (fun i ↦ (V i).toNormFamily) := rfl

/-- The output has rank one, including for the empty tensor family. -/
instance tensorLines_isLine (V : ι → AdelicVectorBundle S)
    [hV : ∀ i, (V i).IsLine] : (tensorLines V).IsLine :=
  ⟨NormFamily.tensor_finrank_one (fun i ↦ (hV i).rank_eq_one)⟩

/-- The tensor line satisfies the actual strong-domination predicate. -/
theorem tensorLines_isStronglyAdelic (V : ι → AdelicVectorBundle S)
    [hV : ∀ i, (V i).IsLine] : (tensorLines V).IsStronglyAdelic :=
  (tensorLines_isLine V).isStronglyAdelic

/-- Every tensor line is Hermitian under the usual Archimedean normalization. -/
theorem tensorLines_isHermitian (V : ι → AdelicVectorBundle S)
    [hV : ∀ i, (V i).IsLine]
    [hS : S.IsArchimedeanNormalized] :
    (tensorLines V).IsHermitian := (tensorLines_isLine V).isHermitian

/-- The same bundle carries the actual projective tensor norm. -/
theorem tensorLines_toNormFamily_eq_projectiveTensor
    (V : ι → AdelicVectorBundle S) [hV : ∀ i, (V i).IsLine] :
    (tensorLines V).toNormFamily = NormFamily.projectiveTensor (fun i ↦ (V i).toNormFamily) := by
  rw [tensorLines_toNormFamily,
    NormFamily.projectiveTensor_eq_injectiveTensor_of_finrank_one _ (fun i ↦ (hV i).rank_eq_one),
    NormFamily.mixedTensor_eq_injectiveTensor_of_finrank_one _ (fun i ↦ (hV i).rank_eq_one)]

/-- The same bundle carries the actual injective tensor norm. -/
theorem tensorLines_toNormFamily_eq_injectiveTensor
    (V : ι → AdelicVectorBundle S) [hV : ∀ i, (V i).IsLine] :
    (tensorLines V).toNormFamily = NormFamily.injectiveTensor (fun i ↦ (V i).toNormFamily) :=
  NormFamily.mixedTensor_eq_injectiveTensor_of_finrank_one _ (fun i ↦ (hV i).rank_eq_one)

end ArakelovGeometry.AdelicVectorBundle
