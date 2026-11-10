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
noncomputable def tensorLines (V : ∀ i, AdelicVectorBundle S (E i))
    (hV : ∀ i, (V i).IsLine) : AdelicVectorBundle S (⨂[K] i, E i) :=
  ofLine (NormFamily.mixedTensor (fun i ↦ (V i).toNormFamily))
    (by exact NormFamily.tensor_finrank_one hV)
    (by exact NormFamily.IsMeasurable.mixedTensor_of_finrank_one (fun i ↦ (V i).isMeasurable) hV)
    (by exact NormFamily.IsDominated.mixedTensor_of_finrank_one (fun i ↦ (V i).isDominated) hV)

@[simp]
theorem tensorLines_toNormFamily (V : ∀ i, AdelicVectorBundle S (E i))
    (hV : ∀ i, (V i).IsLine) :
    (tensorLines V hV).toNormFamily = NormFamily.mixedTensor (fun i ↦ (V i).toNormFamily) := rfl

/-- The output has rank one, including for the empty tensor family. -/
theorem tensorLines_isLine (V : ∀ i, AdelicVectorBundle S (E i))
    (hV : ∀ i, (V i).IsLine) : (tensorLines V hV).IsLine :=
  NormFamily.tensor_finrank_one hV

/-- The tensor line satisfies the actual strong-domination predicate. -/
theorem tensorLines_isStronglyAdelic (V : ∀ i, AdelicVectorBundle S (E i))
    (hV : ∀ i, (V i).IsLine) : (tensorLines V hV).IsStronglyAdelic :=
  (tensorLines_isLine V hV).isStronglyAdelic

/-- Every tensor line is Hermitian under the usual Archimedean normalization. -/
theorem tensorLines_isHermitian (V : ∀ i, AdelicVectorBundle S (E i))
    (hV : ∀ i, (V i).IsLine)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (tensorLines V hV).IsHermitian hS := (tensorLines_isLine V hV).isHermitian hS

/-- The same bundle carries the actual projective tensor norm. -/
theorem tensorLines_toNormFamily_eq_projectiveTensor
    (V : ∀ i, AdelicVectorBundle S (E i)) (hV : ∀ i, (V i).IsLine) :
    (tensorLines V hV).toNormFamily = NormFamily.projectiveTensor (fun i ↦ (V i).toNormFamily) := by
  rw [tensorLines_toNormFamily,
    NormFamily.projectiveTensor_eq_injectiveTensor_of_finrank_one _ hV,
    NormFamily.mixedTensor_eq_injectiveTensor_of_finrank_one _ hV]

/-- The same bundle carries the actual injective tensor norm. -/
theorem tensorLines_toNormFamily_eq_injectiveTensor
    (V : ∀ i, AdelicVectorBundle S (E i)) (hV : ∀ i, (V i).IsLine) :
    (tensorLines V hV).toNormFamily = NormFamily.injectiveTensor (fun i ↦ (V i).toNormFamily) :=
  NormFamily.mixedTensor_eq_injectiveTensor_of_finrank_one _ hV

end ArakelovGeometry.AdelicVectorBundle
