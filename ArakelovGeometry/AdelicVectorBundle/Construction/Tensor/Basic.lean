/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Basic
public import ArakelovGeometry.AdelicVectorBundle.Determinant.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite

import ArakelovGeometry.AdelicVectorBundle.Exterior.Domination
import ArakelovGeometry.AdelicVectorBundle.Tensor.Domination
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Adelic tensor products and determinant lines

The injective and mixed clauses of source Proposition 4.1.32(4), and its
determinant clause (5). Each constructor retains precisely the source's
measurability assumptions; strong domination is proved by actual tensor
and quotient constructions. Orthogonal tensors remain a separate construction.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w wι

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {ι : Type wι} [Fintype ι] {E : ι → Type w}
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)]

/-- The actual injective tensor bundle with the source's two measurability premises. -/
noncomputable def injectiveTensor (V : ∀ i, AdelicVectorBundle S (E i))
    [hm : (NormFamily.injectiveTensor (fun i ↦ (V i).toNormFamily)).IsMeasurable]
    [hdm : (NormFamily.injectiveTensor (fun i ↦ (V i).toNormFamily)).dual.IsMeasurable]
    (hfin : S.v S.Ωinf < ⊤) : AdelicVectorBundle S (⨂[K] i, E i) where
  toNormFamily := NormFamily.injectiveTensor (fun i ↦ (V i).toNormFamily)
  isMeasurable := hm
  dual_isMeasurable := hdm
  isDominated := by
    exact (NormFamily.IsDominated.strong_injectiveTensor _
      (fun i ↦ (V i).isDominated) hfin).isDominated

@[simp]
theorem injectiveTensor_toNormFamily (V : ∀ i, AdelicVectorBundle S (E i))
    [hm : (NormFamily.injectiveTensor (fun i ↦ (V i).toNormFamily)).IsMeasurable]
    [hdm : (NormFamily.injectiveTensor (fun i ↦ (V i).toNormFamily)).dual.IsMeasurable]
    (hfin : S.v S.Ωinf < ⊤) :
    (injectiveTensor V hfin).toNormFamily =
      NormFamily.injectiveTensor (fun i ↦ (V i).toNormFamily) := rfl

theorem injectiveTensor_isStronglyAdelic (V : ∀ i, AdelicVectorBundle S (E i))
    [(NormFamily.injectiveTensor (fun i ↦ (V i).toNormFamily)).IsMeasurable]
    [(NormFamily.injectiveTensor (fun i ↦ (V i).toNormFamily)).dual.IsMeasurable]
    (hfin : S.v S.Ωinf < ⊤) : (injectiveTensor V hfin).IsStronglyAdelic :=
  NormFamily.IsDominated.strong_injectiveTensor _ (fun i ↦ (V i).isDominated) hfin

/-- The actual mixed tensor bundle with the source's two measurability premises. -/
noncomputable def mixedTensor (V : ∀ i, AdelicVectorBundle S (E i))
    [hm : (NormFamily.mixedTensor (fun i ↦ (V i).toNormFamily)).IsMeasurable]
    [hdm : (NormFamily.mixedTensor (fun i ↦ (V i).toNormFamily)).dual.IsMeasurable]
    (hfin : S.v S.Ωinf < ⊤) : AdelicVectorBundle S (⨂[K] i, E i) where
  toNormFamily := NormFamily.mixedTensor (fun i ↦ (V i).toNormFamily)
  isMeasurable := hm
  dual_isMeasurable := hdm
  isDominated := by
    exact (NormFamily.IsDominated.strong_mixedTensor _
      (fun i ↦ (V i).isDominated) hfin).isDominated

@[simp]
theorem mixedTensor_toNormFamily (V : ∀ i, AdelicVectorBundle S (E i))
    [hm : (NormFamily.mixedTensor (fun i ↦ (V i).toNormFamily)).IsMeasurable]
    [hdm : (NormFamily.mixedTensor (fun i ↦ (V i).toNormFamily)).dual.IsMeasurable]
    (hfin : S.v S.Ωinf < ⊤) :
    (mixedTensor V hfin).toNormFamily =
      NormFamily.mixedTensor (fun i ↦ (V i).toNormFamily) := rfl

theorem mixedTensor_isStronglyAdelic (V : ∀ i, AdelicVectorBundle S (E i))
    [(NormFamily.mixedTensor (fun i ↦ (V i).toNormFamily)).IsMeasurable]
    [(NormFamily.mixedTensor (fun i ↦ (V i).toNormFamily)).dual.IsMeasurable]
    (hfin : S.v S.Ωinf < ⊤) : (mixedTensor V hfin).IsStronglyAdelic :=
  NormFamily.IsDominated.strong_mixedTensor _ (fun i ↦ (V i).isDominated) hfin

variable {F : Type w} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- The determinant is an adelic line under exactly the source measurability premise. -/
noncomputable def determinant (V : AdelicVectorBundle S F)
    [hm : V.toNormFamily.determinant.IsMeasurable]
    [hS : S.IsArchimedeanNormalized] :
    AdelicVectorBundle S (⋀[K]^(Module.finrank K F) F) :=
  ofLine V.toNormFamily.determinant NormFamily.determinant_finrank
    (hd := by exact V.isDominated.determinant)

@[simp]
theorem determinant_toNormFamily (V : AdelicVectorBundle S F)
    [hm : V.toNormFamily.determinant.IsMeasurable]
    [hS : S.IsArchimedeanNormalized] :
    (V.determinant).toNormFamily = V.toNormFamily.determinant := rfl

instance determinant_isLine (V : AdelicVectorBundle S F)
    [hm : V.toNormFamily.determinant.IsMeasurable]
    [hS : S.IsArchimedeanNormalized] :
    (V.determinant).IsLine := ⟨NormFamily.determinant_finrank⟩

theorem determinant_isStronglyAdelic (V : AdelicVectorBundle S F)
    [hm : V.toNormFamily.determinant.IsMeasurable]
    [hS : S.IsArchimedeanNormalized] :
    (V.determinant).IsStronglyAdelic := (V.determinant_isLine).isStronglyAdelic

end ArakelovGeometry.AdelicVectorBundle
