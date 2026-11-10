/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Basic
public import ArakelovGeometry.AdelicVectorBundle.ExteriorDomination

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
    (hm : (NormFamily.injectiveTensor (fun i ↦ (V i).toNormFamily)).IsMeasurable)
    (hdm : (NormFamily.injectiveTensor (fun i ↦ (V i).toNormFamily)).dual.IsMeasurable)
    (hfin : S.v S.Ωinf < ⊤) : AdelicVectorBundle S (⨂[K] i, E i) where
  toNormFamily := NormFamily.injectiveTensor (fun i ↦ (V i).toNormFamily)
  isMeasurable := hm
  dual_isMeasurable := hdm
  isDominated := (NormFamily.IsDominated.strong_injectiveTensor _
    (fun i ↦ (V i).isDominated) hfin).isDominated

@[simp]
theorem injectiveTensor_toNormFamily (V : ∀ i, AdelicVectorBundle S (E i))
    (hm : (NormFamily.injectiveTensor (fun i ↦ (V i).toNormFamily)).IsMeasurable)
    (hdm : (NormFamily.injectiveTensor (fun i ↦ (V i).toNormFamily)).dual.IsMeasurable)
    (hfin : S.v S.Ωinf < ⊤) :
    (injectiveTensor V hm hdm hfin).toNormFamily =
      NormFamily.injectiveTensor (fun i ↦ (V i).toNormFamily) := rfl

theorem injectiveTensor_isStronglyAdelic (V : ∀ i, AdelicVectorBundle S (E i))
    (hm : (NormFamily.injectiveTensor (fun i ↦ (V i).toNormFamily)).IsMeasurable)
    (hdm : (NormFamily.injectiveTensor (fun i ↦ (V i).toNormFamily)).dual.IsMeasurable)
    (hfin : S.v S.Ωinf < ⊤) : (injectiveTensor V hm hdm hfin).IsStronglyAdelic :=
  NormFamily.IsDominated.strong_injectiveTensor _ (fun i ↦ (V i).isDominated) hfin

/-- The actual mixed tensor bundle with the source's two measurability premises. -/
noncomputable def mixedTensor (V : ∀ i, AdelicVectorBundle S (E i))
    (hm : (NormFamily.mixedTensor (fun i ↦ (V i).toNormFamily)).IsMeasurable)
    (hdm : (NormFamily.mixedTensor (fun i ↦ (V i).toNormFamily)).dual.IsMeasurable)
    (hfin : S.v S.Ωinf < ⊤) : AdelicVectorBundle S (⨂[K] i, E i) where
  toNormFamily := NormFamily.mixedTensor (fun i ↦ (V i).toNormFamily)
  isMeasurable := hm
  dual_isMeasurable := hdm
  isDominated := (NormFamily.IsDominated.strong_mixedTensor _
    (fun i ↦ (V i).isDominated) hfin).isDominated

@[simp]
theorem mixedTensor_toNormFamily (V : ∀ i, AdelicVectorBundle S (E i))
    (hm : (NormFamily.mixedTensor (fun i ↦ (V i).toNormFamily)).IsMeasurable)
    (hdm : (NormFamily.mixedTensor (fun i ↦ (V i).toNormFamily)).dual.IsMeasurable)
    (hfin : S.v S.Ωinf < ⊤) :
    (mixedTensor V hm hdm hfin).toNormFamily =
      NormFamily.mixedTensor (fun i ↦ (V i).toNormFamily) := rfl

theorem mixedTensor_isStronglyAdelic (V : ∀ i, AdelicVectorBundle S (E i))
    (hm : (NormFamily.mixedTensor (fun i ↦ (V i).toNormFamily)).IsMeasurable)
    (hdm : (NormFamily.mixedTensor (fun i ↦ (V i).toNormFamily)).dual.IsMeasurable)
    (hfin : S.v S.Ωinf < ⊤) : (mixedTensor V hm hdm hfin).IsStronglyAdelic :=
  NormFamily.IsDominated.strong_mixedTensor _ (fun i ↦ (V i).isDominated) hfin

variable {F : Type w} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- The determinant is an adelic line under exactly the source measurability premise. -/
noncomputable def determinant (V : AdelicVectorBundle S F)
    (hm : V.toNormFamily.determinant.IsMeasurable)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    AdelicVectorBundle S (⋀[K]^(Module.finrank K F) F) :=
  ofLine V.toNormFamily.determinant NormFamily.determinant_finrank
    hm (V.isDominated.determinant hS)

@[simp]
theorem determinant_toNormFamily (V : AdelicVectorBundle S F)
    (hm : V.toNormFamily.determinant.IsMeasurable)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.determinant hm hS).toNormFamily = V.toNormFamily.determinant := rfl

theorem determinant_isLine (V : AdelicVectorBundle S F)
    (hm : V.toNormFamily.determinant.IsMeasurable)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.determinant hm hS).IsLine := NormFamily.determinant_finrank

theorem determinant_isStronglyAdelic (V : AdelicVectorBundle S F)
    (hm : V.toNormFamily.determinant.IsMeasurable)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.determinant hm hS).IsStronglyAdelic := (V.determinant_isLine hm hS).isStronglyAdelic

end ArakelovGeometry.AdelicVectorBundle
