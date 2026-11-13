/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Dual.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic
public import ArakelovGeometry.AdelicVectorBundle.Subquotient.Quotient.Basic

import ArakelovGeometry.AdelicVectorBundle.Dual.Bidual
import ArakelovGeometry.AdelicVectorBundle.Dual.Map
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Archimedean
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Domination.Descent
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Dual.FiniteStage
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Quotient
import ArakelovGeometry.AdelicVectorBundle.Slope.Quotient
import ArakelovGeometry.Analysis.ScalarExtension.ArchimedeanComplexExtension
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual ordinary quotient norms over a complexified base

Bijective actual Archimedean completed scalar maps extend rational dual norm
identities to the entire dual fibre. Genuine dual restrictions and biduality
then identify the ordinary extension of every actual quotient at all places.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.NormFamily

universe u w wE wF
variable {K : Type u} [Field K] {L : Type w} [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] {S : AdelicStructure K}
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type wF} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- Over a base containing a square root of minus one, the actual ordinary
dual extension identity holds on the whole Archimedean completed dual fibre. -/
theorem scalarExtension_dual_norm_eq_of_sqrt_neg_one (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized]
    (hi : ∃ a : K, a ^ 2 = -1) (x : S.ParameterSpaceExtension L)
    (hx : x.base ∈ S.Ωinf)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] Module.Dual K E)) :
    (ξ.dual.scalarExtension (L := L)).norm x z =
      (ξ.scalarExtension (L := L)).dual.norm x
        ((dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion z) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let : IsRCLikeNormedField (S.ϕ x.base).Completion := hN x.base hx
  have hroot : ∃ a : (S.ϕ x.base).Completion, a ^ 2 = -1 := by
    obtain ⟨a, ha⟩ := hi
    refine ⟨algebraMap K (S.ϕ x.base).Completion a, ?_⟩
    simpa only [map_pow, map_neg, map_one] using
      congrArg (algebraMap K (S.ϕ x.base).Completion) ha
  let e := completedScalarExtensionEquiv (Module.Dual K E)
    (S.ϕ x.base) x.abv x.restrict_eq
  obtain ⟨d, hd⟩ := one_tmul_surjective_of_isRCLikeNormedField_sqrt_neg_one
    hroot ((S.ϕ x.base).Completion ⊗[K] Module.Dual K E) (e z)
  have hz : z = e.symm ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] d) := by
    apply e.injective
    simpa only [e.apply_symm_apply] using hd.symm
  rw [hz]
  calc
    _ = ξ.dual.norm x.base d :=
      (ξ.dual.scalarExtension_norm_completed_one_tmul x d).trans
        (ξ.dual.dual_dual_norm_eval_eq_of_isRCLike x.base (hN x.base hx) d)
    _ = _ := (ξ.scalarExtension_dual_norm_completed_one_tmul x d).symm

/-- At an actual Archimedean place over a complexified base, the quotient of
the ordinary extension and the extension of the quotient have equal dual norms. -/
theorem scalarExtension_pushforward_dual_norm_eq_of_sqrt_neg_one (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized]
    (hi : ∃ a : K, a ^ 2 = -1) (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (x : S.ParameterSpaceExtension L) (hx : x.base ∈ S.Ωinf)
    (z : x.abv.Completion ⊗[L] Module.Dual L (L ⊗[K] F)) :
    ((ξ.scalarExtension (L := L)).pushforward (π.baseChange L)
        (LinearMap.baseChange_surjective L hπ)).dual.norm x z =
      ((ξ.pushforward π hπ).scalarExtension (L := L)).dual.norm x z := by
  obtain ⟨d, rfl⟩ := LinearMap.baseChange_surjective x.abv.Completion
    (dualBaseChangeEquiv K L F).surjective z
  erw [(ξ.scalarExtension (L := L)).pushforward_dual_norm_eq,
    dualBaseChangeEquiv_dualMap_baseChange,
    ← ξ.scalarExtension_dual_norm_eq_of_sqrt_neg_one hi x hx,
    ← (ξ.pushforward π hπ).scalarExtension_dual_norm_eq_of_sqrt_neg_one hi x hx]
  change (ξ.dual.scalarExtension (L := L)).norm x
      ((π.dualMap.baseChange L).baseChange x.abv.Completion d) =
    ((ξ.pushforward π hπ).dual.scalarExtension (L := L)).norm x d
  rw [ξ.pushforward_dual π hπ]
  exact ξ.dual.scalarExtension_pullback_norm_eq_of_sqrt_neg_one
    (hξ := ξ.dual_isUltrametricAtFinitePlaces) hi π.dualMap
      (LinearMap.dualMap_injective_of_surjective hπ) x d

private theorem dual_norm_congr_at_place
    {k : Type*} [Field k] {T : AdelicStructure k}
    {G : Type*} [AddCommGroup G] [Module k G] [FiniteDimensional k G]
    (η θ : NormFamily T G) (ω : T.Ω) (hn : ∀ z, η.norm ω z = θ.norm ω z)
    (z : (T.ϕ ω).Completion ⊗[k] Module.Dual k G) :
    η.dual.norm ω z = θ.dual.norm ω z := by
  rw [η.dual_norm_eq_sSup, θ.dual_norm_eq_sSup]
  simp only [hn]

attribute [local irreducible] scalarExtension pushforward dual in
/-- Ordinary extension commutes with every actual quotient on the whole
completed fibre at every place over a complexified normalized base. -/
theorem scalarExtension_pushforward_norm_eq_of_sqrt_neg_one (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized]
    (hi : ∃ a : K, a ^ 2 = -1) (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (x : S.ParameterSpaceExtension L) (z : x.abv.Completion ⊗[L] (L ⊗[K] F)) :
    ((ξ.scalarExtension (L := L)).pushforward (π.baseChange L)
        (LinearMap.baseChange_surjective L hπ)).norm x z =
      ((ξ.pushforward π hπ).scalarExtension (L := L)).norm x z := by
  by_cases hx : x.base ∈ S.Ωfin
  · exact ξ.scalarExtension_pushforward_norm_eq_of_mem_Ωfin π hπ x hx z
  · have hx' : x ∈ (S.algebraicExtension L).Ωinf :=
      fun hh => hx ((AdelicStructure.mem_Ωfin_algebraicExtension_iff x).mp hh)
    have hNx := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) x hx'
    let η := (ξ.scalarExtension (L := L)).pushforward (π.baseChange L)
      (LinearMap.baseChange_surjective L hπ)
    let θ := (ξ.pushforward π hπ).scalarExtension (L := L)
    change η.norm x z = θ.norm x z
    rw [← η.dual_dual_norm_eval_eq_of_isRCLike x hNx z,
      ← θ.dual_dual_norm_eval_eq_of_isRCLike x hNx z]
    exact dual_norm_congr_at_place η.dual θ.dual x
      (ξ.scalarExtension_pushforward_dual_norm_eq_of_sqrt_neg_one hi π hπ x hx) _

omit [FiniteDimensional K F] in
/-- The native quotient by the actual base-changed subspace has exactly the
extended original quotient norm under the canonical tensor quotient equivalence. -/
theorem scalarExtension_quotient_norm_eq_of_sqrt_neg_one (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized]
    (hi : ∃ a : K, a ^ 2 = -1) (A : Submodule K E)
    (x : S.ParameterSpaceExtension L) (z : x.abv.Completion ⊗[L] (L ⊗[K] (E ⧸ A))) :
    ((ξ.scalarExtension (L := L)).quotient (A.baseChange L)).norm x
        ((TensorProduct.AlgebraTensorModule.tensorQuotientEquiv L K L A).toLinearMap.baseChange
          x.abv.Completion z) =
      ((ξ.quotient A).scalarExtension (L := L)).norm x z := by
  let e : (L ⊗[K] (E ⧸ A)) ≃ₗ[L] ((L ⊗[K] E) ⧸ A.baseChange L) :=
    TensorProduct.AlgebraTensorModule.tensorQuotientEquiv L K L A
  have he : e.toLinearMap.comp (A.mkQ.baseChange L) = (A.baseChange L).mkQ := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a y
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul]
    rfl
  let η := ξ.scalarExtension (L := L)
  have hc := η.pushforward_comp_norm (A.mkQ.baseChange L)
    (LinearMap.baseChange_surjective L A.mkQ_surjective)
    e.toLinearMap e.surjective x (e.toLinearMap.baseChange x.abv.Completion z)
  simp only [he] at hc
  have ht := (η.pushforward (A.mkQ.baseChange L)
    (LinearMap.baseChange_surjective L A.mkQ_surjective)).pushforward_norm_of_injective
    e.toLinearMap e.surjective e.injective x z
  calc
    _ = (η.pushforward (A.mkQ.baseChange L)
        (LinearMap.baseChange_surjective L A.mkQ_surjective)).norm x z := hc.symm.trans ht
    _ = _ := ξ.scalarExtension_pushforward_norm_eq_of_sqrt_neg_one
      hi A.mkQ A.mkQ_surjective x z

end ArakelovGeometry.NormFamily
