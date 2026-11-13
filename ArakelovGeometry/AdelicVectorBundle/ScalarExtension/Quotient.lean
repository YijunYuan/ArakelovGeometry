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
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Dual.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Subspace.Basic
import ArakelovGeometry.AdelicVectorBundle.Slope.Quotient
import Mathlib.CategoryTheory.Category.Init
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Actual quotients under non-Archimedean scalar extension

Canonical dual base change, the produced restriction isometry on the actual
dual norm, and ultrametric biduality compare the genuine quotient norms.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry

universe u w wE wF wC

variable {K : Type u} [Field K] {L : Type w} [Field L] [Algebra K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type wF} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- Canonical dual base change commutes with a transpose after a further
actual scalar extension. -/
theorem dualBaseChangeEquiv_dualMap_baseChange
    (π : E →ₗ[K] F) (C : Type wC) [Field C] [Algebra L C]
    (z : C ⊗[L] (L ⊗[K] Module.Dual K F)) :
    ((π.baseChange L).dualMap.baseChange C)
        ((dualBaseChangeEquiv K L F).toLinearMap.baseChange C z) =
      (dualBaseChangeEquiv K L E).toLinearMap.baseChange C
        ((π.dualMap.baseChange L).baseChange C z) := by
  have he : (π.baseChange L).dualMap.comp (dualBaseChangeEquiv K L F).toLinearMap =
      (dualBaseChangeEquiv K L E).toLinearMap.comp (π.dualMap.baseChange L) := by
    apply LinearMap.ext
    intro d
    exact (dualBaseChangeEquiv_dualMap L π d).symm
  simpa only [LinearMap.baseChange_comp, LinearMap.comp_apply] using
    LinearMap.congr_fun (congrArg (fun f => f.baseChange C) he) z

namespace NormFamily

variable {S : AdelicStructure K}

private theorem dual_norm_eq_of_pointwise_eq (η θ : NormFamily S E) (ω : S.Ω)
    (hn : ∀ z, η.norm ω z = θ.norm ω z)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K E) :
    η.dual.norm ω z = θ.dual.norm ω z := by
  rw [η.dual_norm_eq_sSup, θ.dual_norm_eq_sSup]
  simp only [hn]

variable (ξ : NormFamily S E) [Algebra.IsAlgebraic K L]

/-- The genuine quotient of the injective extension and the injective
extension of the genuine quotient have identical completed dual norms. -/
theorem injectiveScalarExtension_pushforward_dual_norm_eq
    (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (x : AdelicStructure.ParameterSpaceExtension S L) (hx : x.base ∈ S.Ωfin)
    (z : x.abv.Completion ⊗[L] Module.Dual L (L ⊗[K] F)) :
    ((ξ.injectiveScalarExtension (L := L)).pushforward (π.baseChange L)
        (LinearMap.baseChange_surjective L hπ)).dual.norm x z =
      ((ξ.pushforward π hπ).injectiveScalarExtension (L := L)).dual.norm x z := by
  have hnon : IsNonarchimedean x.abv := (AdelicStructure.mem_Ωfin_algebraicExtension_iff x).mpr hx
  obtain ⟨d, rfl⟩ := LinearMap.baseChange_surjective x.abv.Completion
    (dualBaseChangeEquiv K L F).surjective z
  erw [(ξ.injectiveScalarExtension (L := L)).pushforward_dual_norm_eq,
    dualBaseChangeEquiv_dualMap_baseChange,
    ← ξ.injectiveScalarExtension_dual x hnon,
    ← (ξ.pushforward π hπ).injectiveScalarExtension_dual x hnon]
  have he := ξ.dual.injectiveScalarExtensionSeminorm_pullback_eq
    (hξ := ξ.dual_isUltrametric) π.dualMap (LinearMap.dualMap_injective_of_surjective hπ)
    x hx d
  change (ξ.dual.injectiveScalarExtension (L := L)).norm x
      ((π.dualMap.baseChange L).baseChange x.abv.Completion d) =
    ((ξ.pushforward π hπ).dual.injectiveScalarExtension (L := L)).norm x d
  rw [ξ.pushforward_dual π hπ]
  exact he

attribute [local irreducible] injectiveScalarExtension pushforward dual in
/-- Injective extension commutes with actual quotient norms on every
completed vector at a non-Archimedean place; original ultrametricity is
unnecessary because both extended quotient norms are ultrametric. -/
theorem injectiveScalarExtension_pushforward_norm_eq
    (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (x : AdelicStructure.ParameterSpaceExtension S L) (hx : x.base ∈ S.Ωfin)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] F)) :
    ((ξ.injectiveScalarExtension (L := L)).pushforward (π.baseChange L)
        (LinearMap.baseChange_surjective L hπ)).norm x z =
      ((ξ.pushforward π hπ).injectiveScalarExtension (L := L)).norm x z := by
  let η := (ξ.injectiveScalarExtension (L := L)).pushforward (π.baseChange L)
    (LinearMap.baseChange_surjective L hπ)
  let θ := (ξ.pushforward π hπ).injectiveScalarExtension (L := L)
  have hx' : x ∈ (S.algebraicExtension L).Ωfin := (AdelicStructure.mem_Ωfin_algebraicExtension_iff
    x).mpr hx
  have hη : η.IsUltrametric :=
    ξ.injectiveScalarExtension_isUltrametric.pushforward _ _
  have hθ : θ.IsUltrametric := (ξ.pushforward π hπ).injectiveScalarExtension_isUltrametric
  change η.norm x z = θ.norm x z
  rw [← hη.dual_dual_norm_eval x hx' z, ← hθ.dual_dual_norm_eval x hx' z]
  exact dual_norm_eq_of_pointwise_eq η.dual θ.dual x
    (ξ.injectiveScalarExtension_pushforward_dual_norm_eq π hπ x hx) _

omit [FiniteDimensional K F] in
private theorem pushforward_norm_eq_of_pointwise_eq
    (η θ : NormFamily S E) (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (ω : S.Ω) (hn : ∀ z, η.norm ω z = θ.norm ω z)
    (z : (S.ϕ ω).Completion ⊗[K] F) :
    (η.pushforward π hπ).norm ω z = (θ.pushforward π hπ).norm ω z := by
  rw [η.pushforward_norm_eq_sInf, θ.pushforward_norm_eq_sInf]
  simp only [hn]

/-- Ordinary scalar extension commutes with the actual quotient norm
at every finite place, without assuming original ultrametricity. -/
theorem scalarExtension_pushforward_norm_eq_of_mem_Ωfin
    (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (x : AdelicStructure.ParameterSpaceExtension S L) (hx : x.base ∈ S.Ωfin)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] F)) :
    ((ξ.scalarExtension (L := L)).pushforward (π.baseChange L)
        (LinearMap.baseChange_surjective L hπ)).norm x z =
      ((ξ.pushforward π hπ).scalarExtension (L := L)).norm x z := by
  calc
    _ = ((ξ.injectiveScalarExtension (L := L)).pushforward (π.baseChange L)
        (LinearMap.baseChange_surjective L hπ)).norm x z :=
      pushforward_norm_eq_of_pointwise_eq (ξ.scalarExtension (L := L))
        (ξ.injectiveScalarExtension (L := L)) (π.baseChange L)
        (LinearMap.baseChange_surjective L hπ) x
        (fun a => ξ.scalarExtension_norm_of_mem_Ωfin x hx a) z
    _ = ((ξ.pushforward π hπ).injectiveScalarExtension (L := L)).norm x z :=
      ξ.injectiveScalarExtension_pushforward_norm_eq π hπ x hx z
    _ = _ := ((ξ.pushforward π hπ).scalarExtension_norm_of_mem_Ωfin x hx z).symm

omit [FiniteDimensional K F] in
/-- Under the canonical quotient tensor equivalence, the native quotient
by the actual base-changed subspace has the extended original quotient norm
on every completed vector at a finite place. -/
theorem scalarExtension_quotient_norm_eq_of_mem_Ωfin
    (A : Submodule K E) (x : AdelicStructure.ParameterSpaceExtension S L)
    (hx : x.base ∈ S.Ωfin)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] (E ⧸ A))) :
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
  have hi := (η.pushforward (A.mkQ.baseChange L)
    (LinearMap.baseChange_surjective L A.mkQ_surjective)).pushforward_norm_of_injective
    e.toLinearMap e.surjective e.injective x z
  calc
    _ = (η.pushforward (A.mkQ.baseChange L)
        (LinearMap.baseChange_surjective L A.mkQ_surjective)).norm x z := hc.symm.trans hi
    _ = _ := ξ.scalarExtension_pushforward_norm_eq_of_mem_Ωfin A.mkQ A.mkQ_surjective x hx z

end NormFamily

end ArakelovGeometry
