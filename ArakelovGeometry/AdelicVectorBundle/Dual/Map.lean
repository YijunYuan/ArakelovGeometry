/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Dual.Basic
public import ArakelovGeometry.AdelicVectorBundle.Subquotient.Quotient.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Duals of restrictions and quotients

The completed dual scalar-extension equivalence is natural in a rational
linear map. It identifies duals of quotient norms with restrictions of the
dual norm, and bounds the dual of a restricted norm by any extended functional.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

universe u w w'

variable {K : Type u} [Field K] {E : Type w} [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] {F : Type w'} [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]

/-- Dual scalar extension carries precomposition to completed precomposition. -/
theorem dualBaseChangeEquiv_dualMap (L : Type*) [Field L] [Algebra K L]
    (f : F →ₗ[K] E) (z : L ⊗[K] Module.Dual K E) :
    dualBaseChangeEquiv K L F (f.dualMap.baseChange L z) =
      (dualBaseChangeEquiv K L E z).comp (f.baseChange L) := by
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simp [hz, ht, LinearMap.add_comp]
  | tmul a ℓ =>
    apply TensorProduct.AlgebraTensorModule.ext
    intro b x
    simp [LinearMap.dualMap_apply]

namespace NormFamily

variable {S : AdelicStructure K}

/-- Restricting a functional to a subspace cannot increase its dual norm. -/
theorem pullback_dual_norm_le (ξ : NormFamily S E) (f : F →ₗ[K] E)
    (hf : Function.Injective f) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K E) :
    (ξ.pullback f hf).dual.norm ω (f.dualMap.baseChange (S.ϕ ω).Completion z) ≤
      ξ.dual.norm ω z := by
  apply (ξ.pullback f hf).dual_norm_le ω _ (ξ.dual.norm_nonneg ω z)
  intro x
  rw [dualBaseChangeEquiv_dualMap, LinearMap.comp_apply]
  exact ξ.norm_dual_apply_le ω z (f.baseChange (S.ϕ ω).Completion x)

/-- Pullback of a quotient functional preserves its dual norm exactly. -/
theorem pushforward_dual_norm_eq (ξ : NormFamily S E) (π : E →ₗ[K] F)
    (hπ : Function.Surjective π) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K F) :
    (ξ.pushforward π hπ).dual.norm ω z =
      ξ.dual.norm ω (π.dualMap.baseChange (S.ϕ ω).Completion z) := by
  let C := ξ.dual.norm ω (π.dualMap.baseChange (S.ϕ ω).Completion z)
  have hC : 0 ≤ C := ξ.dual.norm_nonneg ω _
  apply le_antisymm
  · apply (ξ.pushforward π hπ).dual_norm_le ω z hC
    intro y
    have hb (x : (S.ϕ ω).Completion ⊗[K] E) :
        ‖dualBaseChangeEquiv K (S.ϕ ω).Completion F z
          (π.baseChange (S.ϕ ω).Completion x)‖ ≤ C * ξ.norm ω x := by
      simpa only [dualBaseChangeEquiv_dualMap, LinearMap.comp_apply] using
        ξ.norm_dual_apply_le ω (π.dualMap.baseChange (S.ϕ ω).Completion z) x
    by_cases hzero : C = 0
    · obtain ⟨x, rfl⟩ := LinearMap.baseChange_surjective (S.ϕ ω).Completion hπ y
      simpa only [hzero, zero_mul] using hb x
    · have hpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hzero)
      have hdiv : ‖dualBaseChangeEquiv K (S.ϕ ω).Completion F z y‖ / C ≤
          ξ.quotientSeminorm π hπ ω y := by
        apply (ξ.le_quotientSeminorm_iff π hπ ω y _).2
        intro x hx
        apply (div_le_iff₀ hpos).2
        simpa only [hx, mul_comm] using hb x
      simpa only [pushforward_norm, mul_comm] using (div_le_iff₀ hpos).1 hdiv
  · apply ξ.dual_norm_le ω _ ((ξ.pushforward π hπ).dual.norm_nonneg ω z)
    intro x
    rw [dualBaseChangeEquiv_dualMap, LinearMap.comp_apply]
    exact ((ξ.pushforward π hπ).norm_dual_apply_le ω z
      (π.baseChange (S.ϕ ω).Completion x)).trans
      (mul_le_mul_of_nonneg_left (ξ.pushforward_norm_le π hπ ω x)
        ((ξ.pushforward π hπ).dual.norm_nonneg ω z))

/-- The dual of a quotient family is the restriction along the transpose. -/
theorem pushforward_dual (ξ : NormFamily S E) (π : E →ₗ[K] F)
    (hπ : Function.Surjective π) :
    (ξ.pushforward π hπ).dual =
      ξ.dual.pullback π.dualMap (LinearMap.dualMap_injective_of_surjective hπ) := by
  ext ω z
  exact ξ.pushforward_dual_norm_eq π hπ ω z

/-- The actual completed transpose preserves the actual dual norm when the
original rational equivalence preserves every completed vector norm. -/
theorem dualEquiv_norm_eq_of_completed_isometry (ξ : NormFamily S E)
    (η : NormFamily S F) (ω : S.Ω) (e : E ≃ₗ[K] F)
    (he : ∀ x, η.norm ω (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = ξ.norm ω x)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K F) :
    ξ.dual.norm ω (e.dualMap.toLinearMap.baseChange (S.ϕ ω).Completion z) =
      η.dual.norm ω z := by
  change ξ.dual.norm ω (e.toLinearMap.dualMap.baseChange (S.ϕ ω).Completion z) =
    η.dual.norm ω z
  apply le_antisymm
  · apply ξ.dual_norm_le ω _ (η.dual.norm_nonneg ω z)
    intro x
    rw [dualBaseChangeEquiv_dualMap, LinearMap.comp_apply]
    simpa only [he] using η.norm_dual_apply_le ω z
      (e.toLinearMap.baseChange (S.ϕ ω).Completion x)
  · apply η.dual_norm_le ω z (ξ.dual.norm_nonneg ω _)
    intro y
    obtain ⟨x, rfl⟩ := (e.baseChange K (S.ϕ ω).Completion E F).surjective y
    change ‖dualBaseChangeEquiv K (S.ϕ ω).Completion F z
      (e.toLinearMap.baseChange (S.ϕ ω).Completion x)‖ ≤
        ξ.dual.norm ω (e.toLinearMap.dualMap.baseChange (S.ϕ ω).Completion z) *
          η.norm ω (e.toLinearMap.baseChange (S.ϕ ω).Completion x)
    simpa only [dualBaseChangeEquiv_dualMap, LinearMap.comp_apply, he] using
      ξ.norm_dual_apply_le ω (e.toLinearMap.dualMap.baseChange
        (S.ϕ ω).Completion z) x


/-- Duality transports an equivalence pullback by the inverse transpose. -/
theorem pullbackEquiv_dual (ξ : NormFamily S E) (e : F ≃ₗ[K] E) :
    (ξ.pullback e.toLinearMap e.injective).dual =
      ξ.dual.pullback e.symm.dualMap.toLinearMap e.symm.dualMap.injective := by
  ext ω z
  let η := ξ.pullback e.toLinearMap e.injective
  have h (x : (S.ϕ ω).Completion ⊗[K] E) :
      η.norm ω (e.symm.toLinearMap.baseChange (S.ϕ ω).Completion x) = ξ.norm ω x := by
    change ξ.norm ω ((e.baseChange K (S.ϕ ω).Completion _ _)
      ((e.baseChange K (S.ϕ ω).Completion _ _).symm x)) = _
    rw [LinearEquiv.apply_symm_apply]
  exact (ξ.dualEquiv_norm_eq_of_completed_isometry η ω e.symm h z).symm

/-- The canonical bidual norm commutes with equivalence pullback. -/
theorem pullbackEquiv_bidual (ξ : NormFamily S E) (e : F ≃ₗ[K] E) :
    (ξ.pullback e.toLinearMap e.injective).dual.dual.pullback
        (Module.Dual.eval K F) (Module.eval_apply_injective K) =
      (ξ.dual.dual.pullback (Module.Dual.eval K E)
        (Module.eval_apply_injective K)).pullback e.toLinearMap e.injective := by
  ext ω x
  let η := ξ.pullback e.toLinearMap e.injective
  have h (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K E) :
      η.dual.norm ω (e.dualMap.toLinearMap.baseChange (S.ϕ ω).Completion z) =
        ξ.dual.norm ω z :=
    η.dualEquiv_norm_eq_of_completed_isometry ξ ω e (fun _ ↦ rfl) z
  have hh := ξ.dual.dualEquiv_norm_eq_of_completed_isometry η.dual ω e.dualMap h
    ((Module.Dual.eval K F).baseChange (S.ϕ ω).Completion x)
  have hc : e.dualMap.dualMap.toLinearMap.comp (Module.Dual.eval K F) =
      (Module.Dual.eval K E).comp e.toLinearMap := by ext y f; rfl
  have hcx := DFunLike.congr_fun (congrArg (fun f ↦ f.baseChange (S.ϕ ω).Completion) hc) x
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at hcx
  rw [hcx] at hh
  exact hh.symm

end NormFamily
end ArakelovGeometry
