/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DirectSum.Basic
public import ArakelovGeometry.AdelicVectorBundle.Measurability.Basic

import ArakelovGeometry.AdelicVectorBundle.Dual.Map
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# The actual non-Archimedean dual of a profile direct sum

The finite-place formula used in Chen–Moriwaki Proposition 4.1.35.
It applies to all completed dual vectors and arbitrary profiles, without
requiring the input vector norms to be ultrametric.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

universe u v w w'
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- Every actual completed functional splits along the completed coordinate projections. -/
theorem dualBaseChange_prod_apply (ω : S.Ω)
    (f : (S.ϕ ω).Completion ⊗[K] Module.Dual K (E × F))
    (z : (S.ϕ ω).Completion ⊗[K] (E × F)) :
    dualBaseChangeEquiv K (S.ϕ ω).Completion (E × F) f z =
      dualBaseChangeEquiv K (S.ϕ ω).Completion E
        ((LinearMap.inl K E F).dualMap.baseChange (S.ϕ ω).Completion f)
        ((LinearMap.fst K E F).baseChange (S.ϕ ω).Completion z) +
      dualBaseChangeEquiv K (S.ϕ ω).Completion F
        ((LinearMap.inr K E F).dualMap.baseChange (S.ϕ ω).Completion f)
        ((LinearMap.snd K E F).baseChange (S.ϕ ω).Completion z) := by
  rw [dualBaseChangeEquiv_dualMap, dualBaseChangeEquiv_dualMap]
  simp only [LinearMap.comp_apply, ← map_add]
  congr 1
  induction z using TensorProduct.inductionOn with
  | tmul a p =>
      simp only [LinearMap.baseChange_tmul, LinearMap.fst_apply, LinearMap.snd_apply,
        LinearMap.inl_apply, LinearMap.inr_apply]
      rw [← TensorProduct.tmul_add]
      simp only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta]
  | add x y hx hy =>
      simp only [map_add]
      conv_lhs => rw [hx, hy]
      abel

namespace NormFamily

variable (ξ : NormFamily S E) (η : NormFamily S F)

/-- At finite places every profile has the same actual completed dual: the coordinate maximum. -/
theorem directSum_dual_norm_eq_max_of_finite (ψ : S.Ω → NormShape)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (f : (S.ϕ ω).Completion ⊗[K] Module.Dual K (E × F)) :
    (ξ.directSum η ψ).dual.norm ω f =
      max (ξ.dual.norm ω ((LinearMap.inl K E F).dualMap.baseChange (S.ϕ ω).Completion f))
        (η.dual.norm ω ((LinearMap.inr K E F).dualMap.baseChange (S.ϕ ω).Completion f)) := by
  let A := ξ.dual.norm ω ((LinearMap.inl K E F).dualMap.baseChange (S.ϕ ω).Completion f)
  let B := η.dual.norm ω ((LinearMap.inr K E F).dualMap.baseChange (S.ϕ ω).Completion f)
  have hAB : 0 ≤ max A B := (ξ.dual.norm_nonneg ω _).trans (le_max_left _ _)
  apply le_antisymm
  · apply (ξ.directSum η ψ).dual_norm_le ω f hAB
    intro z
    rw [dualBaseChange_prod_apply]
    apply (S.norm_add_le_max_of_finite ω hω _ _).trans
    apply max_le
    · exact (ξ.norm_dual_apply_le ω _ _).trans
        (mul_le_mul (le_max_left A B) (ξ.directSum_norm_fst_le η ψ ω z)
          (ξ.norm_nonneg ω _) hAB)
    · exact (η.norm_dual_apply_le ω _ _).trans
        (mul_le_mul (le_max_right A B) (ξ.directSum_norm_snd_le η ψ ω z)
          (η.norm_nonneg ω _) hAB)
  · apply max_le
    · simpa only [directSum_pullback_inl] using
        (ξ.directSum η ψ).pullback_dual_norm_le (LinearMap.inl K E F)
          LinearMap.inl_injective ω f
    · simpa only [directSum_pullback_inr] using
        (ξ.directSum η ψ).pullback_dual_norm_le (LinearMap.inr K E F)
          LinearMap.inr_injective ω f

/-- The exact finite-place formula on rational functionals, as used by measurability. -/
theorem directSum_dual_norm_rational_eq_max_of_finite (ψ : S.Ω → NormShape)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) (ℓ : Module.Dual K (E × F)) :
    (ξ.directSum η ψ).dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ) =
      max (ξ.dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ.comp (LinearMap.inl K E F)))
        (η.dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ.comp (LinearMap.inr K E F))) := by
  have h₁ : (LinearMap.inl K E F).dualMap ℓ = ℓ.comp (LinearMap.inl K E F) := by
    ext x; rfl
  have h₂ : (LinearMap.inr K E F).dualMap ℓ = ℓ.comp (LinearMap.inr K E F) := by
    ext x; rfl
  simpa only [LinearMap.baseChange_tmul, h₁, h₂] using
    ξ.directSum_dual_norm_eq_max_of_finite η ψ ω hω (1 ⊗ₜ[K] ℓ)

/-- On the finite locus the dual sum is measurable without any profile measurability assumption. -/
theorem measurable_directSum_dual_norm_on_finite (ψ : S.Ω → NormShape)
    [hξ : ξ.dual.IsMeasurable] [hη : η.dual.IsMeasurable] (ℓ : Module.Dual K (E × F)) :
    Measurable (fun ω : S.Ωfin ↦
      (ξ.directSum η ψ).dual.norm ω.val ((1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] ℓ)) := by
  have h := ((hξ (ℓ.comp (LinearMap.inl K E F))).max
    (hη (ℓ.comp (LinearMap.inr K E F)))).comp (measurable_subtype_coe (p := fun ω ↦ ω ∈ S.Ωfin))
  convert h using 1
  ext ω
  exact ξ.directSum_dual_norm_rational_eq_max_of_finite η ψ ω.val ω.property ℓ

end NormFamily
end ArakelovGeometry
