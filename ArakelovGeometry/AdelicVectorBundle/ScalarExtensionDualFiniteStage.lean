/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDualPure
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionFiniteStage
import ArakelovGeometry.AdelicVectorBundle.DualMap

/-!
# Actual scalar dual norms and finite stages

Canonical completed functional extension and the actual dual cancellation map
preserve dual norms, supplying rational finite-stage measurability descent.
-/

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

universe u v w wE

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E)

private theorem dual_norm_eq_of_pointwise (η θ : NormFamily S E)
    (ω : S.Ω) (hn : ∀ t, η.norm ω t = θ.norm ω t)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K E) :
    η.dual.norm ω z = θ.dual.norm ω z := by
  rw [dual_norm_eq_sSup, dual_norm_eq_sSup]
  apply congrArg sSup
  apply congrArg Set.range
  funext t
  exact congrArg (fun a : ℝ => ‖dualBaseChangeEquiv K (S.ϕ ω).Completion E z t‖ / a)
    (hn t)

/-- Ordinary mixed extension preserves every actual completed base functional's norm. -/
theorem scalarExtension_dual_norm_completed_one_tmul
    (x : S.ParameterSpaceExtension L)
    (y : (S.ϕ x.base).Completion ⊗[K] Module.Dual K E) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    (ξ.scalarExtension (L := L)).dual.norm x
      ((dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion
        ((completedScalarExtensionEquiv (Module.Dual K E) (S.ϕ x.base) x.abv
          x.restrict_eq).symm ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] y))) =
      ξ.dual.norm x.base y := by
  intro aVW
  let := aVW
  let z := (completedScalarExtensionEquiv (Module.Dual K E) (S.ϕ x.base) x.abv
    x.restrict_eq).symm ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] y)
  by_cases hx : x.base ∈ S.Ωfin
  · have he : (ξ.scalarExtension (L := L)).dual.norm x
          ((dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion z) =
        (ξ.injectiveScalarExtension (L := L)).dual.norm x
          ((dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion z) := by
      exact dual_norm_eq_of_pointwise (ξ.scalarExtension (L := L))
        (ξ.injectiveScalarExtension (L := L)) x
        (fun t => ξ.scalarExtension_norm_of_mem_Ωfin x hx t) _
    exact he.trans (ξ.injectiveScalarExtension_dual_norm_completed_one_tmul x y)
  · have he : (ξ.scalarExtension (L := L)).dual.norm x
          ((dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion z) =
        (ξ.projectiveScalarExtension (L := L)).dual.norm x
          ((dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion z) := by
      exact dual_norm_eq_of_pointwise (ξ.scalarExtension (L := L))
        (ξ.projectiveScalarExtension (L := L)) x
        (fun t => ξ.scalarExtension_norm_of_not_mem_Ωfin x hx t) _
    exact he.trans (ξ.projectiveScalarExtension_dual_norm_completed_one_tmul x y)

/-- The actual rational extended functional has its original completed dual norm. -/
theorem scalarExtension_dual_norm_rational_one_tmul
    (x : S.ParameterSpaceExtension L) (ℓ : Module.Dual K E) :
    (ξ.scalarExtension (L := L)).dual.norm x
      ((1 : x.abv.Completion) ⊗ₜ[L] dualBaseChangeEquiv K L E ((1 : L) ⊗ₜ[K] ℓ)) =
      ξ.dual.norm x.base ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] ℓ) := by
  have h := ξ.scalarExtension_dual_norm_completed_one_tmul x
    ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] ℓ)
  simp only [completedScalarExtensionEquiv_symm_tmul, map_one, mul_one,
    LinearMap.baseChange_tmul, LinearEquiv.coe_coe] at h
  convert h using 1
  rfl

section Tower

variable {F : Type*} [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
  [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L]

/-- The actual dual cancellation equivalence preserves every completed dual norm in a tower. -/
theorem scalarExtension_dual_trans
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
    (z : x.abv.Completion ⊗[L] Module.Dual L (L ⊗[K] E)) :
    let d := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    ((ξ.scalarExtension (L := F)).scalarExtension (L := L)).dual.norm x
      (d.dualMap.toLinearMap.baseChange x.abv.Completion z) =
      (ξ.scalarExtension (L := L)).dual.norm (scalarExtensionTowerPlace x) z := by
  intro d
  let η := (ξ.scalarExtension (L := F)).scalarExtension (L := L)
  let θ := ξ.scalarExtension (L := L)
  have hm (t : x.abv.Completion ⊗[L] (L ⊗[F] (F ⊗[K] E))) :
      η.norm x t = θ.norm (scalarExtensionTowerPlace x)
        (d.toLinearMap.baseChange x.abv.Completion t) :=
    ξ.scalarExtension_trans (L := F) (M := L) x t
  change η.dual.norm x (d.toLinearMap.dualMap.baseChange x.abv.Completion z) =
    θ.dual.norm (scalarExtensionTowerPlace x) z
  apply le_antisymm
  · apply η.dual_norm_le x _ (θ.dual.norm_nonneg (scalarExtensionTowerPlace x) z)
    intro t
    change x.abv.Completion ⊗[L] (L ⊗[F] (F ⊗[K] E)) at t
    change ‖dualBaseChangeEquiv L x.abv.Completion (L ⊗[F] (F ⊗[K] E))
        (d.toLinearMap.dualMap.baseChange x.abv.Completion z) t‖ ≤
      θ.dual.norm (scalarExtensionTowerPlace x) z * η.norm x t
    rw [dualBaseChangeEquiv_dualMap, LinearMap.comp_apply]
    rw [hm]
    exact θ.norm_dual_apply_le (scalarExtensionTowerPlace x) z _
  · apply θ.dual_norm_le (scalarExtensionTowerPlace x) z (η.dual.norm_nonneg x _)
    intro y
    obtain ⟨t, rfl⟩ := (d.baseChange L x.abv.Completion _ _).surjective y
    change ‖dualBaseChangeEquiv L x.abv.Completion (L ⊗[K] E) z
        (d.toLinearMap.baseChange x.abv.Completion t)‖ ≤
      η.dual.norm x (d.toLinearMap.dualMap.baseChange x.abv.Completion z) *
        θ.norm (scalarExtensionTowerPlace x) (d.toLinearMap.baseChange x.abv.Completion t)
    have h := η.norm_dual_apply_le x
      (d.toLinearMap.dualMap.baseChange x.abv.Completion z) t
    change ‖dualBaseChangeEquiv L x.abv.Completion (L ⊗[F] (F ⊗[K] E))
        (d.toLinearMap.dualMap.baseChange x.abv.Completion z) t‖ ≤
      η.dual.norm x (d.toLinearMap.dualMap.baseChange x.abv.Completion z) * η.norm x t at h
    rw [dualBaseChangeEquiv_dualMap, LinearMap.comp_apply, hm] at h
    exact h

end Tower

end ArakelovGeometry.NormFamily

end
