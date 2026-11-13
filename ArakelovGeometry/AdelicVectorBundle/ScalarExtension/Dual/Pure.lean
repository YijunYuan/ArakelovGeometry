/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Dual.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Dual.Basic
import ArakelovGeometry.Analysis.ScalarExtension.Dual
import Mathlib.CategoryTheory.Category.Init

/-!
# Norms of completed dual vectors under scalar extension

The canonical extension of an actual completed base functional preserves its
operator norm. This bridges the accepted local dual-norm identities to the
actual completed families, without original vector ultrametricity.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

universe u w wE

variable {K : Type u} [Field K] {S : ArakelovGeometry.AdelicStructure K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Projective extension preserves the norm of each actual completed base functional. -/
theorem projectiveScalarExtension_dual_norm_completed_one_tmul (ξ : NormFamily S E)
    (x : S.ParameterSpaceExtension L)
    (y : (S.ϕ x.base).Completion ⊗[K] Module.Dual K E) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    (ξ.projectiveScalarExtension (L := L)).dual.norm x
      ((dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion
        ((completedScalarExtensionEquiv (Module.Dual K E) (S.ϕ x.base) x.abv
          x.restrict_eq).symm ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] y))) =
      ξ.dual.norm x.base y := by
  intro aVW
  let := aVW
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let z := (completedScalarExtensionEquiv (Module.Dual K E) (S.ϕ x.base) x.abv
    x.restrict_eq).symm ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] y)
  let f := dualBaseChangeEquiv K (S.ϕ x.base).Completion E y
  have he := ξ.projectiveScalarExtension_dual_norm_apply x z
  have ht :
      (dualBaseChangeEquiv K (S.ϕ x.base).Completion E).toLinearMap.baseChange
        x.abv.Completion
        (completedScalarExtensionEquiv (Module.Dual K E) (S.ϕ x.base) x.abv
          x.restrict_eq z) =
      (1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] f := by
    rw [show z = _ from rfl, LinearEquiv.apply_symm_apply, LinearMap.baseChange_tmul]
    rfl
  dsimp only at he
  rw [ht, dualBaseChangeEquiv_one_tmul] at he
  exact he.trans (scalarExtensionProjective_dualNorm (L := x.abv.Completion) f)

/-- Injective extension preserves the norm of each actual completed base functional. -/
theorem injectiveScalarExtension_dual_norm_completed_one_tmul (ξ : NormFamily S E)
    (x : S.ParameterSpaceExtension L)
    (y : (S.ϕ x.base).Completion ⊗[K] Module.Dual K E) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    (ξ.injectiveScalarExtension (L := L)).dual.norm x
      ((dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion
        ((completedScalarExtensionEquiv (Module.Dual K E) (S.ϕ x.base) x.abv
          x.restrict_eq).symm ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] y))) =
      ξ.dual.norm x.base y := by
  intro aVW
  let := aVW
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let z := (completedScalarExtensionEquiv (Module.Dual K E) (S.ϕ x.base) x.abv
    x.restrict_eq).symm ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] y)
  let f := dualBaseChangeEquiv K (S.ϕ x.base).Completion E y
  have he := ξ.injectiveScalarExtension_dual_norm_apply x z
  have ht :
      (dualBaseChangeEquiv K (S.ϕ x.base).Completion E).toLinearMap.baseChange
        x.abv.Completion
        (completedScalarExtensionEquiv (Module.Dual K E) (S.ϕ x.base) x.abv
          x.restrict_eq z) =
      (1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] f := by
    rw [show z = _ from rfl, LinearEquiv.apply_symm_apply, LinearMap.baseChange_tmul]
    rfl
  dsimp only at he
  rw [ht, dualBaseChangeEquiv_one_tmul] at he
  exact he.trans (scalarExtensionInjective_dualNorm (L := x.abv.Completion) f)

end ArakelovGeometry.NormFamily

end
