/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic
public import ArakelovGeometry.AdelicCurve.Extension.CompletionEquiv
import ArakelovGeometry.Analysis.ScalarExtension.FieldIsomorphism
import Mathlib.CategoryTheory.Category.Init

/-!
# Completed scalar-extension norms under field isomorphisms

Canonical completed tensor transport preserves every projective, injective,
and ordinary scalar-extension norm at the corresponding actual places.
-/

@[expose] public section

open scoped TensorProduct
namespace ArakelovGeometry
open AdelicStructure.ParameterSpaceExtension
noncomputable section
variable {K L M E : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [AddCommGroup E] [Module K E]
  {S : AdelicStructure K}

/-- The canonical completed tensor equivalence, linear over the original completed field. -/
def completedScalarExtensionEquivOverBase (v : AbsoluteValue K ℝ)
    (w : AbsoluteValue L ℝ) (h : w.under K = v) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq v w h
    w.Completion ⊗[L] (L ⊗[K] E) ≃ₗ[v.Completion]
      w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq v w h
  let : IsScalarTower v.Completion w.Completion w.Completion := IsScalarTower.right
  let : IsScalarTower v.Completion w.Completion (w.Completion ⊗[L] (L ⊗[K] E)) :=
    TensorProduct.isScalarTower_left (R := L) (R' := w.Completion)
      (R'₂ := v.Completion) (M := w.Completion) (N := L ⊗[K] E)
  let : IsScalarTower v.Completion w.Completion
      (w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E)) :=
    TensorProduct.isScalarTower_left (R := v.Completion) (R' := w.Completion)
      (R'₂ := v.Completion) (M := w.Completion) (N := v.Completion ⊗[K] E)
  exact (completedScalarExtensionEquiv E v w h).restrictScalars v.Completion

/-- Canonical vector transport between the actual completed fibres at
corresponding extension places, linear over the original completed field. -/
def completedScalarExtensionAlgEquiv (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    (pullbackAlgEquiv S σ x).abv.Completion ⊗[L] (L ⊗[K] E) ≃ₗ[(S.ϕ x.base).Completion]
      x.abv.Completion ⊗[M] (M ⊗[K] E) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
    (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  exact completedScalarExtensionEquivOverBase (E := E) (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    ≪≫ₗ TensorProduct.congr (algEquivCompletedFields S σ x).toLinearEquiv
      (LinearEquiv.refl (S.ϕ x.base).Completion ((S.ϕ x.base).Completion ⊗[K] E))
    ≪≫ₗ (completedScalarExtensionEquivOverBase (E := E)
      (S.ϕ x.base) x.abv x.restrict_eq).symm

/-- Completed coefficient transport agrees with tensoring the completed-field equivalence. -/
theorem completedScalarExtensionAlgEquiv_flatten (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    ∀ z : (pullbackAlgEquiv S σ x).abv.Completion ⊗[L] (L ⊗[K] E),
    completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq
      (completedScalarExtensionAlgEquiv (E := E) σ x z) =
    TensorProduct.congr (algEquivCompletedFields S σ x).toLinearEquiv
      (LinearEquiv.refl (S.ϕ x.base).Completion ((S.ϕ x.base).Completion ⊗[K] E))
      (completedScalarExtensionEquiv E (S.ϕ x.base)
        (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq z) := by
  intro aL aM z
  let := aL
  let := aM
  change (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq)
    ((completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).symm _) = _
  exact LinearEquiv.apply_symm_apply _ _

/-- Original coefficients and every completed coefficient follow the
literal field-isomorphism formula under the completed vector transport. -/
theorem completedScalarExtensionAlgEquiv_tmul (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M)
    (a : (pullbackAlgEquiv S σ x).abv.Completion) (b : L) (z : E) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    completedScalarExtensionAlgEquiv (E := E) σ x (a ⊗ₜ[L] (b ⊗ₜ[K] z)) =
      algEquivCompletedFields S σ x a ⊗ₜ[M] (σ b ⊗ₜ[K] z) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
    (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  apply (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).injective
  have hL := completedScalarExtensionEquiv_tmul E (S.ϕ x.base)
    (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq a b z
  have hM := completedScalarExtensionEquiv_tmul E (S.ϕ x.base) x.abv x.restrict_eq
    (algEquivCompletedFields S σ x a) (σ b) z
  rw [completedScalarExtensionAlgEquiv_flatten]
  rw [hL, hM]
  simp only [TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  congr 1
  exact (map_mul (algEquivCompletedFields S σ x) _ _).trans
    (congrArg (fun c ↦ c * algEquivCompletedFields S σ x a)
      (algEquivCompletedFields_algebraMap S σ x b))

namespace NormFamily
variable [FiniteDimensional K E] (ξ : NormFamily S E)

omit [FiniteDimensional K E] in
/-- The projective seminorm is preserved on EVERY actual completed vector. -/
theorem projectiveScalarExtensionSeminorm_algEquiv (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    ∀ z : (pullbackAlgEquiv S σ x).abv.Completion ⊗[L] (L ⊗[K] E),
    ξ.projectiveScalarExtensionSeminorm x (completedScalarExtensionAlgEquiv (E := E) σ x z) =
      ξ.projectiveScalarExtensionSeminorm (pullbackAlgEquiv S σ x) z := by
  intro aL aM z
  let := aL
  let := aM
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  change scalarExtensionProjectiveSeminorm
    (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq
      (completedScalarExtensionAlgEquiv (E := E) σ x z)) =
    scalarExtensionProjectiveSeminorm
      (completedScalarExtensionEquiv E (S.ϕ x.base)
        (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq z)
  rw [completedScalarExtensionAlgEquiv_flatten]
  exact scalarExtensionProjectiveSeminorm_algEquiv (algEquivCompletedFields S σ x)
    ((isometry_algEquivCompletedFields S σ x).norm_map_of_map_zero
      (map_zero (algEquivCompletedFields S σ x))) _

/-- The injective seminorm is preserved on EVERY actual completed vector. -/
theorem injectiveScalarExtensionSeminorm_algEquiv (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    ∀ z : (pullbackAlgEquiv S σ x).abv.Completion ⊗[L] (L ⊗[K] E),
    ξ.injectiveScalarExtensionSeminorm x (completedScalarExtensionAlgEquiv (E := E) σ x z) =
      ξ.injectiveScalarExtensionSeminorm (pullbackAlgEquiv S σ x) z := by
  intro aL aM z
  let := aL
  let := aM
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  change scalarExtensionInjectiveSeminorm
    (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq
      (completedScalarExtensionAlgEquiv (E := E) σ x z)) =
    scalarExtensionInjectiveSeminorm
      (completedScalarExtensionEquiv E (S.ϕ x.base)
        (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq z)
  rw [completedScalarExtensionAlgEquiv_flatten]
  exact scalarExtensionInjectiveSeminorm_algEquiv (algEquivCompletedFields S σ x)
    ((isometry_algEquivCompletedFields S σ x).norm_map_of_map_zero
      (map_zero (algEquivCompletedFields S σ x))) _

variable [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K M]

/-- The ordinary scalar-extension family is preserved on EVERY actual
completed vector, with the actual non-Archimedean branch unchanged. -/
theorem scalarExtension_norm_algEquiv (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    ∀ z : (pullbackAlgEquiv S σ x).abv.Completion ⊗[L] (L ⊗[K] E),
    (ξ.scalarExtension (L := M)).norm x (completedScalarExtensionAlgEquiv (E := E) σ x z) =
      (ξ.scalarExtension (L := L)).norm (pullbackAlgEquiv S σ x) z := by
  classical
  intro aL aM z
  let := aL
  let := aM
  change (if x.base ∈ S.Ωfin then ξ.injectiveScalarExtensionSeminorm x else
      ξ.projectiveScalarExtensionSeminorm x) (completedScalarExtensionAlgEquiv (E := E) σ x z) =
    (if x.base ∈ S.Ωfin then ξ.injectiveScalarExtensionSeminorm (pullbackAlgEquiv S σ x) else
      ξ.projectiveScalarExtensionSeminorm (pullbackAlgEquiv S σ x)) z
  by_cases h : x.base ∈ S.Ωfin
  · rw [ite_eq_left h, ite_eq_left h]
    exact ξ.injectiveScalarExtensionSeminorm_algEquiv σ x z
  · rw [ite_eq_right h, ite_eq_right h]
    exact ξ.projectiveScalarExtensionSeminorm_algEquiv σ x z

end NormFamily

end
end ArakelovGeometry
