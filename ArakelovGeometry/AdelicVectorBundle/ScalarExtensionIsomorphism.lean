/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Equiv
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionIdentity

/-!
# Completed fields under algebraic extension isomorphisms

The actual completed field isomorphism fixes the original completed base
field and preserves its norm. Its coefficient formula is the field map.
-/

open UniformSpace
noncomputable section
namespace AbsoluteValue
variable {L M : Type*} [Field L] [Field M]

private def pullbackWithAbsRingEquiv (w : AbsoluteValue M ℝ) (σ : L ≃+* M) :
    WithAbs (w.pullback σ.toRingHom) ≃+* WithAbs w :=
  ((WithAbs.equiv (w.pullback σ.toRingHom)).trans σ).trans (WithAbs.equiv w).symm

private theorem isometry_pullbackWithAbsRingEquiv
    (w : AbsoluteValue M ℝ) (σ : L ≃+* M) :
    Isometry (pullbackWithAbsRingEquiv w σ).toRingHom :=
  AddMonoidHomClass.isometry_of_norm (pullbackWithAbsRingEquiv w σ).toRingHom
    (fun _ ↦ rfl)

private theorem isometry_pullbackWithAbsRingEquiv_symm
    (w : AbsoluteValue M ℝ) (σ : L ≃+* M) :
    Isometry (pullbackWithAbsRingEquiv w σ).symm.toRingHom := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  change w (σ (σ.symm x.ofAbs)) = w x.ofAbs
  rw [σ.apply_symm_apply]

/-- Pullback of the absolute value makes a field isomorphism extend to the
actual completions, with the inverse obtained by completing its inverse. -/
def completionRingEquivOfPullback (w : AbsoluteValue M ℝ) (σ : L ≃+* M) :
    (w.pullback σ.toRingHom).Completion ≃+* w.Completion := by
  let e := pullbackWithAbsRingEquiv w σ
  let h := isometry_pullbackWithAbsRingEquiv w σ
  let hi := isometry_pullbackWithAbsRingEquiv_symm w σ
  exact {
    toFun := h.mapRingHom
    invFun := hi.mapRingHom
    left_inv := fun a ↦ by
      refine Completion.induction_on a ?_ ?_
      · exact isClosed_eq (hi.isometry_mapRingHom.continuous.comp
          h.isometry_mapRingHom.continuous) continuous_id
      · intro b
        rw [h.mapRingHom_coe, hi.mapRingHom_coe]
        exact congrArg (fun z : WithAbs (w.pullback σ.toRingHom) ↦
          (z : (w.pullback σ.toRingHom).Completion)) (e.symm_apply_apply b)
    right_inv := fun a ↦ by
      refine Completion.induction_on a ?_ ?_
      · exact isClosed_eq (h.isometry_mapRingHom.continuous.comp
          hi.isometry_mapRingHom.continuous) continuous_id
      · intro b
        rw [hi.mapRingHom_coe, h.mapRingHom_coe]
        exact congrArg (fun z : WithAbs w ↦ (z : w.Completion)) (e.apply_symm_apply b)
    map_mul' := h.mapRingHom.map_mul
    map_add' := h.mapRingHom.map_add }

/-- Completing a pulled-back field isomorphism preserves every actual distance. -/
theorem isometry_completionRingEquivOfPullback (w : AbsoluteValue M ℝ) (σ : L ≃+* M) :
    Isometry (completionRingEquivOfPullback w σ) :=
  (isometry_pullbackWithAbsRingEquiv w σ).isometry_mapRingHom

/-- The completed map sends the original coefficient to its field-isomorphism image. -/
theorem completionRingEquivOfPullback_algebraMap
    (w : AbsoluteValue M ℝ) (σ : L ≃+* M) (a : L) :
    completionRingEquivOfPullback w σ
      (algebraMap L (w.pullback σ.toRingHom).Completion a) =
      algebraMap M w.Completion (σ a) :=
  (isometry_pullbackWithAbsRingEquiv w σ).mapRingHom_coe
    (WithAbs.toAbs (w.pullback σ.toRingHom) a)

/-- The inverse completed map has the inverse original-coefficient formula. -/
theorem completionRingEquivOfPullback_symm_algebraMap
    (w : AbsoluteValue M ℝ) (σ : L ≃+* M) (a : M) :
    (completionRingEquivOfPullback w σ).symm (algebraMap M w.Completion a) =
      algebraMap L (w.pullback σ.toRingHom).Completion (σ.symm a) := by
  apply (completionRingEquivOfPullback w σ).injective
  rw [RingEquiv.apply_symm_apply, completionRingEquivOfPullback_algebraMap,
    σ.apply_symm_apply]

end AbsoluteValue

namespace ArakelovGeometry
namespace AdelicStructure.ParameterSpaceExtension
universe u v wL wM
variable {K : Type u} [Field K] (S : AdelicStructure.{u, v} K)
  {L : Type wL} [Field L] [Algebra K L]
  {M : Type wM} [Field M] [Algebra K M]

/-- Actual completed fields at transported places are algebras over the same
original completed field, and their canonical isomorphism fixes that field. -/
def algEquivCompletedFields (σ : L ≃ₐ[K] M) (x : ParameterSpaceExtension S M) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    (pullbackAlgEquiv S σ x).abv.Completion ≃ₐ[(S.ϕ x.base).Completion] x.abv.Completion := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
    (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let e : (pullbackAlgEquiv S σ x).abv.Completion ≃+* x.abv.Completion :=
    AbsoluteValue.completionRingEquivOfPullback x.abv σ.toRingEquiv
  refine { e with commutes' := ?_ }
  intro a
  refine Completion.induction_on a ?_ ?_
  · exact isClosed_eq
      ((AbsoluteValue.isometry_completionRingEquivOfPullback x.abv σ.toRingEquiv).continuous.comp
        (AbsoluteValue.isometry_normedAlgebraCompletionOfEq (S.ϕ x.base)
          (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq).continuous)
      (AbsoluteValue.isometry_normedAlgebraCompletionOfEq (S.ϕ x.base)
        x.abv x.restrict_eq).continuous
  · intro b
    change e (algebraMap (S.ϕ x.base).Completion (pullbackAlgEquiv S σ x).abv.Completion
      (algebraMap K (S.ϕ x.base).Completion b.ofAbs)) =
      algebraMap (S.ϕ x.base).Completion x.abv.Completion
        (algebraMap K (S.ϕ x.base).Completion b.ofAbs)
    have hL := AbsoluteValue.algebraMap_normedAlgebraCompletionOfEq_coe
      (S.ϕ x.base) (pullbackAlgEquiv S σ x).abv
      (pullbackAlgEquiv S σ x).restrict_eq b.ofAbs
    have hM := AbsoluteValue.algebraMap_normedAlgebraCompletionOfEq_coe
      (S.ϕ x.base) x.abv x.restrict_eq b.ofAbs
    rw [hL, hM]
    exact (AbsoluteValue.completionRingEquivOfPullback_algebraMap
      x.abv σ.toRingEquiv (algebraMap K L b.ofAbs)).trans
      (congrArg (algebraMap M x.abv.Completion) (σ.commutes b.ofAbs))

/-- The actual completed base-field algebra isomorphism is an isometry. -/
theorem isometry_algEquivCompletedFields
    (σ : L ≃ₐ[K] M) (x : ParameterSpaceExtension S M) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    Isometry (algEquivCompletedFields S σ x) :=
  AbsoluteValue.isometry_completionRingEquivOfPullback x.abv σ.toRingEquiv

/-- Every original completed base coefficient commutes with the actual transport. -/
theorem algEquivCompletedFields_commutes
    (σ : L ≃ₐ[K] M) (x : ParameterSpaceExtension S M) (a : (S.ϕ x.base).Completion) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    algEquivCompletedFields S σ x
      (algebraMap (S.ϕ x.base).Completion (pullbackAlgEquiv S σ x).abv.Completion a) =
      algebraMap (S.ϕ x.base).Completion x.abv.Completion a := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
    (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  exact (algEquivCompletedFields S σ x).commutes a

/-- Transport at an actual place sends the original coefficient to its field image. -/
theorem algEquivCompletedFields_algebraMap
    (σ : L ≃ₐ[K] M) (x : ParameterSpaceExtension S M) (a : L) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    algEquivCompletedFields S σ x
      (algebraMap L (pullbackAlgEquiv S σ x).abv.Completion a) =
      algebraMap M x.abv.Completion (σ a) :=
  AbsoluteValue.completionRingEquivOfPullback_algebraMap x.abv σ.toRingEquiv a

end AdelicStructure.ParameterSpaceExtension
end ArakelovGeometry
