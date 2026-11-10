/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic
public import ArakelovGeometry.AdelicVectorBundle.Tensor.HermitianInnerProduct
public import ArakelovGeometry.Analysis.ScalarExtension.Hermitian.Basic
import Mathlib.CategoryTheory.Category.Init

/-!
# Hermitian scalar extension of norm families

For a Hermitian norm family, extension uses the injective norm at non-Archimedean
places and the norm of the extended positive-definite inner product at Archimedean
places. The base and extension completion fields carry the stated usual real or
complex normalization.

The construction acts on the completed scalar-extension fibres. The comparison
with ordinary projective scalar extension is established separately, with its
precise normalization and scalar hypotheses.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

universe u v w wE

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E)
  (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hL : ∀ x ∈ (S.algebraicExtension L).Ωinf,
    IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
  (hξ : ξ.IsHermitian hS)

/-- An extending infinite place lies above an infinite base place. -/
theorem scalarExtension_mem_Ωinf_iff (x : S.ParameterSpaceExtension L) :
    x ∈ (S.algebraicExtension L).Ωinf ↔ x.base ∈ S.Ωinf :=
  not_congr (AdelicStructure.mem_Ωfin_algebraicExtension_iff x)

/-- The exact Hermitian norm transported to the actual completed fibre at
an infinite extending place. Both completed-field normalizations are explicit. -/
def hermitianScalarExtensionArchSeminorm (x : S.ParameterSpaceExtension L)
    (hx : x ∈ (S.algebraicExtension L).Ωinf) :
    Seminorm x.abv.Completion (x.abv.Completion ⊗[L] (L ⊗[K] E)) := by
  letI := hS x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
  letI := IsRCLikeNormedField.rclike (S.ϕ x.base).Completion
  letI : IsRCLikeNormedField x.abv.Completion := hL x hx
  letI := IsRCLikeNormedField.rclike x.abv.Completion
  letI : NormedAlgebra (S.ϕ x.base).Completion x.abv.Completion :=
    AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  letI := ξ.fibreNormedAddCommGroup x.base
  letI := ξ.fibreNormedSpace x.base
  letI := hξ.fibreInnerProductSpace x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
  exact (ArakelovGeometry.hermitianScalarExtensionSeminorm
    (L := x.abv.Completion)
    (stdOrthonormalBasis (S.ϕ x.base).Completion ((S.ϕ x.base).Completion ⊗[K] E))).comp
      (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).toLinearMap

/-- The infinite-place Hermitian scalar-extension seminorm separates zero. -/
theorem hermitianScalarExtensionArchSeminorm_eq_zero_iff (x : S.ParameterSpaceExtension L)
    (hx : x ∈ (S.algebraicExtension L).Ωinf)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    hermitianScalarExtensionArchSeminorm ξ hS hL hξ x hx z = 0 ↔ z = 0 := by
  let := hS x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
  let := IsRCLikeNormedField.rclike (S.ϕ x.base).Completion
  let : IsRCLikeNormedField x.abv.Completion := hL x hx
  let := IsRCLikeNormedField.rclike x.abv.Completion
  let : NormedAlgebra (S.ϕ x.base).Completion x.abv.Completion :=
    AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let := hξ.fibreInnerProductSpace x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
  change ArakelovGeometry.hermitianScalarExtensionSeminorm _
    (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq z) = 0 ↔ _
  rw [ArakelovGeometry.hermitianScalarExtensionSeminorm_eq_zero_iff,
    LinearEquiv.map_eq_zero_iff]

/-- Hermitian scalar extension uses the exact extended inner product at
infinite places and the injective norm at finite places. -/
def hermitianScalarExtension : NormFamily (S.algebraicExtension L) (L ⊗[K] E) := by
  classical
  exact
    { norm := fun x => if hx : x ∈ (S.algebraicExtension L).Ωinf then
        hermitianScalarExtensionArchSeminorm ξ hS hL hξ x hx
      else (ξ.injectiveScalarExtension (L := L)).norm x
      norm_eq_zero_iff := fun x z => by
        change S.ParameterSpaceExtension L at x
        change x.abv.Completion ⊗[L] (L ⊗[K] E) at z
        change (if hx : x ∈ (S.algebraicExtension L).Ωinf then
          hermitianScalarExtensionArchSeminorm ξ hS hL hξ x hx
          else ξ.injectiveScalarExtensionSeminorm x) z = 0 ↔ z = 0
        by_cases hx : x ∈ (S.algebraicExtension L).Ωinf
        · rw [dite_eq_left hx]
          exact hermitianScalarExtensionArchSeminorm_eq_zero_iff ξ hS hL hξ x hx z
        · rw [dite_eq_right hx]
          exact ξ.injectiveScalarExtensionSeminorm_eq_zero_iff x z }

/-- The actual Hermitian scalar-extension norm is injective at finite places. -/
theorem hermitianScalarExtension_norm_of_finite (x : S.ParameterSpaceExtension L)
    (hx : x ∈ (S.algebraicExtension L).Ωfin)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    (hermitianScalarExtension ξ hS hL hξ).norm x z =
      (ξ.injectiveScalarExtension (L := L)).norm x z := by
  classical
  change (if hx : x ∈ (S.algebraicExtension L).Ωinf then
    hermitianScalarExtensionArchSeminorm ξ hS hL hξ x hx
    else ξ.injectiveScalarExtensionSeminorm x) z = ξ.injectiveScalarExtensionSeminorm x z
  simp only [dite_eq_right (show x ∉ (S.algebraicExtension L).Ωinf
    from fun hi => hi hx)]

/-- The actual Hermitian scalar-extension norm is the transported pairing
norm at infinite places. -/
theorem hermitianScalarExtension_norm_of_infinite (x : S.ParameterSpaceExtension L)
    (hx : x ∈ (S.algebraicExtension L).Ωinf)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    (hermitianScalarExtension ξ hS hL hξ).norm x z =
      hermitianScalarExtensionArchSeminorm ξ hS hL hξ x hx z := by
  classical
  change (if hx : x ∈ (S.algebraicExtension L).Ωinf then
    hermitianScalarExtensionArchSeminorm ξ hS hL hξ x hx
    else ξ.injectiveScalarExtensionSeminorm x) z = _
  simp only [dite_eq_left hx]

/-- The Hermitian extension is ultrametric at all finite extending places. -/
theorem hermitianScalarExtension_isUltrametric :
    (hermitianScalarExtension ξ hS hL hξ).IsUltrametric := by
  intro x hx z t
  change S.ParameterSpaceExtension L at x
  change x.abv.Completion ⊗[L] (L ⊗[K] E) at z t
  change (hermitianScalarExtension ξ hS hL hξ).norm x (z + t) ≤
    max ((hermitianScalarExtension ξ hS hL hξ).norm x z)
      ((hermitianScalarExtension ξ hS hL hξ).norm x t)
  simp only [hermitianScalarExtension_norm_of_finite ξ hS hL hξ x hx]
  exact ξ.injectiveScalarExtension_isUltrametric x hx z t

/-- The scalar-extended family is Hermitian for its actual completed
norms and the given usual Archimedean normalizations. -/
theorem hermitianScalarExtension_isHermitian :
    (hermitianScalarExtension ξ hS hL hξ).IsHermitian hL := by
  classical
  refine ⟨hermitianScalarExtension_isUltrametric ξ hS hL hξ, fun x hx => ?_⟩
  change S.ParameterSpaceExtension L at x
  let := hS x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
  let := IsRCLikeNormedField.rclike (S.ϕ x.base).Completion
  let : IsRCLikeNormedField x.abv.Completion := hL x hx
  let := IsRCLikeNormedField.rclike x.abv.Completion
  let : NormedAlgebra (S.ϕ x.base).Completion x.abv.Completion :=
    AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let := hξ.fibreInnerProductSpace x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
  let : NormedAddCommGroup (x.abv.Completion ⊗[L] (L ⊗[K] E)) :=
    (hermitianScalarExtension ξ hS hL hξ).fibreNormedAddCommGroup x
  let : NormedSpace x.abv.Completion (x.abv.Completion ⊗[L] (L ⊗[K] E)) :=
    (hermitianScalarExtension ξ hS hL hξ).fibreNormedSpace x
  let b := stdOrthonormalBasis (S.ϕ x.base).Completion ((S.ϕ x.base).Completion ⊗[K] E)
  let f := (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).trans
    (ArakelovGeometry.hermitianScalarExtensionCoordinates b)
  change ∃ c : InnerProductSpace.Core x.abv.Completion
    (x.abv.Completion ⊗[L] (L ⊗[K] E)), ∀ z, ‖z‖ ^ 2 = RCLike.re (c.inner z z)
  apply exists_innerProductCore_iff_innerProductSpaceable.mpr
  apply innerProductSpaceable_of_norm_preserving_addMonoidHom f.toAddMonoidHom
  intro z
  change ‖f z‖ = (hermitianScalarExtension ξ hS hL hξ).norm x z
  rw [hermitianScalarExtension_norm_of_infinite ξ hS hL hξ x hx z]
  rfl

/-- On every pure scalar tensor in an infinite completed fibre, the
Hermitian extension has the exact product norm. -/
theorem hermitianScalarExtension_norm_tmul_of_infinite (x : S.ParameterSpaceExtension L)
    (hx : x ∈ (S.algebraicExtension L).Ωinf)
    (a : x.abv.Completion) (y : (S.ϕ x.base).Completion ⊗[K] E) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    (hermitianScalarExtension ξ hS hL hξ).norm x
      ((completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).symm
        (a ⊗ₜ[(S.ϕ x.base).Completion] y)) = ‖a‖ * ξ.norm x.base y := by
  let := hS x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
  let := IsRCLikeNormedField.rclike (S.ϕ x.base).Completion
  let : IsRCLikeNormedField x.abv.Completion := hL x hx
  let := IsRCLikeNormedField.rclike x.abv.Completion
  let : NormedAlgebra (S.ϕ x.base).Completion x.abv.Completion :=
    AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let := hξ.fibreInnerProductSpace x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
  rw [hermitianScalarExtension_norm_of_infinite ξ hS hL hξ x hx]
  change ArakelovGeometry.hermitianScalarExtensionSeminorm _
    (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq
      ((completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).symm
        (a ⊗ₜ[(S.ϕ x.base).Completion] y))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact ArakelovGeometry.hermitianScalarExtensionSeminorm_tmul _ a y

end ArakelovGeometry.NormFamily

end
