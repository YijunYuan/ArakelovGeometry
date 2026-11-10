/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionTower
public import ArakelovGeometry.Analysis.ScalarExtensionSubspace

/-!
# Completed scalar extension and actual subspace norms

The canonical completed tensor identifications commute with every base-changed
linear map. Consequently ordinary scalar extension is contractive on genuine
subspaces and preserves their norms exactly at non-Archimedean places when the
original norm family is ultrametric.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry

universe u v w wE wF

variable {K : Type u} [Field K] {L : Type w} [Field L] [Algebra K L]
  {E : Type wE} [AddCommGroup E] [Module K E]
  {F : Type wF} [AddCommGroup F] [Module K F]

/-- The canonical completed tensor identification commutes with every
base-changed linear map. -/
theorem completedScalarExtensionEquiv_baseChange (f : F →ₗ[K] E)
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) (h : w.restriction K = v)
    (z : w.Completion ⊗[L] (L ⊗[K] F)) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq v w h
    completedScalarExtensionEquiv E v w h
        ((f.baseChange L).baseChange w.Completion z) =
      (f.baseChange v.Completion).baseChange w.Completion
        (completedScalarExtensionEquiv F v w h z) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq v w h
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simp only [map_add, hz, ht]
  | tmul a y =>
    induction y using TensorProduct.inductionOn with
    | add y t hy ht => simp only [TensorProduct.tmul_add, map_add, hy, ht]
    | tmul b y =>
      simp only [LinearMap.baseChange_tmul, completedScalarExtensionEquiv_tmul]

namespace NormFamily

variable {S : AdelicStructure.{u, v} K} (ξ : NormFamily S E)

/-- Projective extension is contractive on the entire actual completed
fibre of a pullback. -/
theorem projectiveScalarExtensionSeminorm_pullback_le (f : F →ₗ[K] E)
    (hf : Function.Injective f) (x : AdelicStructure.ParameterSpaceExtension S L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] F)) :
    ξ.projectiveScalarExtensionSeminorm x
        ((f.baseChange L).baseChange x.abv.Completion z) ≤
      (ξ.pullback f hf).projectiveScalarExtensionSeminorm x z := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let := (ξ.pullback f hf).fibreNormedAddCommGroup x.base
  let := (ξ.pullback f hf).fibreNormedSpace x.base
  change scalarExtensionProjectiveSeminorm
      (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq
        ((f.baseChange L).baseChange x.abv.Completion z)) ≤
    scalarExtensionProjectiveSeminorm
      (completedScalarExtensionEquiv F (S.ϕ x.base) x.abv x.restrict_eq z)
  rw [completedScalarExtensionEquiv_baseChange]
  exact scalarExtensionProjectiveSeminorm_baseChange_le
    (f.baseChange (S.ϕ x.base).Completion) (fun _ => le_rfl) _

variable [FiniteDimensional K E] [FiniteDimensional K F]

/-- At a non-Archimedean extending place, injective extension is
contractive on the actual pullback even without original ultrametricity. -/
theorem injectiveScalarExtensionSeminorm_pullback_le (f : F →ₗ[K] E)
    (hf : Function.Injective f) (x : AdelicStructure.ParameterSpaceExtension S L)
    (hx : x.base ∈ S.Ωfin) (z : x.abv.Completion ⊗[L] (L ⊗[K] F)) :
    ξ.injectiveScalarExtensionSeminorm x
        ((f.baseChange L).baseChange x.abv.Completion z) ≤
      (ξ.pullback f hf).injectiveScalarExtensionSeminorm x z := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let := (ξ.pullback f hf).fibreNormedAddCommGroup x.base
  let := (ξ.pullback f hf).fibreNormedSpace x.base
  have hnon : IsNonarchimedean x.abv := by
    apply (AbsoluteValue.isNonarchimedean_restriction_iff (K := K) x.abv).mp
    rw [x.restrict_eq]
    exact hx
  let := AbsoluteValue.isUltrametricDist_completion x.abv hnon
  change scalarExtensionInjectiveSeminorm
      (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq
        ((f.baseChange L).baseChange x.abv.Completion z)) ≤
    scalarExtensionInjectiveSeminorm
      (completedScalarExtensionEquiv F (S.ϕ x.base) x.abv x.restrict_eq z)
  rw [completedScalarExtensionEquiv_baseChange]
  exact scalarExtensionInjectiveSeminorm_baseChange_le
    (f.baseChange (S.ϕ x.base).Completion) (fun _ => le_rfl) _

/-- When the original family is ultrametric, actual pullback and injective
extension commute isometrically on every completed vector at a finite place. -/
theorem injectiveScalarExtensionSeminorm_pullback_eq (hξ : ξ.IsUltrametric)
    (f : F →ₗ[K] E) (hf : Function.Injective f)
    (x : AdelicStructure.ParameterSpaceExtension S L) (hx : x.base ∈ S.Ωfin)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] F)) :
    ξ.injectiveScalarExtensionSeminorm x
        ((f.baseChange L).baseChange x.abv.Completion z) =
      (ξ.pullback f hf).injectiveScalarExtensionSeminorm x z := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let := (ξ.pullback f hf).fibreNormedAddCommGroup x.base
  let := (ξ.pullback f hf).fibreNormedSpace x.base
  have hnon : IsNonarchimedean x.abv := by
    apply (AbsoluteValue.isNonarchimedean_restriction_iff (K := K) x.abv).mp
    rw [x.restrict_eq]
    exact hx
  let := AbsoluteValue.isUltrametricDist_completion x.abv hnon
  let : IsUltrametricDist ((S.ϕ x.base).Completion ⊗[K] E) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (hξ x.base hx)
  let j : ((S.ϕ x.base).Completion ⊗[K] F) →ₗᵢ[(S.ϕ x.base).Completion]
      ((S.ϕ x.base).Completion ⊗[K] E) :=
    { toLinearMap := f.baseChange (S.ϕ x.base).Completion, norm_map' := fun _ => rfl }
  change scalarExtensionInjectiveSeminorm
      (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq
        ((f.baseChange L).baseChange x.abv.Completion z)) =
    scalarExtensionInjectiveSeminorm
      (completedScalarExtensionEquiv F (S.ϕ x.base) x.abv x.restrict_eq z)
  rw [completedScalarExtensionEquiv_baseChange]
  exact scalarExtensionInjectiveSeminorm_baseChange_embedding j _

variable [Algebra.IsAlgebraic K L]

/-- The actual ordinary extended norm is contractive on the base change
of every genuine pullback. -/
theorem scalarExtension_pullback_norm_le (f : F →ₗ[K] E)
    (hf : Function.Injective f) (x : AdelicStructure.ParameterSpaceExtension S L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] F)) :
    (ξ.scalarExtension (L := L)).norm x
        ((f.baseChange L).baseChange x.abv.Completion z) ≤
      ((ξ.pullback f hf).scalarExtension (L := L)).norm x z := by
  by_cases hx : x.base ∈ S.Ωfin
  · rw [scalarExtension_norm_of_mem_Ωfin ξ x hx,
      scalarExtension_norm_of_mem_Ωfin (ξ.pullback f hf) x hx]
    exact ξ.injectiveScalarExtensionSeminorm_pullback_le f hf x hx z
  · rw [scalarExtension_norm_of_not_mem_Ωfin ξ x hx,
      scalarExtension_norm_of_not_mem_Ωfin (ξ.pullback f hf) x hx]
    exact ξ.projectiveScalarExtensionSeminorm_pullback_le f hf x z

/-- Actual ordinary extension preserves every completed pullback norm at
a non-Archimedean place of an ultrametric family. -/
theorem scalarExtension_pullback_norm_eq_of_mem_Ωfin (hξ : ξ.IsUltrametric)
    (f : F →ₗ[K] E) (hf : Function.Injective f)
    (x : AdelicStructure.ParameterSpaceExtension S L) (hx : x.base ∈ S.Ωfin)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] F)) :
    (ξ.scalarExtension (L := L)).norm x
        ((f.baseChange L).baseChange x.abv.Completion z) =
      ((ξ.pullback f hf).scalarExtension (L := L)).norm x z := by
  rw [scalarExtension_norm_of_mem_Ωfin ξ x hx,
    scalarExtension_norm_of_mem_Ωfin (ξ.pullback f hf) x hx]
  exact ξ.injectiveScalarExtensionSeminorm_pullback_eq hξ f hf x hx z

omit [FiniteDimensional K F] in
/-- The actual restricted extended norm on the base-changed subspace is
bounded by the extension of the original restricted norm, through the
canonical subspace tensor equivalence. -/
theorem scalarExtension_restrict_norm_le (A : Submodule K E)
    (x : AdelicStructure.ParameterSpaceExtension S L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] A)) :
    ((ξ.scalarExtension (L := L)).restrict (A.baseChange L)).norm x
        ((Submodule.toBaseChange.toLinearEquiv L A).toLinearMap.baseChange
          x.abv.Completion z) ≤
      ((ξ.restrict A).scalarExtension (L := L)).norm x z := by
  change (ξ.scalarExtension (L := L)).norm x
      ((A.baseChange L).subtype.baseChange x.abv.Completion
        ((Submodule.toBaseChange.toLinearEquiv L A).toLinearMap.baseChange
          x.abv.Completion z)) ≤ _
  have he : (A.baseChange L).subtype.comp
      (Submodule.toBaseChange.toLinearEquiv L A).toLinearMap =
      A.subtype.baseChange L := rfl
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, he]
  exact ξ.scalarExtension_pullback_norm_le A.subtype A.subtype_injective x z

omit [FiniteDimensional K F] in
/-- At every finite place, the actual canonical tensor equivalence between
the extension of a subspace and its base-changed image preserves all
completed restricted norms of an ultrametric family. -/
theorem scalarExtension_restrict_norm_eq_of_mem_Ωfin (hξ : ξ.IsUltrametric)
    (A : Submodule K E) (x : AdelicStructure.ParameterSpaceExtension S L)
    (hx : x.base ∈ S.Ωfin) (z : x.abv.Completion ⊗[L] (L ⊗[K] A)) :
    ((ξ.scalarExtension (L := L)).restrict (A.baseChange L)).norm x
        ((Submodule.toBaseChange.toLinearEquiv L A).toLinearMap.baseChange
          x.abv.Completion z) =
      ((ξ.restrict A).scalarExtension (L := L)).norm x z := by
  change (ξ.scalarExtension (L := L)).norm x
      ((A.baseChange L).subtype.baseChange x.abv.Completion
        ((Submodule.toBaseChange.toLinearEquiv L A).toLinearMap.baseChange
          x.abv.Completion z)) = _
  have he : (A.baseChange L).subtype.comp
      (Submodule.toBaseChange.toLinearEquiv L A).toLinearMap =
      A.subtype.baseChange L := rfl
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, he]
  exact ξ.scalarExtension_pullback_norm_eq_of_mem_Ωfin
    hξ A.subtype A.subtype_injective x hx z

end NormFamily

end ArakelovGeometry
