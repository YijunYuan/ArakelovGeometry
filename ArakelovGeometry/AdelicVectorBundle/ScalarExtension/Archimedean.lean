/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic
public import ArakelovGeometry.AdelicVectorBundle.Subquotient.Restriction.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Subspace.Basic
import ArakelovGeometry.Analysis.ScalarExtension.ArchimedeanComplexExtension
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual restricted norms after complexification

A finite intermediate field can contain a square root of minus one. Over such
a base field the actual Archimedean completion maps are onto, so projective
extension preserves every completed pullback. Together with the finite-place
isometry this gives ordinary restriction identities on all actual fibres.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry

universe u v w wE wF

variable {K : Type u} [Field K] {L : Type w} [Field L] [Algebra K L]

/-- The algebraically closed extending field produces an actual finite
intermediate field containing a square root of minus one, in any characteristic. -/
theorem exists_finiteStage_sqrt_neg_one [Algebra.IsAlgebraic K L] [IsAlgClosed L] :
    ∃ F : AdelicStructure.FiniteIntermediateField K L, ∃ a : F, a ^ 2 = -1 := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : L) (show 0 < 2 by decide)
  let A := IntermediateField.adjoin K ({a} : Set L)
  let : FiniteDimensional K A := IntermediateField.finiteDimensional_adjoin
    (fun b _ => Algebra.IsIntegral.isIntegral b)
  let F : AdelicStructure.FiniteIntermediateField K L := ⟨A, inferInstance⟩
  let b : F := ⟨a, IntermediateField.subset_adjoin K _ (Set.mem_singleton a)⟩
  refine ⟨F, b, ?_⟩
  apply Subtype.ext
  exact ha

variable {S : AdelicStructure.{u, v} K}

/-- If the original field contains a square root of minus one, every actual
Archimedean completed scalar embedding is bijective. -/
theorem AdelicStructure.completedEmbedding_bijective_of_sqrt_neg_one
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hi : ∃ a : K, a ^ 2 = -1)
    (x : S.ParameterSpaceExtension L) (hx : x.base ∈ S.Ωinf) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    Function.Bijective (algebraMap (S.ϕ x.base).Completion x.abv.Completion) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let : IsRCLikeNormedField (S.ϕ x.base).Completion := hN x.base hx
  obtain ⟨a, ha⟩ := hi
  apply algebraMap_bijective_of_isRCLikeNormedField_sqrt_neg_one
  refine ⟨algebraMap K (S.ϕ x.base).Completion a, ?_⟩
  simpa only [map_pow, map_neg, map_one] using
    congrArg (algebraMap K (S.ϕ x.base).Completion) ha

namespace NormFamily

variable {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type wF} [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  (ξ : NormFamily S E)

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- With a square root of minus one in the base, projective extension
preserves every actual completed pullback at each Archimedean place. -/
theorem projectiveScalarExtensionSeminorm_pullback_eq_of_sqrt_neg_one
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hi : ∃ a : K, a ^ 2 = -1) (f : F →ₗ[K] E) (hf : Function.Injective f)
    (x : S.ParameterSpaceExtension L) (hx : x.base ∈ S.Ωinf)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] F)) :
    ξ.projectiveScalarExtensionSeminorm x
        ((f.baseChange L).baseChange x.abv.Completion z) =
      (ξ.pullback f hf).projectiveScalarExtensionSeminorm x z := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let : IsRCLikeNormedField (S.ϕ x.base).Completion := hN x.base hx
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let := (ξ.pullback f hf).fibreNormedAddCommGroup x.base
  let := (ξ.pullback f hf).fibreNormedSpace x.base
  have hroot : ∃ a : (S.ϕ x.base).Completion, a ^ 2 = -1 := by
    obtain ⟨a, ha⟩ := hi
    refine ⟨algebraMap K (S.ϕ x.base).Completion a, ?_⟩
    simpa only [map_pow, map_neg, map_one] using
      congrArg (algebraMap K (S.ϕ x.base).Completion) ha
  change scalarExtensionProjectiveSeminorm
      (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq
        ((f.baseChange L).baseChange x.abv.Completion z)) =
    scalarExtensionProjectiveSeminorm
      (completedScalarExtensionEquiv F (S.ϕ x.base) x.abv x.restrict_eq z)
  rw [completedScalarExtensionEquiv_baseChange]
  exact scalarExtensionProjectiveSeminorm_baseChange_embedding_of_sqrt_neg_one
    hroot (f.baseChange (S.ϕ x.base).Completion) (fun _ => rfl) _

variable [Algebra.IsAlgebraic K L]

/-- Ordinary extension over a complexified base preserves the actual
completed pullback norm at every place of an ultrametric norm family. -/
theorem scalarExtension_pullback_norm_eq_of_sqrt_neg_one (hξ : ξ.IsUltrametric)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hi : ∃ a : K, a ^ 2 = -1) (f : F →ₗ[K] E) (hf : Function.Injective f)
    (x : S.ParameterSpaceExtension L) (z : x.abv.Completion ⊗[L] (L ⊗[K] F)) :
    (ξ.scalarExtension (L := L)).norm x
        ((f.baseChange L).baseChange x.abv.Completion z) =
      ((ξ.pullback f hf).scalarExtension (L := L)).norm x z := by
  by_cases hx : x.base ∈ S.Ωfin
  · exact ξ.scalarExtension_pullback_norm_eq_of_mem_Ωfin hξ f hf x hx z
  · rw [scalarExtension_norm_of_not_mem_Ωfin ξ x hx,
      scalarExtension_norm_of_not_mem_Ωfin (ξ.pullback f hf) x hx]
    exact ξ.projectiveScalarExtensionSeminorm_pullback_eq_of_sqrt_neg_one
      hN hi f hf x hx z

omit [FiniteDimensional K F] in
/-- The native base-changed subspace, under the canonical tensor equivalence,
has exactly the extended original restriction norm on every completed fibre. -/
theorem scalarExtension_restrict_norm_eq_of_sqrt_neg_one (hξ : ξ.IsUltrametric)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hi : ∃ a : K, a ^ 2 = -1) (A : Submodule K E)
    (x : S.ParameterSpaceExtension L) (z : x.abv.Completion ⊗[L] (L ⊗[K] A)) :
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
  exact ξ.scalarExtension_pullback_norm_eq_of_sqrt_neg_one
    hξ hN hi A.subtype A.subtype_injective x z

end NormFamily

end ArakelovGeometry
