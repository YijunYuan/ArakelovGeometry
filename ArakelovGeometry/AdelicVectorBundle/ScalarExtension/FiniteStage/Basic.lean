/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Measurability.Basic
public import ArakelovGeometry.AdelicVectorBundle.Measurability.Density.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.TowerBasic
import ArakelovGeometry.AdelicVectorBundle.Dual.Bidual
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Domination.Descent
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Measurable
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Tower.Basic
import Mathlib.CategoryTheory.Category.Init

/-!
# Finite-stage descent of scalar-extension measurability

Every extended rational vector lies in an actual finite coordinate subfield.
The canonical tensor and place maps identify its norm with the finite-stage
norm when the intermediate Archimedean completions have their usual norm.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

universe u w wE

variable {K : Type u} [Field K] {L : Type w} [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] {E : Type wE} [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- Finitely many actual tensor coordinates give a finite intermediate field
and a vector whose canonical scalar extension is the prescribed vector. -/
theorem exists_finiteStage_tensor_lift (z : L ⊗[K] E) :
    ∃ F : AdelicStructure.FiniteIntermediateField K L, ∃ y : F ⊗[K] E,
      TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
        ((1 : L) ⊗ₜ[F] y) = z := by
  classical
  let b := Module.finBasis K E
  let c := (b.baseChange L).equivFun z
  let A := IntermediateField.adjoin K (Set.range c)
  have hc (j) : c j ∈ A := IntermediateField.subset_adjoin K _ ⟨j, rfl⟩
  let : FiniteDimensional K A := IntermediateField.finiteDimensional_adjoin
    (fun a _ => Algebra.IsIntegral.isIntegral a)
  let F : AdelicStructure.FiniteIntermediateField K L := ⟨A, inferInstance⟩
  let y : F ⊗[K] E := (b.baseChange F).equivFun.symm (fun j => ⟨c j, hc j⟩)
  refine ⟨F, y, ?_⟩
  rw [← (b.baseChange L).sum_repr z]
  simp only [y, Module.Basis.equivFun_symm_apply, Module.Basis.baseChange_apply,
    TensorProduct.tmul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one, one_smul]
  rfl

namespace NormFamily

variable {S : AdelicStructure K} (ξ : NormFamily S E)

/-- Ultrametricity at finite places and usual Archimedean normalization make
the canonical embedding of every completed base vector isometric. -/
theorem scalarExtension_norm_completed_one_tmul_eq_of_ultrametric
    [hξ : ξ.IsUltrametric]
    [hS : S.IsArchimedeanNormalized]
    (x : S.ParameterSpaceExtension L) (y : (S.ϕ x.base).Completion ⊗[K] E) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    (ξ.scalarExtension (L := L)).norm x
      ((completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).symm
        ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] y)) =
      ξ.norm x.base y := by
  intro aVW
  let := aVW
  apply (ξ.scalarExtension_norm_completed_one_tmul x y).trans
  by_cases hx : x.base ∈ S.Ωfin
  · exact hξ.dual_dual_norm_eval x.base hx y
  · exact ξ.dual_dual_norm_eval_eq_of_isRCLike x.base (hS x.base hx) y

/-- A rational vector from a finite intermediate field has exactly its
finite-stage norm at the restricted place. -/
theorem scalarExtension_norm_finiteStage
    (F : AdelicStructure.FiniteIntermediateField K L)
    [hF : (S.algebraicExtension F).IsArchimedeanNormalized]
    (x : S.ParameterSpaceExtension L) (z : F ⊗[K] E) :
    (ξ.scalarExtension (L := L)).norm x
      ((1 : x.abv.Completion) ⊗ₜ[L]
        (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
          ((1 : L) ⊗ₜ[F] z))) =
      (ξ.scalarExtension (L := F)).norm
        (AdelicStructure.ParameterSpaceExtension.restrict S L x F)
        ((1 : (x.abv.under F).Completion) ⊗ₜ[F] z) := by
  let xT := (AdelicStructure.Algebraic.towerMeasurableEquiv S F.1).symm x
  let := AbsoluteValue.normedAlgebraCompletionOfEq
    ((S.algebraicExtension F).ϕ xT.base) xT.abv xT.restrict_eq
  have he := (ξ.scalarExtension (L := F)).scalarExtension_norm_completed_one_tmul_eq_of_ultrametric
    (hξ := ξ.scalarExtension_isUltrametric) xT
      ((1 : ((S.algebraicExtension F).ϕ xT.base).Completion) ⊗ₜ[F] z)
  simp only [completedScalarExtensionEquiv_symm_tmul, map_one, mul_one] at he
  have ht := ξ.scalarExtension_trans xT
    ((1 : xT.abv.Completion) ⊗ₜ[L] ((1 : L) ⊗ₜ[F] z))
  rw [LinearMap.baseChange_tmul] at ht
  exact ht.symm.trans he

/-- Arbitrary algebraic scalar extension is measurable when all actual finite
intermediate Archimedean completions have their usual norm. Each rational
vector is pulled back from its finite coordinate field. -/
theorem IsMeasurable.scalarExtension_of_finiteStage_normalization
    {ξ : NormFamily S E} (hξ : ξ.IsMeasurable)
    (hS : S.HasCommonCountableDenseSubfield)
    [hN : ∀ F : AdelicStructure.FiniteIntermediateField K L,
      (S.algebraicExtension F).IsArchimedeanNormalized] :
    (ξ.scalarExtension (L := L)).IsMeasurable := by
  constructor
  intro z
  obtain ⟨F, y, hy⟩ := exists_finiteStage_tensor_lift z
  have hm := hξ.scalarExtension_of_finiteDimensional_of_common_countable_dense_subfield
    (L := F) hS
  have hr : @Measurable (S.algebraicExtension L).Ω (S.algebraicExtension F).Ω
      (S.algebraicExtension L).instMeasurableSpaceΩ
      (S.algebraicExtension F).instMeasurableSpaceΩ
      (fun x => AdelicStructure.ParameterSpaceExtension.restrict S L x F) := by
    change @Measurable _ _ (AdelicStructure.Algebraic.projectiveMeasurableSpace S L)
      (AdelicStructure.Algebraic.projectiveMeasurableSpace S F) _
    rw [AdelicStructure.Algebraic.projectiveMeasurableSpace_eq,
      AdelicStructure.Algebraic.projectiveMeasurableSpace_eq]
    exact AdelicStructure.ParameterSpaceExtension.measurable_restrict S L F.1
  have he : (fun x : (S.algebraicExtension L).Ω =>
      (ξ.scalarExtension (L := L)).norm x
        ((1 : ((S.algebraicExtension L).ϕ x).Completion) ⊗ₜ[L] z)) =
      (fun x : (S.algebraicExtension L).Ω =>
        (ξ.scalarExtension (L := F)).norm
          (AdelicStructure.ParameterSpaceExtension.restrict S L x F)
          ((1 : (x.abv.under F).Completion) ⊗ₜ[F] y)) := by
    funext x
    rw [← hy]
    exact ξ.scalarExtension_norm_finiteStage F x y
  rw [he]
  exact (hm y).comp hr

/-- Every algebraic ordinary scalar extension of a measurable family is
measurable under common countable density and the original usual Archimedean
normalization. No normalization of intermediate completions is assumed. -/
theorem IsMeasurable.scalarExtension_of_common_countable_dense_subfield
    {ξ : NormFamily S E} (hξ : ξ.IsMeasurable)
    (hS : S.HasCommonCountableDenseSubfield)
    [hN : S.IsArchimedeanNormalized] :
    (ξ.scalarExtension (L := L)).IsMeasurable :=
  hξ.scalarExtension_of_finiteStage_normalization hS

end NormFamily

end ArakelovGeometry
