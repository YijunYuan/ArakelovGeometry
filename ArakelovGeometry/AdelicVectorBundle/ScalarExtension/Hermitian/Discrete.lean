/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Measurability.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Hermitian.Basic

import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Discrete.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.FiniteStage.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Hermitian.Measurable
import Mathlib.CategoryTheory.Category.Init

/-!
# Hermitian scalar extension over a countable discrete base

Actual finite-stage descent proves the corrected discrete alternative of
Chen–Moriwaki Proposition 4.1.24(1.c), without a common dense subfield.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

universe u w wE

variable {K : Type u} [Field K] {L : Type w} [Field L] [Algebra K L]
  {S : AdelicStructure K}
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Algebra.IsAlgebraic K L] (ξ : NormFamily S E)
  [hS : S.IsArchimedeanNormalized]
  [hH : ξ.IsHermitian]

/-- Finite Hermitian scalar extension is measurable on the actual discrete
extending parameter space; normalization is produced from the original base. -/
theorem hermitianScalarExtension_isMeasurable_of_finiteDimensional_of_countable_discrete
    [FiniteDimensional K L] [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] :
    (hermitianScalarExtension ξ
      (hL := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension
          (L := L))⟩)).IsMeasurable := by
  let := AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
    (S := S) (L := L)
  exact isMeasurable_of_discrete (hermitianScalarExtension ξ
    (hL := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩))

/-- Corrected source4.1.24(1.c): actual Hermitian scalar extension is measurable
for every algebraic extension of a countable discrete base, in every rank.
No common dense subfield or measurability premise on the target is assumed. -/
theorem hermitianScalarExtension_isMeasurable_of_countable_discrete
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] :
    (hermitianScalarExtension ξ
      (hL := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension
          (L := L))⟩)).IsMeasurable := by
  constructor
  intro z
  obtain ⟨F, y, hy⟩ := exists_finiteStage_tensor_lift z
  let hF := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := F)
  let hL := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
  have hm := hermitianScalarExtension_isMeasurable_of_finiteDimensional_of_countable_discrete
    (L := F) ξ
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
      (hermitianScalarExtension ξ (hL := ⟨hL⟩)).norm x
        ((1 : x.abv.Completion) ⊗ₜ[L] z)) =
      (fun x : (S.algebraicExtension L).Ω =>
        (hermitianScalarExtension ξ (hL := ⟨hF⟩)).norm
          (AdelicStructure.ParameterSpaceExtension.restrict S L x F)
          ((1 : (x.abv.under F).Completion) ⊗ₜ[F] y)) := by
    funext x
    rw [← hy]
    exact hermitianScalarExtension_norm_finiteStage ξ (hL := ⟨hL⟩) F (hF := ⟨hF⟩) x y
  exact he.symm ▸ (hm y).comp hr

end ArakelovGeometry.NormFamily
