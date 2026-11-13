/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Algebraic.ClosureApproximation
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Bundle
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.HermitianComparison.DeterminantDegree

import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.HermitianComparison.Comparison
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual ordinary and Hermitian extension invariant comparison

The accepted same-completed-fibre Hermitian norm inequality dominates every
genuine ordinary native restricted degree and mean. Actual subspace suprema
then compare canonical positive degree and maximal slope in every rank.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local instance hermitianOrdinaryComparisonProper : (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- Every actual ordinary native restricted degree is at most its Hermitian
counterpart on the same actual target subspace and completed fibres. -/
theorem degree_restrict_scalarExtension_le_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (U : Submodule L (L ⊗[K] V)) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let P := V.scalarExtension (L := L)
    let H := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    (P.restrictOfNormMeasurability U (hS := ⟨hLS⟩)).degree (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) ≤
      (H.restrictOfNormMeasurability U (hS := ⟨hLS⟩)).degree (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) := by
  intro hLN hLS P H
  have hn : H.toNormFamily ≤ P.toNormFamily :=
    V.toNormFamily.hermitianScalarExtension_le_scalarExtension (hL := ⟨hLN⟩)
  exact degree_antitone (H.restrictOfNormMeasurability U (hS := ⟨hLS⟩))
    (P.restrictOfNormMeasurability U (hS := ⟨hLS⟩)).toNormFamily
    (hW := (P.restrictOfNormMeasurability U (hS := ⟨hLS⟩)).toIsAdelic)
    (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (fun x z ↦ hn x _)

/-- Dividing genuine native restricted degree domination by the common rank
compares both real means, including the zero-rank convention. -/
theorem slope_restrict_scalarExtension_le_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (U : Submodule L (L ⊗[K] V)) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let P := V.scalarExtension (L := L)
    let H := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    (P.restrictOfNormMeasurability U (hS := ⟨hLS⟩)).slope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) ≤
      (H.restrictOfNormMeasurability U (hS := ⟨hLS⟩)).slope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) := by
  intro hLN hLS P H
  dsimp only [slope]
  exact div_le_div_of_nonneg_right
    (V.degree_restrict_scalarExtension_le_hermitianScalarExtension_of_isAlgClosed
       U) (Nat.cast_nonneg _)

/-- The ordinary actual positive-degree supremum is bounded by the actual
Hermitian supremum, using every genuine native target restricted degree. -/
theorem positiveDegree_scalarExtension_le_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let P := V.scalarExtension (L := L)
    let H := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    P.positiveDegree (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) ≤ H.positiveDegree (hS := ⟨hLS⟩)
        (hN := ⟨hLN⟩) := by
  intro hLN hLS P H
  apply P.positiveDegree_le (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
  intro U
  exact (EReal.coe_le_coe_iff.mpr
    (V.degree_restrict_scalarExtension_le_hermitianScalarExtension_of_isAlgClosed
       U)).trans (H.degree_restrict_le_positiveDegree (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) U)

/-- Every actual positive-rank ordinary mean is bounded by the same Hermitian
mean, hence the actual maximal-slope suprema are ordered in every rank. -/
theorem maximalSlope_scalarExtension_le_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let P := V.scalarExtension (L := L)
    let H := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    P.maximalSlope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) ≤ H.maximalSlope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) := by
  intro hLN hLS P H
  apply P.maximalSlope_le (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
  intro U hU
  exact (EReal.coe_le_coe_iff.mpr
    (V.slope_restrict_scalarExtension_le_hermitianScalarExtension_of_isAlgClosed
       U)).trans (H.slope_restrict_le_maximalSlope U hU (hS := ⟨hLS⟩) (hN := ⟨hLN⟩))

end ArakelovGeometry.AdelicVectorBundle
