/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Bundle

import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Slopes
import ArakelovGeometry.AdelicVectorBundle.Slope.Finite
import Mathlib.CategoryTheory.Category.Init

/-!
# Absolute invariants of actual scalar-extended adelic bundles

The canonical algebraic-closure bundle supplies absolute positive degree and
maximal slope. Common countable density in its completed fields is produced,
so the suprema range over all actual native subspaces and their usual degrees.
Finiteness and the zero-rank conventions follow from the actual slope bounds.
-/

@[expose] public section

noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Positive degree of the actual ordinary algebraic-closure bundle. -/
def absolutePositiveDegree (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized] : EReal :=
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S (AlgebraicClosure K)
  (V.scalarExtension (L := AlgebraicClosure K)).positiveDegree
    (hS := ⟨(by exact Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := AlgebraicClosure K)))⟩)
    (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := AlgebraicClosure K))⟩)

/-- Maximal slope of the actual ordinary algebraic-closure bundle; the zero
bundle has the existing empty-supremum value `⊥`. -/
def absoluteMaximalSlope (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized] : EReal :=
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S (AlgebraicClosure K)
  (V.scalarExtension (L := AlgebraicClosure K)).maximalSlope
    (hS := ⟨(by exact Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := AlgebraicClosure K)))⟩)
    (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := AlgebraicClosure K))⟩)

/-- The actual zero subspace makes absolute positive degree nonnegative. -/
theorem absolutePositiveDegree_nonneg (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized] :
    0 ≤ V.absolutePositiveDegree := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S (AlgebraicClosure K)
  exact (V.scalarExtension (L := AlgebraicClosure K)).positiveDegree_nonneg

/-- A produced actual rank-degree bound excludes positive infinity. -/
theorem absolutePositiveDegree_lt_top (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized] :
    V.absolutePositiveDegree < ⊤ := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S (AlgebraicClosure K)
  exact (V.scalarExtension (L := AlgebraicClosure K)).positiveDegree_lt_top

/-- Absolute maximal slope has a finite upper bound in every rank. -/
theorem absoluteMaximalSlope_lt_top (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized] :
    V.absoluteMaximalSlope < ⊤ := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S (AlgebraicClosure K)
  exact (V.scalarExtension (L := AlgebraicClosure K)).maximalSlope_lt_top

/-- Both endpoints are excluded before representing absolute positive degree
by a real value, including in rank zero. -/
theorem exists_absolutePositiveDegree_eq_coe (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized] :
    ∃ c : ℝ, V.absolutePositiveDegree = (c : EReal) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S (AlgebraicClosure K)
  exact (V.scalarExtension (L := AlgebraicClosure K)).exists_positiveDegree_eq_coe

/-- Positive original rank produces a finite real absolute maximal slope. -/
theorem exists_absoluteMaximalSlope_eq_coe (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (hr : 0 < Module.finrank K V) :
    ∃ c : ℝ, V.absoluteMaximalSlope = (c : EReal) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S (AlgebraicClosure K)
  apply (V.scalarExtension (L := AlgebraicClosure K)).exists_maximalSlope_eq_coe
  simpa only [Module.finrank_baseChange] using hr

/-- The actual zero bundle has absolute positive degree zero. -/
theorem absolutePositiveDegree_eq_zero_of_finrank_eq_zero (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (hr : Module.finrank K V = 0) : V.absolutePositiveDegree = 0 := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S (AlgebraicClosure K)
  let W := V.scalarExtension (L := AlgebraicClosure K)
  apply W.positiveDegree_eq_zero_of_finrank_eq_zero
  change Module.finrank (AlgebraicClosure K) (TensorProduct K (AlgebraicClosure K) V) = 0
  simpa only [Module.finrank_baseChange] using hr

/-- There is no positive-rank algebraic-closure subspace in rank zero. -/
theorem absoluteMaximalSlope_eq_bot_of_finrank_eq_zero (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (hr : Module.finrank K V = 0) : V.absoluteMaximalSlope = ⊥ := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S (AlgebraicClosure K)
  let W := V.scalarExtension (L := AlgebraicClosure K)
  apply W.maximalSlope_eq_bot_of_finrank_eq_zero
  change Module.finrank (AlgebraicClosure K) (TensorProduct K (AlgebraicClosure K) V) = 0
  simpa only [Module.finrank_baseChange] using hr

/-- Source 4.3.67's positive-degree inequality for the actual closure bundle. -/
theorem positiveDegree_le_absolutePositiveDegree (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized] :
    V.positiveDegree ≤ V.absolutePositiveDegree :=
  V.positiveDegree_le_scalarExtension_of_isAlgClosed (L := AlgebraicClosure K)

/-- Source 4.3.67's maximal-slope inequality, including the zero convention. -/
theorem maximalSlope_le_absoluteMaximalSlope (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized] :
    V.maximalSlope ≤ V.absoluteMaximalSlope :=
  V.maximalSlope_le_scalarExtension_of_isAlgClosed (L := AlgebraicClosure K)

/-- Every actual original restricted degree is bounded by absolute positive degree. -/
theorem degree_restrict_le_absolutePositiveDegree (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized] (A : Submodule K V) :
    ((V.restrictOfMeasurableBase A).degree : EReal) ≤
      V.absolutePositiveDegree :=
  (V.degree_restrict_le_positiveDegree A).trans
    (V.positiveDegree_le_absolutePositiveDegree)

end ArakelovGeometry.AdelicVectorBundle
