/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionSlopes
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

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

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Positive degree of the actual ordinary algebraic-closure bundle. -/
def absolutePositiveDegree (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) : EReal :=
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S (AlgebraicClosure K)
  (V.scalarExtension (L := AlgebraicClosure K) hcount hN).positiveDegree
    (Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := AlgebraicClosure K)))
    (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := AlgebraicClosure K) hN)

/-- Maximal slope of the actual ordinary algebraic-closure bundle; the zero
bundle has the existing empty-supremum value `⊥`. -/
def absoluteMaximalSlope (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) : EReal :=
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S (AlgebraicClosure K)
  (V.scalarExtension (L := AlgebraicClosure K) hcount hN).maximalSlope
    (Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := AlgebraicClosure K)))
    (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := AlgebraicClosure K) hN)

/-- The actual zero subspace makes absolute positive degree nonnegative. -/
theorem absolutePositiveDegree_nonneg (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    0 ≤ V.absolutePositiveDegree hcount hN := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S (AlgebraicClosure K)
  exact (V.scalarExtension (L := AlgebraicClosure K) hcount hN).positiveDegree_nonneg _ _

/-- A produced actual rank-degree bound excludes positive infinity. -/
theorem absolutePositiveDegree_lt_top (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.absolutePositiveDegree hcount hN < ⊤ := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S (AlgebraicClosure K)
  exact (V.scalarExtension (L := AlgebraicClosure K) hcount hN).positiveDegree_lt_top _ _

/-- Absolute maximal slope has a finite upper bound in every rank. -/
theorem absoluteMaximalSlope_lt_top (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.absoluteMaximalSlope hcount hN < ⊤ := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S (AlgebraicClosure K)
  exact (V.scalarExtension (L := AlgebraicClosure K) hcount hN).maximalSlope_lt_top _ _

/-- Both endpoints are excluded before representing absolute positive degree
by a real value, including in rank zero. -/
theorem exists_absolutePositiveDegree_eq_coe (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ∃ c : ℝ, V.absolutePositiveDegree hcount hN = (c : EReal) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S (AlgebraicClosure K)
  exact (V.scalarExtension (L := AlgebraicClosure K) hcount hN).exists_positiveDegree_eq_coe _ _

/-- Positive original rank produces a finite real absolute maximal slope. -/
theorem exists_absoluteMaximalSlope_eq_coe (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : 0 < Module.finrank K E) :
    ∃ c : ℝ, V.absoluteMaximalSlope hcount hN = (c : EReal) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S (AlgebraicClosure K)
  apply (V.scalarExtension (L := AlgebraicClosure K) hcount hN).exists_maximalSlope_eq_coe _ _
  simpa only [Module.finrank_baseChange] using hr

/-- The actual zero bundle has absolute positive degree zero. -/
theorem absolutePositiveDegree_eq_zero_of_finrank_eq_zero (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : Module.finrank K E = 0) : V.absolutePositiveDegree hcount hN = 0 := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S (AlgebraicClosure K)
  let W := V.scalarExtension (L := AlgebraicClosure K) hcount hN
  apply W.positiveDegree_eq_zero_of_finrank_eq_zero _ _
  simpa only [Module.finrank_baseChange] using hr

/-- There is no positive-rank algebraic-closure subspace in rank zero. -/
theorem absoluteMaximalSlope_eq_bot_of_finrank_eq_zero (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : Module.finrank K E = 0) : V.absoluteMaximalSlope hcount hN = ⊥ := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S (AlgebraicClosure K)
  let W := V.scalarExtension (L := AlgebraicClosure K) hcount hN
  apply W.maximalSlope_eq_bot_of_finrank_eq_zero _ _
  simpa only [Module.finrank_baseChange] using hr

/-- Source 4.3.67's positive-degree inequality for the actual closure bundle. -/
theorem positiveDegree_le_absolutePositiveDegree (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.positiveDegree (Or.inr hcount) hN ≤ V.absolutePositiveDegree hcount hN :=
  V.positiveDegree_le_scalarExtension_of_isAlgClosed (L := AlgebraicClosure K) hcount hN

/-- Source 4.3.67's maximal-slope inequality, including the zero convention. -/
theorem maximalSlope_le_absoluteMaximalSlope (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.maximalSlope (Or.inr hcount) hN ≤ V.absoluteMaximalSlope hcount hN :=
  V.maximalSlope_le_scalarExtension_of_isAlgClosed (L := AlgebraicClosure K) hcount hN

/-- Every actual original restricted degree is bounded by absolute positive degree. -/
theorem degree_restrict_le_absolutePositiveDegree (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (A : Submodule K E) :
    ((V.restrictOfMeasurableBase A (Or.inr hcount)).degree (Or.inr hcount) hN : EReal) ≤
      V.absolutePositiveDegree hcount hN :=
  (V.degree_restrict_le_positiveDegree (Or.inr hcount) hN A).trans
    (V.positiveDegree_le_absolutePositiveDegree hcount hN)

end ArakelovGeometry.AdelicVectorBundle
