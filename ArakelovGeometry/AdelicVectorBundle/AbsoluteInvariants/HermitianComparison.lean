/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.AbsoluteInvariants.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Algebraic.ClosureApproximation

import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.AlgebraicClosure.HNInvariants
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.AlgebraicClosure.MaximalSlope
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.AlgebraicClosure.ScalarExtensionDegree
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Hermitian.OrdinaryComparison
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Slopes
import Mathlib.CategoryTheory.Category.Init
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Actual ordinary absolute invariants of Hermitian bundles on a common-density base

Genuine ordinary native restrictions of original subspaces preserve degree and
mean. For perfect K, the actual closed Hermitian HN invariants and same-fibre
norm domination bound ordinary invariants above; ordinary monotonicity gives
the reverse bound. The canonical ordinary absolute definitions then agree
with the original positive degree and maximal slope in every rank.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local instance hermitianOrdinaryAbsoluteProper : (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- The actual ordinary native restriction to an original extended subspace
preserves genuine degree. This does not require a perfect original field. -/
theorem degree_restrict_scalarExtension_of_isHermitian_of_isAlgClosed
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (A : Submodule K V) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let P := V.scalarExtension (L := L)
    (P.restrictOfNormMeasurability (A.baseChange L) (hS := ⟨hLS⟩)).degree (hS := ⟨hLS⟩)
      (hN := ⟨hLN⟩) =
      (V.restrictOfNormMeasurability A).degree := by
  intro hLN hLS P
  apply le_antisymm
  · exact (V.degree_restrict_scalarExtension_le_hermitianScalarExtension_of_isAlgClosed
       (A.baseChange L)).trans_eq
        (V.degree_restrict_hermitianScalarExtension_of_isAlgClosed A)
  · exact V.degree_le_restrict_scalarExtension A

/-- Actual ordinary native original subspaces preserve real mean in every
rank by genuine degree equality and the canonical tensor subspace rank. -/
theorem slope_restrict_scalarExtension_of_isHermitian_of_isAlgClosed
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (A : Submodule K V) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let P := V.scalarExtension (L := L)
    (P.restrictOfNormMeasurability (A.baseChange L) (hS := ⟨hLS⟩)).slope (hS := ⟨hLS⟩)
      (hN := ⟨hLN⟩) =
      (V.restrictOfNormMeasurability A).slope := by
  intro hLN hLS P
  have hr : Module.finrank L (A.baseChange L) = Module.finrank K A :=
    (Submodule.toBaseChange.toLinearEquiv L A).finrank_eq.symm.trans Module.finrank_baseChange
  dsimp only [slope]
  rw [V.degree_restrict_scalarExtension_of_isHermitian_of_isAlgClosed A, hr]

section PerfectBase

variable [PerfectField K]

/-- The actual ordinary extension to any algebraic closed field preserves
canonical positive degree over a perfect common-density original base. -/
theorem positiveDegree_scalarExtension_of_isHermitian_of_isAlgClosed
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let P := V.scalarExtension (L := L)
    P.positiveDegree (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) = V.positiveDegree := by
  intro hLN hLS P
  exact le_antisymm
    ((V.positiveDegree_scalarExtension_le_hermitianScalarExtension_of_isAlgClosed
      ).trans_eq
        (V.positiveDegree_hermitianScalarExtension_of_isAlgClosed))
    (V.positiveDegree_le_scalarExtension_of_isAlgClosed)

/-- The actual ordinary closed maximal slope is the original maximum over
a perfect common-density base, including the empty rank-zero supremum. -/
theorem maximalSlope_scalarExtension_of_isHermitian_of_isAlgClosed
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let P := V.scalarExtension (L := L)
    P.maximalSlope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) = V.maximalSlope := by
  intro hLN hLS P
  exact le_antisymm
    ((V.maximalSlope_scalarExtension_le_hermitianScalarExtension_of_isAlgClosed
      ).trans_eq
        (V.maximalSlope_hermitianScalarExtension_of_isAlgClosed))
    (V.maximalSlope_le_scalarExtension_of_isAlgClosed)

/-- The canonical actual ordinary absolute positive degree equals original
positive degree for Hermitian bundles on a perfect common-density base. -/
theorem absolutePositiveDegree_eq_of_isHermitian
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] :
    V.absolutePositiveDegree = V.positiveDegree :=
  V.positiveDegree_scalarExtension_of_isHermitian_of_isAlgClosed
    (L := AlgebraicClosure K)

/-- The canonical actual ordinary absolute maximum equals the genuine original
maximum for Hermitian bundles on a perfect common-density base, in all ranks. -/
theorem absoluteMaximalSlope_eq_of_isHermitian
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] :
    V.absoluteMaximalSlope = V.maximalSlope :=
  V.maximalSlope_scalarExtension_of_isHermitian_of_isAlgClosed
    (L := AlgebraicClosure K)

end PerfectBase

end ArakelovGeometry.AdelicVectorBundle
