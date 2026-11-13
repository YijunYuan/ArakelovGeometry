/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.AbsoluteInvariants.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Algebraic.ClosureApproximation

import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Isomorphism.Invariants
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual absolute invariants computed on any algebraic closure

An algebraic-closure isomorphism is produced from the field hypotheses. The
proved actual invariant transport then compares the existing absolute objects
with ordinary extensions over the prescribed closure.
-/

@[expose] public section

noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
variable {K : Type*} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]

/-- The existing absolute positive degree is computed on any prescribed
algebraic closure using a produced field isomorphism. -/
theorem absolutePositiveDegree_eq_scalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    V.absolutePositiveDegree =
      (V.scalarExtension (L := L)).positiveDegree
        (hS := ⟨(Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))⟩)
        (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) := by
  let : IsAlgClosure K L := ⟨inferInstance, inferInstance⟩
  let σ := IsAlgClosure.equiv K (AlgebraicClosure K) L
  exact (V.positiveDegree_scalarExtension_algEquiv σ).symm

/-- The existing absolute maximal slope is computed on every algebraic
closure, including its bottom convention for the zero bundle. -/
theorem absoluteMaximalSlope_eq_scalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    V.absoluteMaximalSlope =
      (V.scalarExtension (L := L)).maximalSlope
        (hS := ⟨(Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))⟩)
        (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) := by
  let : IsAlgClosure K L := ⟨inferInstance, inferInstance⟩
  let σ := IsAlgClosure.equiv K (AlgebraicClosure K) L
  exact (V.maximalSlope_scalarExtension_algEquiv σ).symm

end ArakelovGeometry.AdelicVectorBundle
