/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Countable
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Algebraic.ClosureApproximation
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Bundle

import ArakelovGeometry.AdelicVectorBundle.Degree.Isometry
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Archimedean
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.DegreeDeterminant
import Mathlib.CategoryTheory.Category.Init

/-!
# Degrees of actual scalar-extended subspaces

Common countable density in an algebraically closed algebraic target is
produced by polynomial approximation. The canonical ordinary extended bundle
therefore has its usual degree, which the actual determinant transport preserves.
If the base contains a square root of minus one and the original finite-place
norms are ultrametric, every native base-changed subspace has the original
restricted degree: the canonical tensor equivalence is isometric on every
completed vector, not merely on rational pure tensors.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w wL

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]

/-- The usual vector degree of the actual ordinary extension to an algebraic
closure equals the original degree; target common density is proved. -/
theorem degree_scalarExtension_of_isAlgClosed [S.IsProper]
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.scalarExtension (L := L)).degree
      (hS := ⟨(Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))⟩)
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
    V.degree := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  exact (degreeOfMeasurableDeterminant_eq_degree _
    (hdet := (V.scalarExtension_determinant_isMeasurable))
    (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩)).symm.trans
      (V.degreeOfMeasurableDeterminant_scalarExtension)

/-- Native restriction after ordinary scalar extension has the original
restricted degree under the actual completed tensor equivalence. -/
theorem degree_restrict_scalarExtension_of_sqrt_neg_one [S.IsProper]
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsUltrametric] (hi : ∃ a : K, a ^ 2 = -1)
    (A : Submodule K E) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    ((V.scalarExtension (L := L)).restrictOfMeasurableBase
      (A.baseChange L) (hS := ⟨(Or.inr (hcount.algebraicExtension_of_isAlgClosed
          (L := L)))⟩)).degree
      (hS := ⟨(Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))⟩)
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
    (V.restrictOfMeasurableBase A).degree := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let hL : DiscreteMeasurableSpace (S.algebraicExtension L).Ω ∨
      (S.algebraicExtension L).HasCommonCountableDenseSubfield :=
    Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
  let W := (V.restrictOfMeasurableBase A).scalarExtension (L := L)
  let R := (V.scalarExtension (L := L)).restrictOfMeasurableBase (A.baseChange L) (hS := ⟨hL⟩)
  have he : W.degree (hS := ⟨hL⟩) (hN := ⟨hLN⟩) = R.degree (hS := ⟨hL⟩) (hN := ⟨hLN⟩) :=
    W.degree_eq_of_completed_isometry R (Submodule.toBaseChange.toLinearEquiv L A)
      (hS := ⟨hL⟩) (hN := ⟨hLN⟩) (fun x z =>
          V.toNormFamily.scalarExtension_restrict_norm_eq_of_sqrt_neg_one
         hi A x z)
  exact he.symm.trans
    ((V.restrictOfMeasurableBase A).degree_scalarExtension_of_isAlgClosed
      )

/-- The native base-changed subbundle has precisely the original restricted
rank, through the same canonical tensor equivalence, including rank zero. -/
theorem rank_restrict_scalarExtension
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized] (A : Submodule K E) :
    ((V.scalarExtension (L := L)).restrictOfMeasurableBase
      (A.baseChange L) (hS := ⟨(Or.inr (hcount.algebraicExtension_of_isAlgClosed
          (L := L)))⟩)).rank =
    (V.restrictOfMeasurableBase A).rank := by
  change Module.finrank L (A.baseChange L) = Module.finrank K A
  exact (Submodule.toBaseChange.toLinearEquiv L A).finrank_eq.symm.trans
    Module.finrank_baseChange

end ArakelovGeometry.AdelicVectorBundle
