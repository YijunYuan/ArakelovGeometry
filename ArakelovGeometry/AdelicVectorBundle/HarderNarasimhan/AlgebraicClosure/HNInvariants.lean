/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.Basic
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Algebraic.ClosureApproximation
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.HermitianComparison.DeterminantDegree

import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.Isometry
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.AlgebraicClosure.HNFactorScalarExtension
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.AlgebraicClosure.ScalarExtensionDegree
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.PositiveDegree
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Hermitian.Quotient
import Mathlib.CategoryTheory.Category.Init
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Actual closed Hermitian ordered slopes and positive degree

Preserved genuine real HN filtration ranks identify every ordered rank slope.
Its actual threshold-zero restriction attains positive degree, whose native
closed restricted degree is preserved. Native quotient positive degree follows
from the canonical completed quotient isometry.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [PerfectField K] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
  {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local instance hermitianClosedHNInvariantsProper : (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- Every actual ordered rank slope is preserved under closed Hermitian
extension, using the produced canonical rank correspondence. -/
theorem hermitianHNOrderedSlope_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (j : Fin (Module.finrank K E)) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    let hLH := V.hermitianScalarExtension_isHermitian (hL := ⟨hLN⟩)
    W.hermitianHNOrderedSlope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH)
        (Fin.cast (Module.finrank_baseChange (R := L) (S := K) (M' := E)).symm j) =
      V.hermitianHNOrderedSlope j := by
  intro hLN hLS W hLH
  change W.toNormFamily.IsHermitian (hS := ⟨hLN⟩) at hLH
  let jL : Fin (Module.finrank L (L ⊗[K] E)) :=
    Fin.cast (Module.finrank_baseChange (R := L) (S := K) (M' := E)).symm j
  have hf (t : ℝ) : Module.finrank L (W.hermitianHNFiltration (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
      (hV := hLH) t) =
      Module.finrank K (V.hermitianHNFiltration t) := by
    rw [← V.hermitianHNFiltration_baseChange_hermitianScalarExtension_of_isAlgClosed
       t]
    exact (Submodule.toBaseChange.toLinearEquiv L
      (V.hermitianHNFiltration t)).finrank_eq.symm.trans
        Module.finrank_baseChange
  have hi (t : ℝ) : t ≤ W.hermitianHNOrderedSlope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) jL ↔
      t ≤ V.hermitianHNOrderedSlope j := by
    rw [W.le_hermitianHNOrderedSlope_iff_lt_filtration_finrank (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
        (hV := hLH) t jL,
      V.le_hermitianHNOrderedSlope_iff_lt_filtration_finrank t j,
      hf t]
    rfl
  exact le_antisymm ((hi _).mp le_rfl) ((hi _).mpr le_rfl)

/-- The actual closed Hermitian extension preserves canonical positive degree,
attained by the genuine restriction to its constructed threshold-zero HN term. -/
theorem positiveDegree_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    W.positiveDegree (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) = V.positiveDegree := by
  intro hLN hLS W
  let hLH := V.hermitianScalarExtension_isHermitian (hL := ⟨hLN⟩)
  change W.toNormFamily.IsHermitian (hS := ⟨hLN⟩) at hLH
  calc
    _ = ((W.restrictOfMeasurableBase (W.hermitianHNFiltration (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
        (hV := hLH) 0) (hS := ⟨hLS⟩)).degree
        (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) : EReal) :=
      W.positiveDegree_eq_degree_restrict_hermitianHNFiltration_zero (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
          (hV := hLH)
    _ = ((W.restrictOfMeasurableBase
        ((V.hermitianHNFiltration 0).baseChange L) (hS := ⟨hLS⟩)).degree
          (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) : EReal) :=
      congrArg (fun U : Submodule L (L ⊗[K] E) ↦
        ((W.restrictOfMeasurableBase U (hS := ⟨hLS⟩)).degree (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) : EReal))
          (V.hermitianHNFiltration_baseChange_hermitianScalarExtension_of_isAlgClosed
             0).symm
    _ = ((V.restrictOfMeasurableBase
        (V.hermitianHNFiltration 0)).degree
          : EReal) :=
      congrArg (fun d : ℝ ↦ (d : EReal))
        (V.degree_restrict_hermitianScalarExtension_of_isAlgClosed
          (V.hermitianHNFiltration 0))
    _ = _ := (V.positiveDegree_eq_degree_restrict_hermitianHNFiltration_zero
     ).symm

/-- The genuine native quotient positive degree is preserved in every rank,
through the actual completed quotient tensor isometry. -/
theorem positiveDegree_quotient_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (U : Submodule K E) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    (W.quotientOfMeasurableBase (U.baseChange L) (hS := ⟨hLS⟩)).positiveDegree (hS := ⟨hLS⟩)
        (hN := ⟨hLN⟩) =
      (V.quotientOfMeasurableBase U).positiveDegree := by
  intro hLN hLS W
  let Q := V.quotientOfMeasurableBase U
  let Qext := Q.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩) (hV := (hH.quotient U))
  have he : Qext.positiveDegree (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) =
      (W.quotientOfMeasurableBase (U.baseChange L) (hS := ⟨hLS⟩)).positiveDegree (hS := ⟨hLS⟩)
          (hN := ⟨hLN⟩) :=
    Qext.positiveDegree_eq_of_completed_isometry _
      (tensorQuotientBaseChangeEquiv (L := L) U) (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
      (fun x z ↦ V.toNormFamily.hermitianScalarExtension_quotient_norm_eq (hLN := ⟨hLN⟩) U x z)
  exact he.symm.trans
    (Q.positiveDegree_hermitianScalarExtension_of_isAlgClosed (hH := (hH.quotient U)))

end ArakelovGeometry.AdelicVectorBundle
