/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Algebraic.ClosureApproximation
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.HermitianComparison.DeterminantDegree
public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic

import ArakelovGeometry.AdelicVectorBundle.Degree.Isometry
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Hermitian.Restriction
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual canonical Hermitian degrees over an algebraic closure

The actual extended determinant-line degree producer applies to every algebraic
extension. Produced common countable density supplies the closed target's usual
vector degree. The genuine completed restriction isometry then identifies the
native restricted degrees and real means, including rank zero.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L]
  {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local instance hermitianClosedDegreeProper : (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- The actual canonical degree of the Hermitian extension to an algebraically
closed algebraic field is the original degree. Target context is produced. -/
theorem degree_hermitianScalarExtension_of_isAlgClosed (V : AdelicVectorBundle S E)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    W.degree (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) = V.degree := by
  intro hLN hLS W
  have hd : (W.determinantOfMeasurableBase (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)).lineDegree
      (hV := (W.determinantOfMeasurableBase_isLine (hS := ⟨hLS⟩) (hN := ⟨hLN⟩))) =
      (V.hermitianScalarExtensionDeterminant (L := L) (hL := ⟨hLN⟩)).lineDegree
        (hV := (V.hermitianScalarExtensionDeterminant_isLine (hL := ⟨hLN⟩))) := by
    apply lineDegree_eq_of_norm_rational_eq _ _ (LinearEquiv.refl L _)
    intro x z
    rfl
  exact hd.trans (V.lineDegree_hermitianScalarExtensionDeterminant
    (L := L) (hL := ⟨hLN⟩))

/-- Genuine closed Hermitian extension preserves the ambient real mean slope,
including the existing real zero-rank convention. -/
theorem slope_hermitianScalarExtension_of_isAlgClosed (V : AdelicVectorBundle S E)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    W.slope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) = V.slope := by
  intro hLN hLS W
  dsimp only [slope]
  rw [V.degree_hermitianScalarExtension_of_isAlgClosed,
    Module.finrank_baseChange]

/-- Every native restriction after actual closed Hermitian extension has
the genuine original restricted degree, through the completed isometry. -/
theorem degree_restrict_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (U : Submodule K E) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    (W.restrictOfMeasurableBase (U.baseChange L) (hS := ⟨hLS⟩)).degree (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) =
      (V.restrictOfMeasurableBase U).degree := by
  intro hLN hLS W
  let R := V.restrictOfMeasurableBase U
  let Rext := R.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩) (hV := (hH.restrict U))
  have he : Rext.degree (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) =
      (W.restrictOfMeasurableBase (U.baseChange L) (hS := ⟨hLS⟩)).degree (hS := ⟨hLS⟩)
          (hN := ⟨hLN⟩) :=
    Rext.degree_eq_of_completed_isometry _ (Submodule.toBaseChange.toLinearEquiv L U)
      (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (fun x z ↦
          V.toNormFamily.hermitianScalarExtension_restrict_norm_eq
            (hLN := ⟨hLN⟩) U x z)
  exact he.symm.trans
    (R.degree_hermitianScalarExtension_of_isAlgClosed (hH := (hH.restrict U)))

/-- Native closed Hermitian restriction preserves the genuine original mean
slope in every rank; no square root of minus one is assumed. -/
theorem slope_restrict_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (U : Submodule K E) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    (W.restrictOfMeasurableBase (U.baseChange L) (hS := ⟨hLS⟩)).slope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) =
      (V.restrictOfMeasurableBase U).slope := by
  intro hLN hLS W
  have hr : Module.finrank L (U.baseChange L) = Module.finrank K U :=
    (Submodule.toBaseChange.toLinearEquiv L U).finrank_eq.symm.trans Module.finrank_baseChange
  dsimp only [slope]
  rw [V.degree_restrict_hermitianScalarExtension_of_isAlgClosed U, hr]

end ArakelovGeometry.AdelicVectorBundle
