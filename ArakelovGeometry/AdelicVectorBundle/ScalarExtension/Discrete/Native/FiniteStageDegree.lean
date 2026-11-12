/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Countable
public import ArakelovGeometry.AdelicVectorBundle.Degree.Determinant.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Discrete.Native.Degree
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Discrete.Quotient
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Discrete.Restriction

import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.DegreeDeterminant
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.FiniteStage.RestrictionIsometry
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.QuotientEquiv
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Tower.DeterminantDegree
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual native finite-stage degrees over a countable discrete base

Produced native determinant measurability and canonical completed isometries
identify actual native degrees with the genuine finite-stage degrees, without
assuming target common density or a discrete target place space.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
universe u v wL wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

variable {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] [IsAlgClosed L]

/-- Actual native restricted determinant degree has the genuine finite-stage
degree, with both determinant measurabilities produced and no target regularity. -/
theorem degree_nativeRestrictionOfCountableDiscreteBase_finiteStage [S.IsProper]
    (V : AdelicVectorBundle S E)
    [hN : S.IsArchimedeanNormalized]
    (F : AdelicStructure.FiniteIntermediateField K L) (hi : ∃ a : F, a ^ 2 = -1)
    (B : Submodule F (F ⊗[K] E)) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    let : Countable (S.algebraicExtension F).Ω :=
      AdelicStructure.ParameterSpaceExtension.countable_of_finiteDimensional (S := S) (L := F)
    let : DiscreteMeasurableSpace (S.algebraicExtension F).Ω :=
      AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
        (S := S) (L := F)
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    let A := (B.baseChange L).map c.toLinearMap
    let R := V.scalarExtensionRestrictionOfCountableDiscreteBase (L := L) A
    R.degreeOfMeasurableDeterminant
        (hdet :=
          (V.toNormFamily.scalarExtension_restrict_determinant_isMeasurable_of_countable_discrete
          A)) (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
    ((V.scalarExtensionOfCountableDiscreteBase (L := F)).restrictOfMeasurableBase
      B).degree
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F))⟩) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
  let : Countable (S.algebraicExtension F).Ω :=
    AdelicStructure.ParameterSpaceExtension.countable_of_finiteDimensional (S := S) (L := F)
  let : DiscreteMeasurableSpace (S.algebraicExtension F).Ω :=
    AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
      (S := S) (L := F)
  let hFN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := F)
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
  let hTN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) (hS := ⟨hFN⟩)
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
  let A := (B.baseChange L).map c.toLinearMap
  let e := (Submodule.toBaseChange.toLinearEquiv L B).trans (c.submoduleMap (B.baseChange L))
  let B₀ := (V.scalarExtensionOfCountableDiscreteBase (L := F)).restrictOfMeasurableBase
    B
  let W := B₀.scalarExtensionOfCountableDiscreteBase (L := L) (hN := ⟨hFN⟩)
  let R := V.scalarExtensionRestrictionOfCountableDiscreteBase (L := L) A
  let hdetW := B₀.scalarExtensionOfCountableDiscreteBase_determinant_isMeasurable (L := L)
  have hdetR : R.toNormFamily.determinant.IsMeasurable :=
    V.toNormFamily.scalarExtension_restrict_determinant_isMeasurable_of_countable_discrete A
  change R.degreeOfMeasurableDeterminant (hdet := hdetR) (hN := ⟨hLN⟩) = B₀.degree (hN := ⟨hFN⟩)
  exact (degreeOfMeasurableDeterminant_eq_of_tower_isometry F.toIntermediateField W R e
    (hdetW := hdetW) (hdetR := hdetR) (hND := ⟨hLN⟩) (hNT := ⟨hTN⟩) (fun x z ↦
      V.toNormFamily.scalarExtension_restrict_finiteStage_norm_eq F hi B x z)).trans
        (B₀.degreeOfMeasurableDeterminant_scalarExtensionOfCountableDiscreteBase (hN := ⟨hFN⟩))

/-- Actual native quotient determinant degree has the genuine finite-stage
degree, with both determinant measurabilities produced and no target regularity. -/
theorem degree_nativeQuotientOfCountableDiscreteBase_finiteStage [S.IsProper]
    (V : AdelicVectorBundle S E)
    [hN : S.IsArchimedeanNormalized]
    (F : AdelicStructure.FiniteIntermediateField K L) (hi : ∃ a : F, a ^ 2 = -1)
    (B : Submodule F (F ⊗[K] E)) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    let : Countable (S.algebraicExtension F).Ω :=
      AdelicStructure.ParameterSpaceExtension.countable_of_finiteDimensional (S := S) (L := F)
    let : DiscreteMeasurableSpace (S.algebraicExtension F).Ω :=
      AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
        (S := S) (L := F)
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    let A := (B.baseChange L).map c.toLinearMap
    let R := V.scalarExtensionQuotientOfCountableDiscreteBase (L := L) A
    R.degreeOfMeasurableDeterminant
        (hdet :=
          (V.toNormFamily.scalarExtension_quotient_determinant_isMeasurable_of_countable_discrete
          A)) (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
    ((V.scalarExtensionOfCountableDiscreteBase (L := F)).quotientOfMeasurableBase
      B).degree
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F))⟩) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
  let : Countable (S.algebraicExtension F).Ω :=
    AdelicStructure.ParameterSpaceExtension.countable_of_finiteDimensional (S := S) (L := F)
  let : DiscreteMeasurableSpace (S.algebraicExtension F).Ω :=
    AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
      (S := S) (L := F)
  let hFN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := F)
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
  let hTN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) (hS := ⟨hFN⟩)
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
  let A := (B.baseChange L).map c.toLinearMap
  let e := finiteStageQuotientEquiv (L := L) F B
  let B₀ := (V.scalarExtensionOfCountableDiscreteBase (L := F)).quotientOfMeasurableBase
    B
  let W := B₀.scalarExtensionOfCountableDiscreteBase (L := L) (hN := ⟨hFN⟩)
  let R := V.scalarExtensionQuotientOfCountableDiscreteBase (L := L) A
  let hdetW := B₀.scalarExtensionOfCountableDiscreteBase_determinant_isMeasurable (L := L)
  have hdetR : R.toNormFamily.determinant.IsMeasurable :=
    V.toNormFamily.scalarExtension_quotient_determinant_isMeasurable_of_countable_discrete A
  change R.degreeOfMeasurableDeterminant (hdet := hdetR) (hN := ⟨hLN⟩) = B₀.degree (hN := ⟨hFN⟩)
  exact (degreeOfMeasurableDeterminant_eq_of_tower_isometry F.toIntermediateField W R e
    (hdetW := hdetW) (hdetR := hdetR) (hND := ⟨hLN⟩) (hNT := ⟨hTN⟩) (fun x z ↦
      V.toNormFamily.scalarExtension_quotient_finiteStage_equiv_norm_eq F hi B x z)).trans
        (B₀.degreeOfMeasurableDeterminant_scalarExtensionOfCountableDiscreteBase (hN := ⟨hFN⟩))

end ArakelovGeometry.AdelicVectorBundle
