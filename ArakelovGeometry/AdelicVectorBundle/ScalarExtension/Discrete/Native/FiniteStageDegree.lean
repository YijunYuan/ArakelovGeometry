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
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
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
    let R := V.scalarExtensionRestrictionOfCountableDiscreteBase (L := L) hN A
    R.degreeOfMeasurableDeterminant
        (V.toNormFamily.scalarExtension_restrict_determinant_isMeasurable_of_countable_discrete
          hN A) (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) =
    ((V.scalarExtensionOfCountableDiscreteBase (L := F) hN).restrictOfMeasurableBase
      B (Or.inl inferInstance)).degree (Or.inl inferInstance)
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
  let : Countable (S.algebraicExtension F).Ω :=
    AdelicStructure.ParameterSpaceExtension.countable_of_finiteDimensional (S := S) (L := F)
  let : DiscreteMeasurableSpace (S.algebraicExtension F).Ω :=
    AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
      (S := S) (L := F)
  let hFN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
  let hTN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hFN
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
  let A := (B.baseChange L).map c.toLinearMap
  let e := (Submodule.toBaseChange.toLinearEquiv L B).trans (c.submoduleMap (B.baseChange L))
  let B₀ := (V.scalarExtensionOfCountableDiscreteBase (L := F) hN).restrictOfMeasurableBase
    B (Or.inl inferInstance)
  let W := B₀.scalarExtensionOfCountableDiscreteBase (L := L) hFN
  let R := V.scalarExtensionRestrictionOfCountableDiscreteBase (L := L) hN A
  let hdetW := B₀.scalarExtensionOfCountableDiscreteBase_determinant_isMeasurable (L := L) hFN
  have hdetR : R.toNormFamily.determinant.IsMeasurable :=
    V.toNormFamily.scalarExtension_restrict_determinant_isMeasurable_of_countable_discrete hN A
  change R.degreeOfMeasurableDeterminant hdetR hLN = B₀.degree (Or.inl inferInstance) hFN
  exact (degreeOfMeasurableDeterminant_eq_of_tower_isometry F.toIntermediateField W R e
    hdetW hdetR hLN hTN (fun x z ↦
      V.toNormFamily.scalarExtension_restrict_finiteStage_norm_eq hN F hi B x z)).trans
        (B₀.degreeOfMeasurableDeterminant_scalarExtensionOfCountableDiscreteBase hFN)

/-- Actual native quotient determinant degree has the genuine finite-stage
degree, with both determinant measurabilities produced and no target regularity. -/
theorem degree_nativeQuotientOfCountableDiscreteBase_finiteStage [S.IsProper]
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
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
    let R := V.scalarExtensionQuotientOfCountableDiscreteBase (L := L) hN A
    R.degreeOfMeasurableDeterminant
        (V.toNormFamily.scalarExtension_quotient_determinant_isMeasurable_of_countable_discrete
          hN A) (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) =
    ((V.scalarExtensionOfCountableDiscreteBase (L := F) hN).quotientOfMeasurableBase
      B (Or.inl inferInstance)).degree (Or.inl inferInstance)
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
  let : Countable (S.algebraicExtension F).Ω :=
    AdelicStructure.ParameterSpaceExtension.countable_of_finiteDimensional (S := S) (L := F)
  let : DiscreteMeasurableSpace (S.algebraicExtension F).Ω :=
    AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
      (S := S) (L := F)
  let hFN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
  let hTN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hFN
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
  let A := (B.baseChange L).map c.toLinearMap
  let e := finiteStageQuotientEquiv (L := L) F B
  let B₀ := (V.scalarExtensionOfCountableDiscreteBase (L := F) hN).quotientOfMeasurableBase
    B (Or.inl inferInstance)
  let W := B₀.scalarExtensionOfCountableDiscreteBase (L := L) hFN
  let R := V.scalarExtensionQuotientOfCountableDiscreteBase (L := L) hN A
  let hdetW := B₀.scalarExtensionOfCountableDiscreteBase_determinant_isMeasurable (L := L) hFN
  have hdetR : R.toNormFamily.determinant.IsMeasurable :=
    V.toNormFamily.scalarExtension_quotient_determinant_isMeasurable_of_countable_discrete hN A
  change R.degreeOfMeasurableDeterminant hdetR hLN = B₀.degree (Or.inl inferInstance) hFN
  exact (degreeOfMeasurableDeterminant_eq_of_tower_isometry F.toIntermediateField W R e
    hdetW hdetR hLN hTN (fun x z ↦
      V.toNormFamily.scalarExtension_quotient_finiteStage_equiv_norm_eq hN F hi B x z)).trans
        (B₀.degreeOfMeasurableDeterminant_scalarExtensionOfCountableDiscreteBase hFN)

end ArakelovGeometry.AdelicVectorBundle
