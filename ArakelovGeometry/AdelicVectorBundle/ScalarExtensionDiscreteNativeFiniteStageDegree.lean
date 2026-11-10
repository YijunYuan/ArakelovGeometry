/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDiscreteNativeDegree

/-!
# Actual native finite-stage degrees over a countable discrete base

Produced native determinant measurability and canonical completed isometries
identify actual native degrees with the genuine finite-stage degrees, without
assuming target common density or a discrete target place space.
-/

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
universe u v wL wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

private theorem discreteNative_degree_tower [S.IsProper]
    {X : Type*} [AddCommGroup X] [Module L X] [FiniteDimensional L X]
    (V : AdelicVectorBundle (S.algebraicExtension L) X) (F : IntermediateField K L)
    (hdetD : V.toNormFamily.determinant.IsMeasurable)
    (hdetT : (V.towerPullback F).toNormFamily.determinant.IsMeasurable)
    (hND : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
    (hNT : ∀ x ∈ ((S.algebraicExtension F).algebraicExtension L).Ωinf,
      IsRCLikeNormedField (((S.algebraicExtension F).algebraicExtension L).ϕ x).Completion) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
    (V.towerPullback F).degreeOfMeasurableDeterminant hdetT hNT =
      V.degreeOfMeasurableDeterminant hdetD hND := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
  change (V.towerPullback F).degreeOfMeasurableDeterminant hdetT hNT =
    V.degreeOfMeasurableDeterminant hdetD hND
  let s := (V.determinant hdetD hND).lineGenerator (V.determinant_isLine hdetD hND)
  rw [degreeOfMeasurableDeterminant_eq_neg_integral _ _ _ s,
    degreeOfMeasurableDeterminant_eq_neg_integral _ _ _ s]
  change -(∫ x, (V.toNormFamily.towerPullback F).determinant.logNorm s.val x
      ∂((S.algebraicExtension F).algebraicExtension L).v) =
    -(∫ x, V.toNormFamily.determinant.logNorm s.val x ∂(S.algebraicExtension L).v)
  rw [NormFamily.towerPullback_determinant, NormFamily.towerPullback_logNorm]
  exact congrArg (fun t : ℝ => -t)
    ((measurePreserving_scalarExtensionTowerPlace (S := S) F).integral_comp
      (AdelicStructure.Algebraic.towerMeasurableEquiv S F).measurableEmbedding _)

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
  let T := R.towerPullback F.toIntermediateField
  let hdetW := B₀.scalarExtensionOfCountableDiscreteBase_determinant_isMeasurable (L := L) hFN
  have hdetR : R.toNormFamily.determinant.IsMeasurable :=
    V.toNormFamily.scalarExtension_restrict_determinant_isMeasurable_of_countable_discrete hN A
  have hdetT : T.toNormFamily.determinant.IsMeasurable := by
    change (R.toNormFamily.towerPullback F.toIntermediateField).determinant.IsMeasurable
    rw [NormFamily.towerPullback_determinant]
    exact hdetR.towerPullback F.toIntermediateField
  change R.degreeOfMeasurableDeterminant hdetR hLN = B₀.degree (Or.inl inferInstance) hFN
  have he : W.degreeOfMeasurableDeterminant hdetW hTN =
      T.degreeOfMeasurableDeterminant hdetT hTN :=
    W.degreeOfMeasurableDeterminant_eq_of_completed_isometry T e hdetW hTN
      (fun x z => V.toNormFamily.scalarExtension_restrict_finiteStage_norm_eq hN F hi B x z)
  have ht : T.degreeOfMeasurableDeterminant hdetT hTN =
      R.degreeOfMeasurableDeterminant hdetR hLN :=
    discreteNative_degree_tower R F.toIntermediateField hdetR hdetT hLN hTN
  exact ht.symm.trans (he.symm.trans
    (B₀.degreeOfMeasurableDeterminant_scalarExtensionOfCountableDiscreteBase hFN))

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
  let e := finiteStageQuotientEquiv F B
  let B₀ := (V.scalarExtensionOfCountableDiscreteBase (L := F) hN).quotientOfMeasurableBase
    B (Or.inl inferInstance)
  let W := B₀.scalarExtensionOfCountableDiscreteBase (L := L) hFN
  let R := V.scalarExtensionQuotientOfCountableDiscreteBase (L := L) hN A
  let T := R.towerPullback F.toIntermediateField
  let hdetW := B₀.scalarExtensionOfCountableDiscreteBase_determinant_isMeasurable (L := L) hFN
  have hdetR : R.toNormFamily.determinant.IsMeasurable :=
    V.toNormFamily.scalarExtension_quotient_determinant_isMeasurable_of_countable_discrete hN A
  have hdetT : T.toNormFamily.determinant.IsMeasurable := by
    change (R.toNormFamily.towerPullback F.toIntermediateField).determinant.IsMeasurable
    rw [NormFamily.towerPullback_determinant]
    exact hdetR.towerPullback F.toIntermediateField
  change R.degreeOfMeasurableDeterminant hdetR hLN = B₀.degree (Or.inl inferInstance) hFN
  have he : W.degreeOfMeasurableDeterminant hdetW hTN =
      T.degreeOfMeasurableDeterminant hdetT hTN :=
    W.degreeOfMeasurableDeterminant_eq_of_completed_isometry T e hdetW hTN
      (fun x z => V.toNormFamily.scalarExtension_quotient_finiteStage_equiv_norm_eq hN F hi B x z)
  have ht : T.degreeOfMeasurableDeterminant hdetT hTN =
      R.degreeOfMeasurableDeterminant hdetR hLN :=
    discreteNative_degree_tower R F.toIntermediateField hdetR hdetT hLN hTN
  exact ht.symm.trans (he.symm.trans
    (B₀.degreeOfMeasurableDeterminant_scalarExtensionOfCountableDiscreteBase hFN))

end ArakelovGeometry.AdelicVectorBundle
