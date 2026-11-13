/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Determinant.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Discrete.Bundle
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.HermitianComparison.DeterminantDegree

import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.HermitianComparison.Degree
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual algebraic scalar-extension vector degree

The completed determinant isometries produce measurability of the actual
extended determinant. Degree defined by that measurable canonical determinant
therefore commutes with every algebraic extension for the actual ordinary
common-density and countable-discrete bundles, and for the actual Hermitian
common-density bundle. No extending discrete-or-common-density hypothesis is
needed; the existing finite-extension degree agrees by the canonical bridge.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u v w wL

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The ordinary common-density bundle's actual determinant is measurable
by the completed determinant isometry and original determinant measurability. -/
instance scalarExtension_determinant_isMeasurable (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [S.IsArchimedeanNormalized] :
    (V.scalarExtension (L := L)).toNormFamily.determinant.IsMeasurable :=
  (V.isMeasurable.determinant_of_discrete_or_countable).determinant_scalarExtension

/-- The actual ordinary common-density extended vector bundle preserves
degree for every algebraic extension, using produced determinant measurability. -/
theorem degreeOfMeasurableDeterminant_scalarExtension [S.IsProper]
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.scalarExtension (L := L)).degreeOfMeasurableDeterminant
      (hdet := (V.scalarExtension_determinant_isMeasurable))
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
        V.degree := by
  intro hp
  let := hp
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
  let W := V.scalarExtension (L := L)
  let hdet := V.scalarExtension_determinant_isMeasurable (L := L)
  have hdegree : (W.determinant (hm := hdet) (hS := ⟨hLN⟩)).lineDegree (hV := (W.determinant_isLine
      (hm := hdet) (hS := ⟨hLN⟩))) =
      (V.scalarExtensionDeterminant (L := L)).lineDegree
        (hV := (V.scalarExtensionDeterminant_isLine)) := by
    apply lineDegree_eq_of_norm_rational_eq _ _ (LinearEquiv.refl L _)
    intro x s
    rfl
  exact hdegree.trans (V.lineDegree_scalarExtensionDeterminant (L := L))

section CountableDiscrete

variable [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]

/-- The countable-discrete bundle's actual determinant is measurable via
the completed determinant isometry and original discrete measurability. -/
instance scalarExtensionOfCountableDiscreteBase_determinant_isMeasurable
    (V : AdelicVectorBundle S)
    [S.IsArchimedeanNormalized] :
    (V.scalarExtensionOfCountableDiscreteBase (L := L)).toNormFamily.determinant.IsMeasurable :=
  (V.isMeasurable.determinant_of_discrete_or_countable
   ).determinant_scalarExtension

/-- The actual countable-discrete extended vector bundle preserves degree
for every algebraic extension, without extending discreteness as a premise. -/
theorem degreeOfMeasurableDeterminant_scalarExtensionOfCountableDiscreteBase [S.IsProper]
    (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.scalarExtensionOfCountableDiscreteBase (L := L)).degreeOfMeasurableDeterminant
      (hdet := (V.scalarExtensionOfCountableDiscreteBase_determinant_isMeasurable))
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
        V.degree := by
  intro hp
  let := hp
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
  let W := V.scalarExtensionOfCountableDiscreteBase (L := L)
  let hdet := V.scalarExtensionOfCountableDiscreteBase_determinant_isMeasurable (L := L)
  have hdegree : (W.determinant (hm := hdet) (hS := ⟨hLN⟩)).lineDegree (hV := (W.determinant_isLine
      (hm := hdet) (hS := ⟨hLN⟩))) =
      (V.scalarExtensionDeterminant (L := L)).lineDegree
        (hV := (V.scalarExtensionDeterminant_isLine)) := by
    apply lineDegree_eq_of_norm_rational_eq _ _ (LinearEquiv.refl L _)
    intro x s
    rfl
  exact hdegree.trans (V.lineDegree_scalarExtensionDeterminant (L := L))

end CountableDiscrete

/-- The actual Hermitian common-density bundle's determinant is measurable
through the proved Hermitian determinant isometry and original measurability. -/
instance hermitianScalarExtension_determinant_isMeasurable (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hS : S.IsArchimedeanNormalized]
    [hL : (S.algebraicExtension L).IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] :
    (V.hermitianScalarExtension (L := L)).toNormFamily.determinant.IsMeasurable :=
  NormFamily.IsMeasurable.determinant_hermitianScalarExtension V.toNormFamily
    (V.isMeasurable.determinant_of_discrete_or_countable)

/-- The actual Hermitian common-density extended vector bundle preserves
degree for every algebraic extension, with actual determinant measurability produced. -/
theorem degreeOfMeasurableDeterminant_hermitianScalarExtension [S.IsProper]
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hS : S.IsArchimedeanNormalized]
    [hL : (S.algebraicExtension L).IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.hermitianScalarExtension (L := L)).degreeOfMeasurableDeterminant
      (hdet := (V.hermitianScalarExtension_determinant_isMeasurable)) =
        V.degree := by
  intro hp
  let := hp
  let W := V.hermitianScalarExtension (L := L)
  let hdet := V.hermitianScalarExtension_determinant_isMeasurable (L := L)
  have hdegree : (W.determinant (hm := hdet)).lineDegree (hV := (W.determinant_isLine
      (hm := hdet))) =
      (V.hermitianScalarExtensionDeterminant (L := L)).lineDegree
        (hV := (V.hermitianScalarExtensionDeterminant_isLine)) := by
    apply lineDegree_eq_of_norm_rational_eq _ _ (LinearEquiv.refl L _)
    intro x s
    rfl
  exact hdegree.trans
    (V.lineDegree_hermitianScalarExtensionDeterminant (L := L))

/-- Over finite extensions, the produced-determinant ordinary degree equals
the existing vector degree with its proved target common-density context. -/
theorem degreeOfMeasurableDeterminant_scalarExtension_eq_degree
    [S.IsProper] [FiniteDimensional K L] (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.scalarExtension (L := L)).degreeOfMeasurableDeterminant
      (hdet := (V.scalarExtension_determinant_isMeasurable))
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
    (V.scalarExtension (L := L)).degree
      (hS := ⟨(Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L)))⟩)
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) := by
  intro hp
  let := hp
  exact degreeOfMeasurableDeterminant_eq_degree _

/-- Over finite extensions, the produced-determinant discrete degree equals
the existing vector degree with its proved target discrete context. -/
theorem degreeOfMeasurableDeterminant_scalarExtensionOfCountableDiscreteBase_eq_degree
    [S.IsProper] [FiniteDimensional K L] [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]
    (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.scalarExtensionOfCountableDiscreteBase (L := L)).degreeOfMeasurableDeterminant
      (hdet := (V.scalarExtensionOfCountableDiscreteBase_determinant_isMeasurable))
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
    (V.scalarExtensionOfCountableDiscreteBase (L := L)).degree
      (hS :=
        ⟨(Or.inl (AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
        (S := S) (L := L)))⟩)
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) := by
  intro hp
  let := hp
  exact degreeOfMeasurableDeterminant_eq_degree _

/-- Over finite extensions, the produced-determinant Hermitian degree equals
the existing vector degree with its proved target common-density context. -/
theorem degreeOfMeasurableDeterminant_hermitianScalarExtension_eq_degree
    [S.IsProper] [FiniteDimensional K L] (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hS : S.IsArchimedeanNormalized]
    [hL : (S.algebraicExtension L).IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.hermitianScalarExtension (L := L)).degreeOfMeasurableDeterminant
      (hdet := (V.hermitianScalarExtension_determinant_isMeasurable)) =
    (V.hermitianScalarExtension (L := L)).degree
      (hS := ⟨(Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L)))⟩) := by
  intro hp
  let := hp
  exact degreeOfMeasurableDeterminant_eq_degree _

end

end ArakelovGeometry.AdelicVectorBundle
