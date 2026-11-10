/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DegreeDeterminant
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDiscreteBundle
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionHermitianDeterminantDegree

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
theorem scalarExtension_determinant_isMeasurable (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.scalarExtension (L := L) hcount hN).toNormFamily.determinant.IsMeasurable :=
  (V.isMeasurable.determinant_of_discrete_or_countable (Or.inr hcount)).determinant_scalarExtension

/-- The actual ordinary common-density extended vector bundle preserves
degree for every algebraic extension, using produced determinant measurability. -/
theorem degreeOfMeasurableDeterminant_scalarExtension [S.IsProper]
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.scalarExtension (L := L) hcount hN).degreeOfMeasurableDeterminant
      (V.scalarExtension_determinant_isMeasurable hcount hN)
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) =
        V.degree (Or.inr hcount) hN := by
  intro hp
  let := hp
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
  let W := V.scalarExtension (L := L) hcount hN
  let hdet := V.scalarExtension_determinant_isMeasurable (L := L) hcount hN
  have hdegree : (W.determinant hdet hLN).lineDegree (W.determinant_isLine hdet hLN) =
      (V.scalarExtensionDeterminant (L := L) (Or.inr hcount) hN).lineDegree
        (V.scalarExtensionDeterminant_isLine (Or.inr hcount) hN) := by
    apply lineDegree_eq_of_norm_rational_eq _ _ _ _ (LinearEquiv.refl L _)
    intro x s
    rfl
  exact hdegree.trans (V.lineDegree_scalarExtensionDeterminant (L := L) (Or.inr hcount) hN)

section CountableDiscrete

variable [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]

/-- The countable-discrete bundle's actual determinant is measurable via
the completed determinant isometry and original discrete measurability. -/
theorem scalarExtensionOfCountableDiscreteBase_determinant_isMeasurable
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.scalarExtensionOfCountableDiscreteBase (L := L) hN).toNormFamily.determinant.IsMeasurable :=
  (V.isMeasurable.determinant_of_discrete_or_countable
    (Or.inl inferInstance)).determinant_scalarExtension

/-- The actual countable-discrete extended vector bundle preserves degree
for every algebraic extension, without extending discreteness as a premise. -/
theorem degreeOfMeasurableDeterminant_scalarExtensionOfCountableDiscreteBase [S.IsProper]
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.scalarExtensionOfCountableDiscreteBase (L := L) hN).degreeOfMeasurableDeterminant
      (V.scalarExtensionOfCountableDiscreteBase_determinant_isMeasurable hN)
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) =
        V.degree (Or.inl inferInstance) hN := by
  intro hp
  let := hp
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
  let W := V.scalarExtensionOfCountableDiscreteBase (L := L) hN
  let hdet := V.scalarExtensionOfCountableDiscreteBase_determinant_isMeasurable (L := L) hN
  have hdegree : (W.determinant hdet hLN).lineDegree (W.determinant_isLine hdet hLN) =
      (V.scalarExtensionDeterminant (L := L) (Or.inl inferInstance) hN).lineDegree
        (V.scalarExtensionDeterminant_isLine (Or.inl inferInstance) hN) := by
    apply lineDegree_eq_of_norm_rational_eq _ _ _ _ (LinearEquiv.refl L _)
    intro x s
    rfl
  exact hdegree.trans (V.lineDegree_scalarExtensionDeterminant (L := L) (Or.inl inferInstance) hN)

end CountableDiscrete

/-- The actual Hermitian common-density bundle's determinant is measurable
through the proved Hermitian determinant isometry and original measurability. -/
theorem hermitianScalarExtension_determinant_isMeasurable (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hL : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
    (hV : V.toNormFamily.IsHermitian hS) :
    (V.hermitianScalarExtension (L := L) hcount hS hL hV).toNormFamily.determinant.IsMeasurable :=
  NormFamily.IsMeasurable.determinant_hermitianScalarExtension V.toNormFamily hS hL hV
    (V.isMeasurable.determinant_of_discrete_or_countable (Or.inr hcount))

/-- The actual Hermitian common-density extended vector bundle preserves
degree for every algebraic extension, with actual determinant measurability produced. -/
theorem degreeOfMeasurableDeterminant_hermitianScalarExtension [S.IsProper]
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hL : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
    (hV : V.toNormFamily.IsHermitian hS) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.hermitianScalarExtension (L := L) hcount hS hL hV).degreeOfMeasurableDeterminant
      (V.hermitianScalarExtension_determinant_isMeasurable hcount hS hL hV) hL =
        V.degree (Or.inr hcount) hS := by
  intro hp
  let := hp
  let W := V.hermitianScalarExtension (L := L) hcount hS hL hV
  let hdet := V.hermitianScalarExtension_determinant_isMeasurable (L := L) hcount hS hL hV
  have hdegree : (W.determinant hdet hL).lineDegree (W.determinant_isLine hdet hL) =
      (V.hermitianScalarExtensionDeterminant (L := L) (Or.inr hcount) hS hL hV).lineDegree
        (V.hermitianScalarExtensionDeterminant_isLine (Or.inr hcount) hS hL hV) := by
    apply lineDegree_eq_of_norm_rational_eq _ _ _ _ (LinearEquiv.refl L _)
    intro x s
    rfl
  exact hdegree.trans
    (V.lineDegree_hermitianScalarExtensionDeterminant (L := L) (Or.inr hcount) hS hL hV)

/-- Over finite extensions, the produced-determinant ordinary degree equals
the existing vector degree with its proved target common-density context. -/
theorem degreeOfMeasurableDeterminant_scalarExtension_eq_degree
    [S.IsProper] [FiniteDimensional K L] (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.scalarExtension (L := L) hcount hN).degreeOfMeasurableDeterminant
      (V.scalarExtension_determinant_isMeasurable hcount hN)
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) =
    (V.scalarExtension (L := L) hcount hN).degree
      (Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L)))
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) := by
  intro hp
  let := hp
  exact degreeOfMeasurableDeterminant_eq_degree _ _ _ _

/-- Over finite extensions, the produced-determinant discrete degree equals
the existing vector degree with its proved target discrete context. -/
theorem degreeOfMeasurableDeterminant_scalarExtensionOfCountableDiscreteBase_eq_degree
    [S.IsProper] [FiniteDimensional K L] [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.scalarExtensionOfCountableDiscreteBase (L := L) hN).degreeOfMeasurableDeterminant
      (V.scalarExtensionOfCountableDiscreteBase_determinant_isMeasurable hN)
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) =
    (V.scalarExtensionOfCountableDiscreteBase (L := L) hN).degree
      (Or.inl (AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
        (S := S) (L := L)))
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) := by
  intro hp
  let := hp
  exact degreeOfMeasurableDeterminant_eq_degree _ _ _ _

/-- Over finite extensions, the produced-determinant Hermitian degree equals
the existing vector degree with its proved target common-density context. -/
theorem degreeOfMeasurableDeterminant_hermitianScalarExtension_eq_degree
    [S.IsProper] [FiniteDimensional K L] (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hL : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
    (hV : V.toNormFamily.IsHermitian hS) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.hermitianScalarExtension (L := L) hcount hS hL hV).degreeOfMeasurableDeterminant
      (V.hermitianScalarExtension_determinant_isMeasurable hcount hS hL hV) hL =
    (V.hermitianScalarExtension (L := L) hcount hS hL hV).degree
      (Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))) hL := by
  intro hp
  let := hp
  exact degreeOfMeasurableDeterminant_eq_degree _ _ _ _

end

end ArakelovGeometry.AdelicVectorBundle
