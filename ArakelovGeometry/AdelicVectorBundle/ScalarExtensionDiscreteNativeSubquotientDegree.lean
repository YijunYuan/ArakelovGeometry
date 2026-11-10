/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionNativeSubquotientFiniteStage
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionTowerDeterminantDegree
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDiscreteSubspaceQuotient
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDegreeDeterminant
import ArakelovGeometry.AdelicVectorBundle.DegreeDeterminantIsometry

/-!
# Actual mixed native determinant degrees over countable discrete bases

Simultaneous genuine finite-stage subquotient descent produces the native
mixed determinant measurability. Canonical all-completed isometries and
measure-preserving tower transport then identify actual finite-stage degrees.
-/

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
universe u v wL wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]

namespace NormFamily

/-- Actual simultaneous finite-stage subquotient descent produces the native
mixed determinant measurability, without original ultrametricity or any target
regularity hypothesis. -/
theorem scalarExtension_subquotient_determinant_isMeasurable_of_countable_discrete
    (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (P Q : Submodule L (L ⊗[K] E)) (hPQ : P ≤ Q) :
    (((ξ.scalarExtension (L := L)).restrict Q).quotient
      (P.comap Q.subtype)).determinant.IsMeasurable := by
  obtain ⟨F, _, P₀, Q₀, _, _, _, e, he, _⟩ :=
    ξ.exists_complexFiniteStage_subquotient_isometry hN P Q hPQ
  let : Countable (S.algebraicExtension F).Ω :=
    AdelicStructure.ParameterSpaceExtension.countable_of_finiteDimensional (S := S) (L := F)
  let : DiscreteMeasurableSpace (S.algebraicExtension F).Ω :=
    AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
      (S := S) (L := F)
  let η₀ := ((ξ.scalarExtension (L := F)).restrict Q₀).quotient (P₀.comap Q₀.subtype)
  let η := η₀.scalarExtension (L := L)
  let θ := ((ξ.scalarExtension (L := L)).restrict Q).quotient (P.comap Q.subtype)
  have hm : η.determinant.IsMeasurable :=
    (η₀.isMeasurable_of_discrete.determinant_of_discrete_or_countable
      (Or.inl inferInstance)).determinant_scalarExtension
  have ht : (θ.towerPullback F.toIntermediateField).determinant.IsMeasurable :=
    η.determinant_isMeasurable_of_completed_isometry
      (θ.towerPullback F.toIntermediateField) e he hm
  rw [towerPullback_determinant] at ht
  exact (θ.determinant.isMeasurable_towerPullback_iff F.toIntermediateField).mp ht

/-- Every genuine quotient of an actual native restriction has measurable
actual determinant, by the proved image/preimage identity for the canonical
subspace inclusion and simultaneous finite-stage descent. -/
theorem scalarExtension_restrict_quotient_determinant_isMeasurable_of_countable_discrete
    (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (Q : Submodule L (L ⊗[K] E)) (T : Submodule L Q) :
    (((ξ.scalarExtension (L := L)).restrict Q).quotient T).determinant.IsMeasurable := by
  let P := T.map Q.subtype
  have hP : P ≤ Q := Q.map_subtype_le T
  have hT : P.comap Q.subtype = T := by
    change (T.map Q.subtype).comap Q.subtype = T
    rw [Submodule.comap_map_eq, Submodule.ker_subtype, sup_bot_eq]
  have hm := ξ.scalarExtension_subquotient_determinant_isMeasurable_of_countable_discrete
    hN P Q hP
  exact Eq.mp (congrArg (fun C : Submodule L Q =>
    (((ξ.scalarExtension (L := L)).restrict Q).quotient C).determinant.IsMeasurable) hT) hm

end NormFamily

namespace AdelicVectorBundle

private theorem nativeMixed_determinant_isMeasurable
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (Q : Submodule L (L ⊗[K] E)) (T : Submodule L Q) :
    let W := V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase hN Q T
    W.toNormFamily.determinant.IsMeasurable := by
  dsimp only
  rw [scalarExtensionSubspaceQuotientOfCountableDiscreteBase_toNormFamily]
  exact NormFamily.scalarExtension_restrict_quotient_determinant_isMeasurable_of_countable_discrete
    V.toNormFamily hN Q T

private theorem nativeMixed_norm_eq
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (F : AdelicStructure.FiniteIntermediateField K L) (hi : ∃ a : F, a ^ 2 = -1)
    (P Q : Submodule F (F ⊗[K] E)) (hPQ : P ≤ Q) :
    let : Countable (S.algebraicExtension F).Ω :=
      AdelicStructure.ParameterSpaceExtension.countable_of_finiteDimensional (S := S) (L := F)
    let : DiscreteMeasurableSpace (S.algebraicExtension F).Ω :=
      AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
        (S := S) (L := F)
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    let A := (P.baseChange L).map c.toLinearMap
    let B := (Q.baseChange L).map c.toLinearMap
    let C := P.comap Q.subtype
    let R : AdelicVectorBundle (S.algebraicExtension L) (B ⧸ A.comap B.subtype) :=
      V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase hN B (A.comap B.subtype)
    let W₀ : AdelicVectorBundle (S.algebraicExtension F) (Q ⧸ C) :=
      ((V.scalarExtensionOfCountableDiscreteBase (L := F) hN).restrictOfMeasurableBase
      Q (Or.inl inferInstance)).quotientOfMeasurableBase C (Or.inl inferInstance)
    ∀ x z, (R.toNormFamily.towerPullback F.toIntermediateField).norm x
      ((finiteStageSubquotientEquiv F P Q hPQ).toLinearMap.baseChange
        (((S.algebraicExtension F).algebraicExtension L).ϕ x).Completion z) =
      (W₀.toNormFamily.scalarExtension (L := L)).norm x z := by
  let : Countable (S.algebraicExtension F).Ω :=
    AdelicStructure.ParameterSpaceExtension.countable_of_finiteDimensional (S := S) (L := F)
  let : DiscreteMeasurableSpace (S.algebraicExtension F).Ω :=
    AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
      (S := S) (L := F)
  dsimp only
  intro x z
  simp only [scalarExtensionSubspaceQuotientOfCountableDiscreteBase_toNormFamily,
    quotientOfMeasurableBase_toNormFamily, restrictOfMeasurableBase_toNormFamily,
    scalarExtensionOfCountableDiscreteBase_toNormFamily]
  exact V.toNormFamily.scalarExtension_subquotient_finiteStage_norm_eq hN F hi P Q hPQ x z

omit [IsAlgClosed L] in
private theorem nativeMixed_degree_of_tower_isometry [S.IsProper]
    (F : AdelicStructure.FiniteIntermediateField K L)
    {X Y : Type*} [AddCommGroup X] [Module F X] [FiniteDimensional F X]
    [AddCommGroup Y] [Module L Y] [FiniteDimensional L Y]
    (W₀ : AdelicVectorBundle (S.algebraicExtension F) X)
    (R : AdelicVectorBundle (S.algebraicExtension L) Y) (e : L ⊗[F] X ≃ₗ[L] Y)
    (hdetR : R.toNormFamily.determinant.IsMeasurable)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (he : ∀ x z, (R.toNormFamily.towerPullback F.toIntermediateField).norm x
      (e.toLinearMap.baseChange
        (((S.algebraicExtension F).algebraicExtension L).ϕ x).Completion z) =
      (W₀.toNormFamily.scalarExtension (L := L)).norm x z) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    let : Countable (S.algebraicExtension F).Ω :=
      AdelicStructure.ParameterSpaceExtension.countable_of_finiteDimensional (S := S) (L := F)
    let : DiscreteMeasurableSpace (S.algebraicExtension F).Ω :=
      AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
        (S := S) (L := F)
    R.degreeOfMeasurableDeterminant hdetR
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) =
      W₀.degree (Or.inl inferInstance)
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
  let W := W₀.scalarExtensionOfCountableDiscreteBase (L := L) hFN
  let T := R.towerPullback F.toIntermediateField
  have hdetW : W.toNormFamily.determinant.IsMeasurable :=
    W₀.scalarExtensionOfCountableDiscreteBase_determinant_isMeasurable (L := L) hFN
  have hdetT : T.toNormFamily.determinant.IsMeasurable :=
    R.toNormFamily.determinant_isMeasurable_towerPullback F.toIntermediateField hdetR
  change R.degreeOfMeasurableDeterminant hdetR hLN = W₀.degree (Or.inl inferInstance) hFN
  have hdeg : W.degreeOfMeasurableDeterminant hdetW hTN =
      T.degreeOfMeasurableDeterminant hdetT hTN :=
    W.degreeOfMeasurableDeterminant_eq_of_completed_isometry T e hdetW hTN he
  have ht : T.degreeOfMeasurableDeterminant hdetT hTN =
      R.degreeOfMeasurableDeterminant hdetR hLN :=
    R.degreeOfMeasurableDeterminant_towerPullback F.toIntermediateField hdetR hN
  exact ht.symm.trans (hdeg.symm.trans
    (W₀.degreeOfMeasurableDeterminant_scalarExtensionOfCountableDiscreteBase hFN))

/-- The actual mixed native determinant degree equals its genuine finite-stage
mixed degree. All determinant measurabilities and normalizations are produced;
no target degree context or original ultrametricity is assumed. -/
theorem degree_nativeSubquotientOfCountableDiscreteBase_finiteStage [S.IsProper]
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (F : AdelicStructure.FiniteIntermediateField K L) (hi : ∃ a : F, a ^ 2 = -1)
    (P Q : Submodule F (F ⊗[K] E)) (hPQ : P ≤ Q) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    let : Countable (S.algebraicExtension F).Ω :=
      AdelicStructure.ParameterSpaceExtension.countable_of_finiteDimensional (S := S) (L := F)
    let : DiscreteMeasurableSpace (S.algebraicExtension F).Ω :=
      AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
        (S := S) (L := F)
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    let A := (P.baseChange L).map c.toLinearMap
    let B := (Q.baseChange L).map c.toLinearMap
    let C := P.comap Q.subtype
    let R : AdelicVectorBundle (S.algebraicExtension L) (B ⧸ A.comap B.subtype) :=
      V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase hN B (A.comap B.subtype)
    R.degreeOfMeasurableDeterminant
      (nativeMixed_determinant_isMeasurable V hN B (A.comap B.subtype))
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) =
      (((V.scalarExtensionOfCountableDiscreteBase (L := F) hN).restrictOfMeasurableBase
        Q (Or.inl inferInstance)).quotientOfMeasurableBase C (Or.inl inferInstance)).degree
          (Or.inl inferInstance)
          (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let : Countable (S.algebraicExtension F).Ω :=
    AdelicStructure.ParameterSpaceExtension.countable_of_finiteDimensional (S := S) (L := F)
  let : DiscreteMeasurableSpace (S.algebraicExtension F).Ω :=
    AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
      (S := S) (L := F)
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
  let A := (P.baseChange L).map c.toLinearMap
  let B := (Q.baseChange L).map c.toLinearMap
  let C := P.comap Q.subtype
  let W₀ : AdelicVectorBundle (S.algebraicExtension F) (Q ⧸ C) :=
      ((V.scalarExtensionOfCountableDiscreteBase (L := F) hN).restrictOfMeasurableBase
    Q (Or.inl inferInstance)).quotientOfMeasurableBase C (Or.inl inferInstance)
  let R : AdelicVectorBundle (S.algebraicExtension L) (B ⧸ A.comap B.subtype) :=
      V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase hN B (A.comap B.subtype)
  have hdetR : R.toNormFamily.determinant.IsMeasurable :=
    nativeMixed_determinant_isMeasurable V hN B (A.comap B.subtype)
  exact nativeMixed_degree_of_tower_isometry (X := Q ⧸ C) (Y := B ⧸ A.comap B.subtype) F W₀ R
    (finiteStageSubquotientEquiv F P Q hPQ) hdetR hN
    (nativeMixed_norm_eq V hN F hi P Q hPQ)

end AdelicVectorBundle
end ArakelovGeometry
