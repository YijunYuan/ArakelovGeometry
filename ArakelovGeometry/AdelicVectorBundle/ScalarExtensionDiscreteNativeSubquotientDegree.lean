/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DegreeDeterminantIsometry
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDegreeDeterminant
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDiscreteNativeFiniteStageDegree
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDiscreteSubspaceQuotient
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionNativeSubquotientFiniteStage
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionTowerDeterminantDegree

/-!
# Actual mixed native determinant degrees over countable discrete bases

Simultaneous genuine finite-stage subquotient descent produces the native
mixed determinant measurability. Canonical all-completed isometries and
measure-preserving tower transport then identify actual finite-stage degrees.
-/

@[expose] public section

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
  exact determinant_isMeasurable_of_tower_completed_isometry F.toIntermediateField η θ e he hm

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

/-- The canonical native subspace quotient has a measurable determinant norm family. -/
theorem scalarExtensionSubspaceQuotientOfCountableDiscreteBase_determinant_isMeasurable
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
    (F : Type*) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L]
    [Countable (S.algebraicExtension F).Ω] [DiscreteMeasurableSpace (S.algebraicExtension F).Ω]
    (hi : ∃ a : F, a ^ 2 = -1)
    (P Q : Submodule F (F ⊗[K] E)) (hPQ : P ≤ Q) :
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    let A := (P.baseChange L).map c.toLinearMap
    let B := (Q.baseChange L).map c.toLinearMap
    let C := P.comap Q.subtype
    let R : AdelicVectorBundle (S.algebraicExtension L) (B ⧸ A.comap B.subtype) :=
      V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase hN B (A.comap B.subtype)
    let W₀ : AdelicVectorBundle (S.algebraicExtension F) (Q ⧸ C) :=
      ((V.scalarExtensionOfCountableDiscreteBase (L := F) hN).restrictOfMeasurableBase
      Q (Or.inl inferInstance)).quotientOfMeasurableBase C (Or.inl inferInstance)
    ∀ (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
      (z : x.abv.Completion ⊗[L] (L ⊗[F] (Q ⧸ C))),
      R.toNormFamily.norm (scalarExtensionTowerPlace x)
      ((finiteStageSubquotientEquiv (L := L) F P Q hPQ).toLinearMap.baseChange
        x.abv.Completion z) =
      (W₀.toNormFamily.scalarExtension (L := L)).norm x z := by
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
        x.abv.Completion z) =
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
  have hdetW : W.toNormFamily.determinant.IsMeasurable :=
    W₀.scalarExtensionOfCountableDiscreteBase_determinant_isMeasurable (L := L) hFN
  change R.degreeOfMeasurableDeterminant hdetR hLN = W₀.degree (Or.inl inferInstance) hFN
  have hdeg : R.degreeOfMeasurableDeterminant hdetR hLN =
      W.degreeOfMeasurableDeterminant hdetW hTN :=
    degreeOfMeasurableDeterminant_eq_of_tower_isometry F.toIntermediateField
      W R e hdetW hdetR hLN hTN he
  exact hdeg.trans
    (W₀.degreeOfMeasurableDeterminant_scalarExtensionOfCountableDiscreteBase hFN)

universe wF

/-- Equality of the native mixed determinant degree with its finite-stage mixed degree.

The transparent predicate retains the actual quotient bundles and their produced determinant
measurability and normalization data. -/
abbrev NativeSubquotientDegreeEq [S.IsProper]
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (F : Type wF) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L] [FiniteDimensional K F]
    (P Q : Submodule F (F ⊗[K] E)) : Prop :=
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
      (scalarExtensionSubspaceQuotientOfCountableDiscreteBase_determinant_isMeasurable
        V hN B (A.comap B.subtype))
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) =
      (((V.scalarExtensionOfCountableDiscreteBase (L := F) hN).restrictOfMeasurableBase
        Q (Or.inl inferInstance)).quotientOfMeasurableBase C (Or.inl inferInstance)).degree
          (Or.inl inferInstance)
          (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN)

private theorem nativeMixed_generic_canonical_degree [S.IsProper]
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (F : Type wF) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L] [FiniteDimensional K F]
    (hd : ∀ {X : Type (max wF wE)} {Y : Type (max wL wE)}
      [AddCommGroup X] [Module F X] [FiniteDimensional F X]
      [AddCommGroup Y] [Module L Y] [FiniteDimensional L Y]
      (W₀ : AdelicVectorBundle (S.algebraicExtension F) X)
      (R : AdelicVectorBundle (S.algebraicExtension L) Y) (e : L ⊗[F] X ≃ₗ[L] Y)
      (hdetR : R.toNormFamily.determinant.IsMeasurable)
      (_he : ∀ (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
        (z : x.abv.Completion ⊗[L] (L ⊗[F] X)),
        R.toNormFamily.norm (scalarExtensionTowerPlace x)
          (e.toLinearMap.baseChange x.abv.Completion z) =
          (W₀.toNormFamily.scalarExtension (L := L)).norm x z),
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
          (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN))
    (hi : ∃ a : F, a ^ 2 = -1)
    (P Q : Submodule F (F ⊗[K] E)) (hPQ : P ≤ Q) :
    V.NativeSubquotientDegreeEq (L := L) hN F P Q := by
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
    scalarExtensionSubspaceQuotientOfCountableDiscreteBase_determinant_isMeasurable
        V hN B (A.comap B.subtype)
  let e := finiteStageSubquotientEquiv (L := L) F P Q hPQ
  have he := nativeMixed_norm_eq (L := L) V hN F hi P Q hPQ
  dsimp only [c, A, B, C, W₀, R] at *
  exact hd (X := Q ⧸ C) (Y := B ⧸ A.comap B.subtype) W₀ R e hdetR he

/-- The actual mixed native determinant degree equals its genuine finite-stage
mixed degree. All determinant measurabilities and normalizations are produced;
no target degree context or original ultrametricity is assumed. -/
theorem degree_nativeSubquotientOfCountableDiscreteBase_finiteStage [S.IsProper]
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (F : AdelicStructure.FiniteIntermediateField K L) (hi : ∃ a : F, a ^ 2 = -1)
    (P Q : Submodule F (F ⊗[K] E)) (hPQ : P ≤ Q) :
    V.NativeSubquotientDegreeEq (L := L) hN F P Q := by
  refine nativeMixed_generic_canonical_degree V hN F ?_ hi P Q hPQ
  intro X Y _ _ _ _ _ _ W₀ R e hdetR he
  exact nativeMixed_degree_of_tower_isometry (X := X) (Y := Y) F W₀ R e hdetR hN he

end AdelicVectorBundle
end ArakelovGeometry
