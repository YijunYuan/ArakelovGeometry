/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.Algebraic.NativeBundle
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.FiniteNativeBundle

import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.NativeSubquotientFiniteStage
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.Algebraic.ScalarBundle
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.FinitePositiveAtoms
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.ScalarExtensionMeasurable
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Tower.DeterminantDegree

/-!
# Actual geometric native finite-stage degrees

Genuine finite-stage bundles, ordinary scalar degree preservation and actual
completed native isometries identify canonical geometric native degrees with
their finite-stage degrees, without countability or target regularity premises.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.NormFamily

universe uK uL uE uΩ uF
variable {K : Type uK} {L : Type uL} {E : Type uE}
  [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L] {S : AdelicStructure.{uK, uΩ} K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [MeasurableSingletonClass S.Ω]

open IsDominated

local instance nativeFiniteStage_isProper_algebraicExtension [S.IsProper] :
    (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

omit [IsAlgClosed L] [MeasurableSingletonClass S.Ω] in
private theorem native_degree_of_tower_isometry [S.IsProper]
    (F : IntermediateField K L)
    [MeasurableSingletonClass (S.algebraicExtension F).Ω]
    {X Y : Type*} [AddCommGroup X] [Module F X] [FiniteDimensional F X]
    [AddCommGroup Y] [Module L Y] [FiniteDimensional L Y]
    (V₀ : AdelicVectorBundle (S.algebraicExtension F) X)
    (R : AdelicVectorBundle (S.algebraicExtension L) Y)
    (e : (L ⊗[F] X) ≃ₗ[L] Y)
    [hpos : (S.algebraicExtension F).HasPositiveAtoms]
    [hS : (S.algebraicExtension F).HasOnlyFinitePlaces]
    (hdet₀ : V₀.toNormFamily.determinant.IsMeasurable)
    (hdetR : R.toNormFamily.determinant.IsMeasurable)
    [hFN : (S.algebraicExtension F).IsArchimedeanNormalized]
    [hLN : (S.algebraicExtension L).IsArchimedeanNormalized]
    (he : ∀ (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
      (z : x.abv.Completion ⊗[L] (L ⊗[F] X)),
      R.toNormFamily.norm (scalarExtensionTowerPlace x)
        (e.toLinearMap.baseChange x.abv.Completion z) =
          (V₀.toNormFamily.scalarExtension (L := L)).norm x z) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    R.degreeOfMeasurableDeterminant (hdet := hdetR) =
      V₀.degreeOfMeasurableDeterminant (hdet := hdet₀) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
  let W := V₀.toNormFamily.algebraicScalarBundleOfPositiveAtoms (L := L)
    (hpos := ⟨hpos⟩) (hS := ⟨hS⟩)
  exact (AdelicVectorBundle.degreeOfMeasurableDeterminant_eq_of_tower_isometry
    F W R e (hdetW := hdet₀.determinant_scalarExtension) (hdetR := hdetR)
    (hNT := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) he).trans
      (V₀.degreeOfMeasurableDeterminant_algebraicScalarBundleOfPositiveAtoms
        (hpos := ⟨hpos⟩) (hS := ⟨hS⟩) (hdet := hdet₀))

/-- Equality between the actual positive-atomic native degree and its finite-stage degree.

This transparent predicate retains the genuine quotient bundles, determinant measurability,
and Archimedean normalization occurring in both degrees. -/
abbrev NativeAlgebraicSubquotientDegreeEq [S.IsProper]
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces]
    [hN : S.IsArchimedeanNormalized]
    (F : Type uF) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L] [FiniteDimensional K F]
    (P₀ Q₀ : Submodule F (F ⊗[K] E)) (P Q : Submodule L (L ⊗[K] E)) : Prop :=
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    (ξ.nativeAlgebraicSubquotientOfPositiveAtoms Q
      (P.comap Q.subtype)).degreeOfMeasurableDeterminant
        (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
    (ξ.nativeSubquotientOfPositiveAtoms Q₀
      (P₀.comap Q₀.subtype)).degreeOfMeasurableDeterminant
        (hdet := (scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms
          ξ hξ Q₀ (P₀.comap Q₀.subtype)))
        (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F))⟩)

/-- Degree comparison for the canonical scalar images of a finite-stage relative quotient. -/
abbrev NativeAlgebraicSubquotientImageDegreeEq [S.IsProper]
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces]
    [hN : S.IsArchimedeanNormalized]
    (F : Type uF) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L] [FiniteDimensional K F]
    (P Q : Submodule F (F ⊗[K] E)) : Prop :=
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    ξ.NativeAlgebraicSubquotientDegreeEq F P Q
      ((P.baseChange L).map c.toLinearMap) ((Q.baseChange L).map c.toLinearMap)

private theorem nativeAlgebraicSubquotient_degree_of_transport [S.IsProper]
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces]
    [hN : S.IsArchimedeanNormalized]
    (F : Type uF) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L] [FiniteDimensional K F]
    (hd : ∀ {X : Type (max uF uE)} {Y : Type (max uL uE)}
      [AddCommGroup X] [Module F X] [FiniteDimensional F X]
      [AddCommGroup Y] [Module L Y] [FiniteDimensional L Y]
      (V₀ : AdelicVectorBundle (S.algebraicExtension F) X)
      (R : AdelicVectorBundle (S.algebraicExtension L) Y) (e : (L ⊗[F] X) ≃ₗ[L] Y)
      (hdet₀ : V₀.toNormFamily.determinant.IsMeasurable)
      (hdetR : R.toNormFamily.determinant.IsMeasurable)
      (_he : ∀ (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
        (z : x.abv.Completion ⊗[L] (L ⊗[F] X)),
        R.toNormFamily.norm (scalarExtensionTowerPlace x)
          (e.toLinearMap.baseChange x.abv.Completion z) =
            (V₀.toNormFamily.scalarExtension (L := L)).norm x z),
      let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
      R.degreeOfMeasurableDeterminant (hdet := hdetR)
        (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
        V₀.degreeOfMeasurableDeterminant (hdet := hdet₀)
          (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F))⟩))
    (hi : ∃ a : F, a ^ 2 = -1)
    (P Q : Submodule F (F ⊗[K] E)) (hPQ : P ≤ Q) :
    ξ.NativeAlgebraicSubquotientImageDegreeEq (L := L) (hξ := hξ) (hpos := ⟨hpos⟩)
        (hS := ⟨hS⟩) F P Q := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
  let A := (P.baseChange L).map c.toLinearMap
  let B := (Q.baseChange L).map c.toLinearMap
  let V₀ := ξ.nativeSubquotientOfPositiveAtoms (hξ := hξ) (hpos := ⟨hpos⟩)
      (hS := ⟨hS⟩) Q (P.comap Q.subtype)
  let R := ξ.nativeAlgebraicSubquotientOfPositiveAtoms (hξ := hξ) (hpos := ⟨hpos⟩)
      (hS := ⟨hS⟩) B (A.comap B.subtype)
  have hdet₀ : V₀.toNormFamily.determinant.IsMeasurable :=
    scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms
      ξ hξ (hpos := ⟨hpos⟩) (hS := ⟨hS⟩) Q (P.comap Q.subtype)
  have hdetR : R.toNormFamily.determinant.IsMeasurable :=
    scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
      ξ hξ (hpos := ⟨hpos⟩) (hS := ⟨hS⟩) B (A.comap B.subtype)
  obtain ⟨e, he, _⟩ := ξ.hasScalarExtensionSubquotientIsometry_of_images
    F hi P Q hPQ A B rfl rfl
  exact hd V₀ R e hdet₀ hdetR he

/-- Canonical degree of the actual native scalar image of a finite-stage
relative quotient equals its genuine finite-stage native degree. -/
theorem nativeAlgebraicSubquotient_degree_finiteStage [S.IsProper]
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces]
    [hN : S.IsArchimedeanNormalized]
    (F : AdelicStructure.FiniteIntermediateField K L) (hi : ∃ a : F, a ^ 2 = -1)
    (P Q : Submodule F (F ⊗[K] E)) (hPQ : P ≤ Q) :
    ξ.NativeAlgebraicSubquotientImageDegreeEq (L := L) F P Q := by
  refine nativeAlgebraicSubquotient_degree_of_transport ξ hξ F ?_ hi P Q hPQ
  intro X Y _ _ _ _ _ _ V₀ R e hdet₀ hdetR he
  let : MeasurableSingletonClass (S.algebraicExtension F).Ω :=
    AdelicStructure.measurableSingletonClass_algebraicExtension_of_finiteDimensional
      (S := S) (L := F)
  have hFpos (x : (S.algebraicExtension F).Ω) :
      0 < (S.algebraicExtension F).v {x} :=
    AdelicStructure.Algebraic.singleton_pos_algebraicExtension_of_finiteDimensional S x
  have hFS (x : (S.algebraicExtension F).Ω) : x ∈ (S.algebraicExtension F).Ωfin :=
    (AdelicStructure.mem_Ωfin_algebraicExtension_iff x).mpr (hS x.base)
  exact native_degree_of_tower_isometry (X := X) (Y := Y) F.toIntermediateField V₀ R e
    (hpos := ⟨hFpos⟩) (hS := ⟨hFS⟩) hdet₀ hdetR he

private theorem nativeAlgebraicSubquotient_degree_of_images [S.IsProper]
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces]
    [hN : S.IsArchimedeanNormalized]
    (F : Type uF) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L] [FiniteDimensional K F]
    (P₀ Q₀ : Submodule F (F ⊗[K] E))
    (hd : ξ.NativeAlgebraicSubquotientImageDegreeEq (L := L) (hξ := hξ) (hpos := ⟨hpos⟩)
        (hS := ⟨hS⟩) F P₀ Q₀)
    (P Q : Submodule L (L ⊗[K] E))
    (hP : (P₀.baseChange L).map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap = P)
    (hQ : (Q₀.baseChange L).map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap = Q) :
    ξ.NativeAlgebraicSubquotientDegreeEq (hξ := hξ) (hpos := ⟨hpos⟩) (hS := ⟨hS⟩) F P₀ Q₀ P Q := by
  subst Q
  subst P
  exact hd

/-- The finite field, nested endpoints, exact native images, quotient rank
and canonical degree comparison are all produced for an arbitrary target pair. -/
theorem exists_complexFiniteStage_nativeAlgebraicSubquotient_degree [S.IsProper]
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces]
    [hN : S.IsArchimedeanNormalized]
    (P Q : Submodule L (L ⊗[K] E)) (hPQ : P ≤ Q) :
    ∃ F : AdelicStructure.FiniteIntermediateField K L, (∃ a : F, a ^ 2 = -1) ∧
      ∃ P₀ Q₀ : Submodule F (F ⊗[K] E), P₀ ≤ Q₀ ∧
        (P₀.baseChange L).map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap = P ∧
        (Q₀.baseChange L).map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap = Q ∧
        Module.finrank L (Q ⧸ P.comap Q.subtype) =
          Module.finrank F (Q₀ ⧸ P₀.comap Q₀.subtype) ∧
        ξ.NativeAlgebraicSubquotientDegreeEq F P₀ Q₀ P Q := by
  obtain ⟨F, hi, P₀, Q₀, hPQ₀, hP, hQ, _, _, hr⟩ :=
    ξ.exists_complexFiniteStage_subquotient_isometry P Q hPQ
  refine ⟨F, hi, P₀, Q₀, hPQ₀, hP, hQ, hr, ?_⟩
  exact nativeAlgebraicSubquotient_degree_of_images ξ hξ F P₀ Q₀
    (ξ.nativeAlgebraicSubquotient_degree_finiteStage F hi P₀ Q₀ hPQ₀)
    P Q hP hQ

end ArakelovGeometry.NormFamily
