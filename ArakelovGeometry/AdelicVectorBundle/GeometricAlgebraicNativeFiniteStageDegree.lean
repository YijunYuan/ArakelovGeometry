/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.GeometricAlgebraicNativeBundle
import ArakelovGeometry.AdelicVectorBundle.GeometricAlgebraicScalarBundle
import ArakelovGeometry.AdelicVectorBundle.GeometricFiniteNativeBundle

/-!
# Actual geometric native finite-stage degrees

Genuine finite-stage bundles, ordinary scalar degree preservation and actual
completed native isometries identify canonical geometric native degrees with
their finite-stage degrees, without countability or target regularity premises.
-/

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.NormFamily

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [MeasurableSingletonClass S.Ω]

open IsDominated

local instance nativeFiniteStage_isProper_algebraicExtension [S.IsProper] :
    (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- Canonical degree of the actual native scalar image of a finite-stage
relative quotient equals its genuine finite-stage native degree. -/
theorem nativeAlgebraicSubquotient_degree_finiteStage [S.IsProper]
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (F : AdelicStructure.FiniteIntermediateField K L) (hi : ∃ a : F, a ^ 2 = -1)
    (P Q : Submodule F (F ⊗[K] E)) (hPQ : P ≤ Q) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    let A := (P.baseChange L).map c.toLinearMap
    let B := (Q.baseChange L).map c.toLinearMap
    (ξ.nativeAlgebraicSubquotientOfPositiveAtoms hξ hpos hS B
      (A.comap B.subtype)).degreeOfMeasurableDeterminant
        (scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
          ξ hξ hpos hS B (A.comap B.subtype))
        (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) =
    (ξ.nativeSubquotientOfPositiveAtoms hξ hpos hS Q
      (P.comap Q.subtype)).degreeOfMeasurableDeterminant
        (scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms
          ξ hξ hpos hS Q (P.comap Q.subtype))
        (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
  let : MeasurableSingletonClass (S.algebraicExtension F).Ω :=
    AdelicStructure.measurableSingletonClass_algebraicExtension_of_finiteDimensional
      (S := S) (L := F)
  have hFpos (x : (S.algebraicExtension F).Ω) :
      0 < (S.algebraicExtension F).v {x} :=
    AdelicStructure.Algebraic.singleton_pos_algebraicExtension_of_finiteDimensional S hpos x
  have hFS (x : (S.algebraicExtension F).Ω) : x ∈ (S.algebraicExtension F).Ωfin :=
    (scalarExtension_mem_Ωfin_iff x).mpr (hS x.base)
  let hFN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
  let hTN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hFN
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
  let A := (P.baseChange L).map c.toLinearMap
  let B := (Q.baseChange L).map c.toLinearMap
  let V₀ := ξ.nativeSubquotientOfPositiveAtoms hξ hpos hS Q (P.comap Q.subtype)
  let W := V₀.toNormFamily.algebraicScalarBundleOfPositiveAtoms (L := L)
    V₀.isDominated hFpos hFS
  let R := ξ.nativeAlgebraicSubquotientOfPositiveAtoms hξ hpos hS B (A.comap B.subtype)
  let T := R.towerPullback F.toIntermediateField
  let e := finiteStageSubquotientEquiv F P Q hPQ
  have hdet₀ : V₀.toNormFamily.determinant.IsMeasurable :=
    scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms
      ξ hξ hpos hS Q (P.comap Q.subtype)
  have hdetW : W.toNormFamily.determinant.IsMeasurable := hdet₀.determinant_scalarExtension
  have hdetR : R.toNormFamily.determinant.IsMeasurable :=
    scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
      ξ hξ hpos hS B (A.comap B.subtype)
  have hdetT : T.toNormFamily.determinant.IsMeasurable :=
    R.toNormFamily.determinant_isMeasurable_towerPullback F.toIntermediateField hdetR
  change R.degreeOfMeasurableDeterminant hdetR hLN =
    V₀.degreeOfMeasurableDeterminant hdet₀ hFN
  have he : W.degreeOfMeasurableDeterminant hdetW hTN =
      T.degreeOfMeasurableDeterminant hdetT hTN :=
    W.degreeOfMeasurableDeterminant_eq_of_completed_isometry T e hdetW hTN
      (fun x z => ξ.scalarExtension_subquotient_finiteStage_norm_eq hN F hi P Q hPQ x z)
  have ht : T.degreeOfMeasurableDeterminant hdetT hTN =
      R.degreeOfMeasurableDeterminant hdetR hLN :=
    R.degreeOfMeasurableDeterminant_towerPullback F.toIntermediateField hdetR hN
  have hs : W.degreeOfMeasurableDeterminant hdetW hTN =
      V₀.degreeOfMeasurableDeterminant hdet₀ hFN :=
    V₀.degreeOfMeasurableDeterminant_algebraicScalarBundleOfPositiveAtoms
      hFpos hFS hdet₀ hFN
  exact ht.symm.trans (he.symm.trans hs)

/-- The finite field, nested endpoints, exact native images, quotient rank
and canonical degree comparison are all produced for an arbitrary target pair. -/
theorem exists_complexFiniteStage_nativeAlgebraicSubquotient_degree [S.IsProper]
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (P Q : Submodule L (L ⊗[K] E)) (hPQ : P ≤ Q) :
    ∃ F : AdelicStructure.FiniteIntermediateField K L, (∃ a : F, a ^ 2 = -1) ∧
      ∃ P₀ Q₀ : Submodule F (F ⊗[K] E), P₀ ≤ Q₀ ∧
        (P₀.baseChange L).map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap = P ∧
        (Q₀.baseChange L).map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap = Q ∧
        Module.finrank L (Q ⧸ P.comap Q.subtype) =
          Module.finrank F (Q₀ ⧸ P₀.comap Q₀.subtype) ∧
        let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
        (ξ.nativeAlgebraicSubquotientOfPositiveAtoms hξ hpos hS Q
          (P.comap Q.subtype)).degreeOfMeasurableDeterminant
            (scalarExtension_subquotient_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
              ξ hξ hpos hS P Q hPQ)
            (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) =
        (ξ.nativeSubquotientOfPositiveAtoms hξ hpos hS Q₀
          (P₀.comap Q₀.subtype)).degreeOfMeasurableDeterminant
            (scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms
              ξ hξ hpos hS Q₀ (P₀.comap Q₀.subtype))
            (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN) := by
  obtain ⟨F, hi, P₀, Q₀, hPQ₀, hP, hQ, _, _, hr⟩ :=
    ξ.exists_complexFiniteStage_subquotient_isometry hN P Q hPQ
  refine ⟨F, hi, P₀, Q₀, hPQ₀, hP, hQ, hr, ?_⟩
  subst Q
  subst P
  exact ξ.nativeAlgebraicSubquotient_degree_finiteStage hξ hpos hS hN F hi P₀ Q₀ hPQ₀

end ArakelovGeometry.NormFamily
