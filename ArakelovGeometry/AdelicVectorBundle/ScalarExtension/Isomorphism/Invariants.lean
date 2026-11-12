/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Algebraic.ClosureApproximation
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Bundle
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Isomorphism.Subspace

import ArakelovGeometry.AdelicVectorBundle.Degree.Isometry
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Isomorphism.Degree
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual scalar-extended invariants under algebraic-closure isomorphisms

The actual native determinant degree transport is consumed on all subspaces.
The resulting suprema retain their original rank-zero conventions.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle

variable {K : Type*} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- A quotient by a submodule proved to be zero has the original degree
through its canonical completed isometry. -/
theorem degree_quotient_of_eq_bot (V : AdelicVectorBundle S E)
    (P : Submodule K E) (hP : P = ⊥)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (V.quotientOfMeasurableBase P).degree = V.degree := by
  symm
  apply degree_eq_of_completed_isometry _ _
    (P.quotEquivOfEqBot hP).symm
  intro ω z
  simp only [quotientOfMeasurableBase_toNormFamily,
    Submodule.coe_quotEquivOfEqBot_symm]
  apply V.toNormFamily.pushforward_norm_of_injective
  apply LinearMap.ker_eq_bot.mp
  exact (Submodule.ker_mkQ P).trans hP

/-- The actual quotient by zero has the original degree. -/
theorem degree_quotient_bot (V : AdelicVectorBundle S E)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (V.quotientOfMeasurableBase ⊥).degree = V.degree :=
  V.degree_quotient_of_eq_bot ⊥ rfl

variable {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra K M]
  [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K M] [IsAlgClosed L] [IsAlgClosed M]

/-- The actual native subquotient degree transport compares restrictions by
taking lower endpoint zero, without replacing their norm families. -/
theorem degree_restrict_scalarExtension_algEquiv
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (σ : L ≃ₐ[K] M) (B : Submodule L (L ⊗[K] E)) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
    let _ := hcount.algebraicExtension_of_isAlgClosed (L := L)
    let _ := hcount.algebraicExtension_of_isAlgClosed (L := M)
    ((V.scalarExtension (L := M)).restrictOfMeasurableBase
      (scalarExtensionSubspaceOrderIso (E := E) σ B)).degree
        (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M))⟩) =
    ((V.scalarExtension (L := L)).restrictOfMeasurableBase B).degree
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  have hd := V.degree_nativeSubquotient_algEquiv σ B ⊥ bot_le
  dsimp only at hd
  let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
  let hM := hcount.algebraicExtension_of_isAlgClosed (L := M)
  let R := (V.scalarExtension (L := L)).restrictOfMeasurableBase B
  let T := (V.scalarExtension (L := M)).restrictOfMeasurableBase
    (scalarExtensionSubspaceOrderIso (E := E) σ B)
  have hbot : ((⊥ : Submodule L (L ⊗[K] E)).comap B.subtype) = ⊥ :=
    (Submodule.comap_bot _).trans (Submodule.ker_subtype B)
  have htbot : ((scalarExtensionSubspaceOrderIso (E := E) σ ⊥).comap
      (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype) = ⊥ := by
    rw [(scalarExtensionSubspaceOrderIso (E := E) σ).map_bot,
      Submodule.comap_bot, Submodule.ker_subtype]
  exact (T.degree_quotient_of_eq_bot _ htbot
    (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M))⟩)).symm.trans
      (hd.trans (R.degree_quotient_of_eq_bot _ hbot
        (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩)))

/-- The transported actual restriction has the same mean degree in every
rank, including the existing real division convention in rank zero. -/
theorem slope_restrict_scalarExtension_algEquiv
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (σ : L ≃ₐ[K] M) (B : Submodule L (L ⊗[K] E)) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
    let _ := hcount.algebraicExtension_of_isAlgClosed (L := L)
    let _ := hcount.algebraicExtension_of_isAlgClosed (L := M)
    ((V.scalarExtension (L := M)).restrictOfMeasurableBase
      (scalarExtensionSubspaceOrderIso (E := E) σ B)).slope
        (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M))⟩) =
    ((V.scalarExtension (L := L)).restrictOfMeasurableBase B).slope
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  dsimp only
  simp only [slope, scalarExtensionSubspaceOrderIso_finrank,
    degree_restrict_scalarExtension_algEquiv]

/-- All actual subspace degrees transport; taking both suprema proves
positive-degree invariance without assuming a maximizing subspace. -/
theorem positiveDegree_scalarExtension_algEquiv
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (σ : L ≃ₐ[K] M) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
    let _ := hcount.algebraicExtension_of_isAlgClosed (L := L)
    let _ := hcount.algebraicExtension_of_isAlgClosed (L := M)
    (V.scalarExtension (L := M)).positiveDegree
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M))⟩) =
    (V.scalarExtension (L := L)).positiveDegree
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
  let hM := hcount.algebraicExtension_of_isAlgClosed (L := M)
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
  let hMN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := M)
  apply le_antisymm
  · apply positiveDegree_le _ (hN := ⟨hMN⟩)
    intro B
    have hd := V.degree_restrict_scalarExtension_algEquiv σ.symm B
    exact (EReal.coe_le_coe_iff.mpr hd.symm.le).trans
      ((V.scalarExtension (L := L)).degree_restrict_le_positiveDegree
        (hN := ⟨hLN⟩) (scalarExtensionSubspaceOrderIso (E := E) σ.symm B))
  · apply positiveDegree_le _ (hN := ⟨hLN⟩)
    intro B
    have hd := V.degree_restrict_scalarExtension_algEquiv σ B
    exact (EReal.coe_le_coe_iff.mpr hd.symm.le).trans
      ((V.scalarExtension (L := M)).degree_restrict_le_positiveDegree
        (hN := ⟨hMN⟩) (scalarExtensionSubspaceOrderIso (E := E) σ B))

/-- Actual positive-rank subspaces and their means transport in both
directions, preserving maximal slope and its empty-supremum convention. -/
theorem maximalSlope_scalarExtension_algEquiv
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (σ : L ≃ₐ[K] M) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
    let _ := hcount.algebraicExtension_of_isAlgClosed (L := L)
    let _ := hcount.algebraicExtension_of_isAlgClosed (L := M)
    (V.scalarExtension (L := M)).maximalSlope
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M))⟩) =
    (V.scalarExtension (L := L)).maximalSlope
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
  let hM := hcount.algebraicExtension_of_isAlgClosed (L := M)
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
  let hMN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := M)
  apply le_antisymm
  · apply maximalSlope_le _ (hN := ⟨hMN⟩)
    intro B hB
    have hd := V.slope_restrict_scalarExtension_algEquiv σ.symm B
    have hr := scalarExtensionSubspaceOrderIso_finrank σ.symm B
    exact (EReal.coe_le_coe_iff.mpr hd.symm.le).trans
      ((V.scalarExtension (L := L)).slope_restrict_le_maximalSlope
        (scalarExtensionSubspaceOrderIso (E := E) σ.symm B) (hr.symm ▸ hB) (hN := ⟨hLN⟩))
  · apply maximalSlope_le _ (hN := ⟨hLN⟩)
    intro B hB
    have hd := V.slope_restrict_scalarExtension_algEquiv σ B
    have hr := scalarExtensionSubspaceOrderIso_finrank σ B
    exact (EReal.coe_le_coe_iff.mpr hd.symm.le).trans
      ((V.scalarExtension (L := M)).slope_restrict_le_maximalSlope
        (scalarExtensionSubspaceOrderIso (E := E) σ B) (hr.symm ▸ hB) (hN := ⟨hMN⟩))

end ArakelovGeometry.AdelicVectorBundle
