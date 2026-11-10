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
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.quotientOfMeasurableBase P hS).degree hS hN = V.degree hS hN := by
  symm
  apply degree_eq_of_completed_isometry _ _
    (P.quotEquivOfEqBot hP).symm hS hN
  intro ω z
  simp only [quotientOfMeasurableBase_toNormFamily,
    Submodule.coe_quotEquivOfEqBot_symm]
  apply V.toNormFamily.pushforward_norm_of_injective
  apply LinearMap.ker_eq_bot.mp
  exact (Submodule.ker_mkQ P).trans hP

/-- The actual quotient by zero has the original degree. -/
theorem degree_quotient_bot (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.quotientOfMeasurableBase ⊥ hS).degree hS hN = V.degree hS hN :=
  V.degree_quotient_of_eq_bot ⊥ rfl hS hN

variable {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra K M]
  [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K M] [IsAlgClosed L] [IsAlgClosed M]

/-- The actual native subquotient degree transport compares restrictions by
taking lower endpoint zero, without replacing their norm families. -/
theorem degree_restrict_scalarExtension_algEquiv
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (σ : L ≃ₐ[K] M) (B : Submodule L (L ⊗[K] E)) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
    let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
    let hM := hcount.algebraicExtension_of_isAlgClosed (L := M)
    ((V.scalarExtension (L := M) hcount hN).restrictOfMeasurableBase
      (scalarExtensionSubspaceOrderIso (E := E) σ B) (Or.inr hM)).degree
        (Or.inr hM) (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M) hN) =
    ((V.scalarExtension (L := L) hcount hN).restrictOfMeasurableBase B (Or.inr hL)).degree
      (Or.inr hL) (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  have hd := V.degree_nativeSubquotient_algEquiv hcount hN σ B ⊥ bot_le
  dsimp only at hd
  let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
  let hM := hcount.algebraicExtension_of_isAlgClosed (L := M)
  let R := (V.scalarExtension (L := L) hcount hN).restrictOfMeasurableBase B (Or.inr hL)
  let T := (V.scalarExtension (L := M) hcount hN).restrictOfMeasurableBase
    (scalarExtensionSubspaceOrderIso (E := E) σ B) (Or.inr hM)
  have hbot : ((⊥ : Submodule L (L ⊗[K] E)).comap B.subtype) = ⊥ :=
    (Submodule.comap_bot _).trans (Submodule.ker_subtype B)
  have htbot : ((scalarExtensionSubspaceOrderIso (E := E) σ ⊥).comap
      (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype) = ⊥ := by
    rw [(scalarExtensionSubspaceOrderIso (E := E) σ).map_bot,
      Submodule.comap_bot, Submodule.ker_subtype]
  exact (T.degree_quotient_of_eq_bot _ htbot (Or.inr hM)
    (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M) hN)).symm.trans
      (hd.trans (R.degree_quotient_of_eq_bot _ hbot (Or.inr hL)
        (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN)))

/-- The transported actual restriction has the same mean degree in every
rank, including the existing real division convention in rank zero. -/
theorem slope_restrict_scalarExtension_algEquiv
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (σ : L ≃ₐ[K] M) (B : Submodule L (L ⊗[K] E)) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
    let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
    let hM := hcount.algebraicExtension_of_isAlgClosed (L := M)
    ((V.scalarExtension (L := M) hcount hN).restrictOfMeasurableBase
      (scalarExtensionSubspaceOrderIso (E := E) σ B) (Or.inr hM)).slope
        (Or.inr hM) (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M) hN) =
    ((V.scalarExtension (L := L) hcount hN).restrictOfMeasurableBase B (Or.inr hL)).slope
      (Or.inr hL) (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  dsimp only
  simp only [slope, scalarExtensionSubspaceOrderIso_finrank,
    degree_restrict_scalarExtension_algEquiv]

/-- All actual subspace degrees transport; taking both suprema proves
positive-degree invariance without assuming a maximizing subspace. -/
theorem positiveDegree_scalarExtension_algEquiv
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (σ : L ≃ₐ[K] M) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
    let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
    let hM := hcount.algebraicExtension_of_isAlgClosed (L := M)
    (V.scalarExtension (L := M) hcount hN).positiveDegree (Or.inr hM)
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M) hN) =
    (V.scalarExtension (L := L) hcount hN).positiveDegree (Or.inr hL)
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
  let hM := hcount.algebraicExtension_of_isAlgClosed (L := M)
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
  let hMN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M) hN
  apply le_antisymm
  · apply positiveDegree_le _ (Or.inr hM) hMN
    intro B
    have hd := V.degree_restrict_scalarExtension_algEquiv hcount hN σ.symm B
    exact (EReal.coe_le_coe_iff.mpr hd.symm.le).trans
      ((V.scalarExtension (L := L) hcount hN).degree_restrict_le_positiveDegree
        (Or.inr hL) hLN (scalarExtensionSubspaceOrderIso (E := E) σ.symm B))
  · apply positiveDegree_le _ (Or.inr hL) hLN
    intro B
    have hd := V.degree_restrict_scalarExtension_algEquiv hcount hN σ B
    exact (EReal.coe_le_coe_iff.mpr hd.symm.le).trans
      ((V.scalarExtension (L := M) hcount hN).degree_restrict_le_positiveDegree
        (Or.inr hM) hMN (scalarExtensionSubspaceOrderIso (E := E) σ B))

/-- Actual positive-rank subspaces and their means transport in both
directions, preserving maximal slope and its empty-supremum convention. -/
theorem maximalSlope_scalarExtension_algEquiv
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (σ : L ≃ₐ[K] M) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
    let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
    let hM := hcount.algebraicExtension_of_isAlgClosed (L := M)
    (V.scalarExtension (L := M) hcount hN).maximalSlope (Or.inr hM)
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M) hN) =
    (V.scalarExtension (L := L) hcount hN).maximalSlope (Or.inr hL)
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
  let hM := hcount.algebraicExtension_of_isAlgClosed (L := M)
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
  let hMN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M) hN
  apply le_antisymm
  · apply maximalSlope_le _ (Or.inr hM) hMN
    intro B hB
    have hd := V.slope_restrict_scalarExtension_algEquiv hcount hN σ.symm B
    have hr := scalarExtensionSubspaceOrderIso_finrank σ.symm B
    exact (EReal.coe_le_coe_iff.mpr hd.symm.le).trans
      ((V.scalarExtension (L := L) hcount hN).slope_restrict_le_maximalSlope
        (scalarExtensionSubspaceOrderIso (E := E) σ.symm B) (hr.symm ▸ hB) (Or.inr hL) hLN)
  · apply maximalSlope_le _ (Or.inr hL) hLN
    intro B hB
    have hd := V.slope_restrict_scalarExtension_algEquiv hcount hN σ B
    have hr := scalarExtensionSubspaceOrderIso_finrank σ B
    exact (EReal.coe_le_coe_iff.mpr hd.symm.le).trans
      ((V.scalarExtension (L := M) hcount hN).slope_restrict_le_maximalSlope
        (scalarExtensionSubspaceOrderIso (E := E) σ B) (hr.symm ▸ hB) (Or.inr hM) hMN)

end ArakelovGeometry.AdelicVectorBundle
