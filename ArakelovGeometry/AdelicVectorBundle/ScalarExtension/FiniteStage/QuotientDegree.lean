/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Countable
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Algebraic.ClosureApproximation
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Bundle

import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.FiniteStage.Degree
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.QuotientEquiv
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Subspace.Degree
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual finite-stage native quotient degrees

Canonical completed quotient isometries and measure-preserving place towers
identify genuine quotient degrees at a produced complexifying finite stage.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
universe u v wL wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

omit [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
private theorem finrank_eq_of_baseChange_equiv
    {F X Y : Type*} [Field F] [Algebra F L] [AddCommGroup X] [Module F X]
    [AddCommGroup Y] [Module L Y] (e : (L ⊗[F] X) ≃ₗ[L] Y) :
    Module.finrank L Y = Module.finrank F X :=
  e.finrank_eq.symm.trans Module.finrank_baseChange

omit [FiniteDimensional K E] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- The actual quotient rank is preserved by the canonical finite-stage
quotient equivalence, including zero and whole-space quotients. -/
theorem rank_quotient_scalarExtension_finiteStage
    (F : AdelicStructure.FiniteIntermediateField K L) (B : Submodule F (F ⊗[K] E)) :
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    Module.finrank L ((L ⊗[K] E) ⧸ ((B.baseChange L).map c.toLinearMap)) =
      Module.finrank F ((F ⊗[K] E) ⧸ B) := by
  dsimp only
  exact finrank_eq_of_baseChange_equiv (finiteStageQuotientEquiv (L := L) F B)

/-- The genuine native closure quotient has its actual complexifying
finite-stage degree through the canonical completed quotient isometry. -/
theorem degree_quotient_scalarExtension_finiteStage [S.IsProper]
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (F : AdelicStructure.FiniteIntermediateField K L) (hi : ∃ a : F, a ^ 2 = -1)
    (B : Submodule F (F ⊗[K] E)) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    let _ := hcount.algebraicExtension_of_finiteDimensional (L := F)
    let _ := hcount.algebraicExtension_of_isAlgClosed (L := L)
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    ((V.scalarExtension (L := L)).quotientOfMeasurableBase
      ((B.baseChange L).map c.toLinearMap)).degree
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
    ((V.scalarExtension (L := F)).quotientOfMeasurableBase
      B).degree
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F))⟩) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
  let hF := hcount.algebraicExtension_of_finiteDimensional (L := F)
  let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
  let hT := hF.algebraicExtension_of_isAlgClosed (L := L)
  let hFN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := F)
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
  let hTN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) (hS := ⟨hFN⟩)
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
  let e := finiteStageQuotientEquiv (L := L) F B
  let Q₀ := (V.scalarExtension (L := F)).quotientOfMeasurableBase B
  let W := Q₀.scalarExtension (L := L) (hS := hF) (hN := ⟨hFN⟩)
  let R := (V.scalarExtension (L := L)).quotientOfMeasurableBase
    ((B.baseChange L).map c.toLinearMap)
  change R.degree (hN := ⟨hLN⟩) = Q₀.degree (hN := ⟨hFN⟩)
  exact (degree_eq_of_tower_completed_isometry F.toIntermediateField W R e
    (hND := ⟨hLN⟩) (hNT := ⟨hTN⟩) (fun x z ↦
      V.toNormFamily.scalarExtension_quotient_finiteStage_equiv_norm_eq F hi B x z)).trans
        (Q₀.degree_scalarExtension_of_isAlgClosed (hcount := hF) (hN := ⟨hFN⟩))

/-- One produced complexifying finite field preserves the native restricted
and quotient degrees and ranks of every actual finite family. -/
theorem exists_complexFiniteStage_native_subspace_quotient_degrees [S.IsProper]
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    {ι : Type*} [Finite ι] (A : ι → Submodule L (L ⊗[K] E)) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let _ := hcount.algebraicExtension_of_isAlgClosed (L := L)
    ∃ F : AdelicStructure.FiniteIntermediateField K L, (∃ a : F, a ^ 2 = -1) ∧
      ∃ B : ι → Submodule F (F ⊗[K] E),
        (∀ i, Submodule.map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap
          ((B i).baseChange L) = A i) ∧
        (∀ i, Module.finrank F (B i) = Module.finrank L (A i)) ∧
        (∀ i j, B i ≤ B j ↔ A i ≤ A j) ∧
        ∀ i,
          let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
          let _ := hcount.algebraicExtension_of_finiteDimensional (L := F)
          (((V.scalarExtension (L := L)).restrictOfMeasurableBase
            (A i)).degree
            (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
          ((V.scalarExtension (L := F)).restrictOfMeasurableBase
            (B i)).degree
            (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F))⟩)) ∧
          (((V.scalarExtension (L := L)).quotientOfMeasurableBase
            (A i)).degree
            (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
          ((V.scalarExtension (L := F)).quotientOfMeasurableBase
            (B i)).degree
            (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F))⟩)) ∧
          Module.finrank L ((L ⊗[K] E) ⧸ A i) =
            Module.finrank F ((F ⊗[K] E) ⧸ B i) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  dsimp only
  obtain ⟨F, hi, B, hB, hr, hinc, hd⟩ :=
    V.exists_complexFiniteStage_native_degrees A
  refine ⟨F, hi, B, hB, hr, hinc, ?_⟩
  intro i
  refine ⟨hd i, ?_, ?_⟩
  · have hq := V.degree_quotient_scalarExtension_finiteStage F hi (B i)
    dsimp only at hq
    rw [← hB i]
    exact hq
  · rw [← hB i]
    exact rank_quotient_scalarExtension_finiteStage F (B i)

end ArakelovGeometry.AdelicVectorBundle
