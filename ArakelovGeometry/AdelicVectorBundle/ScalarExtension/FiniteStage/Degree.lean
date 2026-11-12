/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Countable
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Algebraic.ClosureApproximation
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Bundle

import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.FiniteStage.RestrictionIsometry
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Subspace.ComplexDescent
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Subspace.Degree
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Tower.Transport
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual finite-stage degrees of native algebraic-closure subspaces

Common density is produced at each finite field of definition and at the
algebraic closure. The actual completed restriction isometry and canonical
measure-preserving tower transport compare their genuine determinant degrees.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
universe u v wL wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Native closure restriction has its actual finite-stage degree through the
canonical completed subspace equivalence and measure-preserving tower map. -/
theorem degree_restrict_scalarExtension_finiteStage [S.IsProper]
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (F : AdelicStructure.FiniteIntermediateField K L) (hi : ∃ a : F, a ^ 2 = -1)
    (B : Submodule F (F ⊗[K] E)) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    let _ := hcount.algebraicExtension_of_finiteDimensional (L := F)
    let _ := hcount.algebraicExtension_of_isAlgClosed (L := L)
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    ((V.scalarExtension (L := L)).restrictOfMeasurableBase
      ((B.baseChange L).map c.toLinearMap)).degree
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
    ((V.scalarExtension (L := F)).restrictOfMeasurableBase
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
  let e := (Submodule.toBaseChange.toLinearEquiv L B).trans (c.submoduleMap (B.baseChange L))
  let B₀ := (V.scalarExtension (L := F)).restrictOfMeasurableBase B
  let W := B₀.scalarExtension (L := L) (hS := hF) (hN := ⟨hFN⟩)
  let R := (V.scalarExtension (L := L)).restrictOfMeasurableBase
    ((B.baseChange L).map c.toLinearMap)
  change R.degree (hN := ⟨hLN⟩) = B₀.degree (hN := ⟨hFN⟩)
  have he : R.degree (hN := ⟨hLN⟩) = W.degree (hN := ⟨hTN⟩) :=
    degree_eq_of_tower_completed_isometry F.toIntermediateField W R e
      (hND := ⟨hLN⟩) (hNT := ⟨hTN⟩) (fun x z ↦
        V.toNormFamily.scalarExtension_restrict_finiteStage_norm_eq F hi B x z)
  exact he.trans (B₀.degree_scalarExtension_of_isAlgClosed (hcount := hF) (hN := ⟨hFN⟩))

/-- One actual finite complexifying field preserves the native degrees of every
member of a prescribed finite family, together with ranks and all inclusions. -/
theorem exists_complexFiniteStage_native_degrees [S.IsProper]
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
          ((V.scalarExtension (L := L)).restrictOfMeasurableBase
            (A i)).degree
            (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
          ((V.scalarExtension (L := F)).restrictOfMeasurableBase
            (B i)).degree
            (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F))⟩) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  dsimp only
  obtain ⟨F, hi, B, hB, hr, hinc⟩ := exists_complexFiniteStage_subspaces A
  refine ⟨F, hi, B, hB, hr, hinc, ?_⟩
  intro i
  have hd := V.degree_restrict_scalarExtension_finiteStage F hi (B i)
  dsimp only at hd
  rw [← hB i]
  exact hd

/-- An actual strict exhaustive closure flag descends with every native degree,
including the zero/whole endpoints and the length-zero zero-space flag. -/
theorem exists_complexFiniteStage_flag_native_degrees [S.IsProper]
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (n : ℕ) (A : Fin (n + 1) → Submodule L (L ⊗[K] E)) (hA : StrictMono A)
    (hbot : A 0 = ⊥) (htop : A (Fin.last n) = ⊤) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let _ := hcount.algebraicExtension_of_isAlgClosed (L := L)
    ∃ F : AdelicStructure.FiniteIntermediateField K L, (∃ a : F, a ^ 2 = -1) ∧
      ∃ B : Fin (n + 1) → Submodule F (F ⊗[K] E),
        (∀ i, Submodule.map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap
          ((B i).baseChange L) = A i) ∧
        (∀ i, Module.finrank F (B i) = Module.finrank L (A i)) ∧
        StrictMono B ∧ B 0 = ⊥ ∧ B (Fin.last n) = ⊤ ∧
        ∀ i,
          let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
          let _ := hcount.algebraicExtension_of_finiteDimensional (L := F)
          ((V.scalarExtension (L := L)).restrictOfMeasurableBase
            (A i)).degree
            (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
          ((V.scalarExtension (L := F)).restrictOfMeasurableBase
            (B i)).degree
            (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F))⟩) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  dsimp only
  obtain ⟨F, hi, B, hB, hr, hstrict, hb, ht⟩ :=
    exists_complexFiniteStage_flag n A hA hbot htop
  refine ⟨F, hi, B, hB, hr, hstrict, hb, ht, ?_⟩
  intro i
  have hd := V.degree_restrict_scalarExtension_finiteStage F hi (B i)
  dsimp only at hd
  rw [← hB i]
  exact hd

end ArakelovGeometry.AdelicVectorBundle
