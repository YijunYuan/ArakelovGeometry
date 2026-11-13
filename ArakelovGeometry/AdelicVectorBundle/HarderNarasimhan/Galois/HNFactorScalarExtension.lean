/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.HermitianComparison.DeterminantDegree

import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Galois.HNScalarExtension
import Mathlib.CategoryTheory.Category.Init

/-!
# The actual canonical Hermitian HN factor means under finite Galois extension

The genuine remaining-quotient maxima identify corresponding canonical factor
means. Their real threshold cuts then identify the actual real HN filtration.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [FiniteDimensional K L] [IsGalois K L]
  {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local instance hermitianGaloisHNFactorScalarExtensionProper :
    (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- Corresponding actual canonical HN factors have identical real mean
slopes. The target index bound is produced from the actual length equality. -/
theorem slope_hermitianHNFactor_hermitianScalarExtension_of_finiteGalois
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (i : ℕ)
    (hi : i < V.hermitianHNLength) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    let hLH := V.hermitianScalarExtension_isHermitian (hL := ⟨hLN⟩)
    ∃ hj : i < W.hermitianHNLength (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH),
      (W.hermitianHNFactor (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) ⟨i, hj⟩).slope (hS := ⟨hLS⟩)
          (hN := ⟨hLN⟩) =
        (V.hermitianHNFactor ⟨i, hi⟩).slope := by
  intro hLN hLS W hLH
  change W.toNormFamily.IsHermitian (hS := ⟨hLN⟩) at hLH
  have hlen := V.hermitianHNLength_hermitianScalarExtension_of_finiteGalois
    (L := L)
  have hj : i < W.hermitianHNLength (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) := hlen ▸ hi
  refine ⟨hj, ?_⟩
  apply EReal.coe_injective
  calc
    _ = (W.quotientOfNormMeasurability (W.hermitianHNTerm (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) i)
        (hS := ⟨hLS⟩)).maximalSlope
        (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) := W.slope_hermitianHNFactor_eq_maximalSlope_quotient
            (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) ⟨i, hj⟩
    _ = (W.quotientOfNormMeasurability
        ((V.hermitianHNTerm i).baseChange L) (hS := ⟨hLS⟩)).maximalSlope
          (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) := congrArg (fun U : Submodule L (L ⊗[K] V) ↦
            (W.quotientOfNormMeasurability U (hS := ⟨hLS⟩)).maximalSlope (hS := ⟨hLS⟩)
              (hN := ⟨hLN⟩))
              (V.hermitianHNTerm_baseChange_hermitianScalarExtension_of_finiteGalois
                 i).symm
    _ = (V.quotientOfNormMeasurability
        (V.hermitianHNTerm i)).maximalSlope
          :=
      V.maximalSlope_quotient_hermitianScalarExtension_of_finiteGalois
        (V.hermitianHNTerm i)
    _ = _ := (V.slope_hermitianHNFactor_eq_maximalSlope_quotient
      ⟨i, hi⟩).symm


/-- The actual real threshold cut indices agree, including the empty factor
set and the empty retained set, through produced canonical factor means. -/
theorem hermitianHNCut_hermitianScalarExtension_of_finiteGalois
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (t : ℝ) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    let hLH := V.hermitianScalarExtension_isHermitian (hL := ⟨hLN⟩)
    V.hermitianHNCut t = W.hermitianHNCut (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) t := by
  intro hLN hLS W hLH
  change W.toNormFamily.IsHermitian (hS := ⟨hLN⟩) at hLH
  have hlen := V.hermitianHNLength_hermitianScalarExtension_of_finiteGalois
    (L := L)
  apply le_antisymm
  · apply Finset.sup_le_iff.mpr
    intro i hi
    obtain ⟨hj, hm⟩ := V.slope_hermitianHNFactor_hermitianScalarExtension_of_finiteGalois
      (L := L) i.val i.isLt
    let j : Fin (W.hermitianHNLength (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH)) := ⟨i.val, hj⟩
    have ht : t ≤ (W.hermitianHNFactor (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) j).slope
        (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) := by
      rw [hm]
      exact (Finset.mem_filter.mp hi).2
    exact Finset.le_sup (f := fun k : Fin (W.hermitianHNLength (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
        (hV := hLH)) ↦ k.val + 1)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ j, ht⟩)
  · apply Finset.sup_le_iff.mpr
    intro j hj
    have hi : j.val < V.hermitianHNLength := hlen.symm ▸ j.isLt
    obtain ⟨hb, hm⟩ := V.slope_hermitianHNFactor_hermitianScalarExtension_of_finiteGalois
      (L := L) j.val hi
    let i : Fin (V.hermitianHNLength) := ⟨j.val, hi⟩
    have ht : t ≤ (V.hermitianHNFactor i).slope
        := by
      rw [← hm]
      exact (Finset.mem_filter.mp hj).2
    exact Finset.le_sup
      (f := fun k : Fin (V.hermitianHNLength) ↦ k.val + 1)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ i, ht⟩)

/-- The genuine canonical real HN filtration commutes with finite Galois
Hermitian extension at every real threshold, in every rank. -/
theorem hermitianHNFiltration_baseChange_hermitianScalarExtension_of_finiteGalois
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (t : ℝ) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    let hLH := V.hermitianScalarExtension_isHermitian (hL := ⟨hLN⟩)
    (V.hermitianHNFiltration t).baseChange L =
      W.hermitianHNFiltration (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) t := by
  intro hLN hLS W hLH
  change (V.hermitianHNTerm
    (V.hermitianHNCut t)).baseChange L =
      W.hermitianHNTerm (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) (W.hermitianHNCut (hS := ⟨hLS⟩)
          (hN := ⟨hLN⟩) (hV := hLH) t)
  rw [← V.hermitianHNCut_hermitianScalarExtension_of_finiteGalois t]
  exact V.hermitianHNTerm_baseChange_hermitianScalarExtension_of_finiteGalois
     _

end ArakelovGeometry.AdelicVectorBundle
