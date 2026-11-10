/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.HermitianClosedHNScalarExtension

/-!
# The actual canonical Hermitian HN factor means under closed algebraic extension

The genuine remaining-quotient maxima identify corresponding canonical factor
means. Their real threshold cuts then identify the actual real HN filtration.
-/

open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [PerfectField K] [IsAlgClosed L]
  {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local instance hermitianClosedHNFactorScalarExtensionProper :
    (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- Corresponding actual canonical HN factors have identical real mean
slopes. The target index bound is produced from the actual length equality. -/
theorem slope_hermitianHNFactor_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) (i : ℕ)
    (hi : i < V.hermitianHNLength (Or.inr hcount) hN hH) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    let hLH := V.hermitianScalarExtension_isHermitian hcount hN hLN hH
    ∃ hj : i < W.hermitianHNLength hLS hLN hLH,
      (W.hermitianHNFactor hLS hLN hLH ⟨i, hj⟩).slope hLS hLN =
        (V.hermitianHNFactor (Or.inr hcount) hN hH ⟨i, hi⟩).slope (Or.inr hcount) hN := by
  intro hLN hLS W hLH
  change W.toNormFamily.IsHermitian hLN at hLH
  have hlen := V.hermitianHNLength_hermitianScalarExtension_of_isAlgClosed
    (L := L) hcount hN hH
  have hj : i < W.hermitianHNLength hLS hLN hLH := hlen ▸ hi
  refine ⟨hj, ?_⟩
  apply EReal.coe_injective
  calc
    _ = (W.quotientOfMeasurableBase (W.hermitianHNTerm hLS hLN hLH i) hLS).maximalSlope
        hLS hLN := W.slope_hermitianHNFactor_eq_maximalSlope_quotient hLS hLN hLH ⟨i, hj⟩
    _ = (W.quotientOfMeasurableBase
        ((V.hermitianHNTerm (Or.inr hcount) hN hH i).baseChange L) hLS).maximalSlope
          hLS hLN := congrArg (fun U : Submodule L (L ⊗[K] E) ↦
            (W.quotientOfMeasurableBase U hLS).maximalSlope hLS hLN)
              (V.hermitianHNTerm_baseChange_hermitianScalarExtension_of_isAlgClosed
                hcount hN hH i).symm
    _ = (V.quotientOfMeasurableBase
        (V.hermitianHNTerm (Or.inr hcount) hN hH i) (Or.inr hcount)).maximalSlope
          (Or.inr hcount) hN :=
      V.maximalSlope_quotient_hermitianScalarExtension_of_isAlgClosed hcount hN hH
        (V.hermitianHNTerm (Or.inr hcount) hN hH i)
    _ = _ := (V.slope_hermitianHNFactor_eq_maximalSlope_quotient
      (Or.inr hcount) hN hH ⟨i, hi⟩).symm


/-- The actual real threshold cut indices agree, including the empty factor
set and the empty retained set, through produced canonical factor means. -/
theorem hermitianHNCut_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) (t : ℝ) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    let hLH := V.hermitianScalarExtension_isHermitian hcount hN hLN hH
    V.hermitianHNCut (Or.inr hcount) hN hH t = W.hermitianHNCut hLS hLN hLH t := by
  intro hLN hLS W hLH
  change W.toNormFamily.IsHermitian hLN at hLH
  have hlen := V.hermitianHNLength_hermitianScalarExtension_of_isAlgClosed
    (L := L) hcount hN hH
  apply le_antisymm
  · apply Finset.sup_le_iff.mpr
    intro i hi
    obtain ⟨hj, hm⟩ := V.slope_hermitianHNFactor_hermitianScalarExtension_of_isAlgClosed
      (L := L) hcount hN hH i.val i.isLt
    let j : Fin (W.hermitianHNLength hLS hLN hLH) := ⟨i.val, hj⟩
    have ht : t ≤ (W.hermitianHNFactor hLS hLN hLH j).slope hLS hLN := by
      rw [hm]
      exact (Finset.mem_filter.mp hi).2
    exact Finset.le_sup (f := fun k : Fin (W.hermitianHNLength hLS hLN hLH) ↦ k.val + 1)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ j, ht⟩)
  · apply Finset.sup_le_iff.mpr
    intro j hj
    have hi : j.val < V.hermitianHNLength (Or.inr hcount) hN hH := hlen.symm ▸ j.isLt
    obtain ⟨hb, hm⟩ := V.slope_hermitianHNFactor_hermitianScalarExtension_of_isAlgClosed
      (L := L) hcount hN hH j.val hi
    let i : Fin (V.hermitianHNLength (Or.inr hcount) hN hH) := ⟨j.val, hi⟩
    have ht : t ≤ (V.hermitianHNFactor (Or.inr hcount) hN hH i).slope
        (Or.inr hcount) hN := by
      rw [← hm]
      exact (Finset.mem_filter.mp hj).2
    exact Finset.le_sup
      (f := fun k : Fin (V.hermitianHNLength (Or.inr hcount) hN hH) ↦ k.val + 1)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ i, ht⟩)

/-- The genuine canonical real HN filtration commutes with closed algebraic
Hermitian extension at every real threshold, in every rank. -/
theorem hermitianHNFiltration_baseChange_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) (t : ℝ) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    let hLH := V.hermitianScalarExtension_isHermitian hcount hN hLN hH
    (V.hermitianHNFiltration (Or.inr hcount) hN hH t).baseChange L =
      W.hermitianHNFiltration hLS hLN hLH t := by
  intro hLN hLS W hLH
  change (V.hermitianHNTerm (Or.inr hcount) hN hH
    (V.hermitianHNCut (Or.inr hcount) hN hH t)).baseChange L =
      W.hermitianHNTerm hLS hLN hLH (W.hermitianHNCut hLS hLN hLH t)
  rw [← V.hermitianHNCut_hermitianScalarExtension_of_isAlgClosed hcount hN hH t]
  exact V.hermitianHNTerm_baseChange_hermitianScalarExtension_of_isAlgClosed
    hcount hN hH _

end ArakelovGeometry.AdelicVectorBundle
