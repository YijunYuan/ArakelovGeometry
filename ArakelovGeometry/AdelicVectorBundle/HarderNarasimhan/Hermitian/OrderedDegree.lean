/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.Basic
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Basic

import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Degree
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.PositiveDegree
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Degree sums over actual ordered Hermitian HN slopes

Actual rank intervals identify the multiplicity of each produced factor in
the ordered slope list. Fibrewise finite summation then yields ordinary and
positive degree formulas, including the empty ordered list in rank zero.
-/

@[expose] public section

open scoped BigOperators

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S)
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]
  [hV : V.toNormFamily.IsHermitian]

/-- The actual factor rank is the difference between the dimensions of
its consecutive actual HN terms. -/
theorem finrank_hermitianHNFactor_eq_sub
    (i : Fin (V.hermitianHNLength)) :
    Module.finrank K ((V.hermitianHNTerm (i.val + 1)).map
      (V.hermitianHNTerm i.val).mkQ) =
      Module.finrank K (V.hermitianHNTerm (i.val + 1)) -
        Module.finrank K (V.hermitianHNTerm i.val) := by
  let U := V.hermitianHNTerm i.val
  let W := V.hermitianHNTerm (i.val + 1)
  have hUW : U ≤ W := V.hermitianHNTerm_monotone (Nat.le_succ _)
  have hr := (U.comap W.subtype).finrank_quotient_add_finrank
  rw [(Submodule.comapSubtypeEquivOfLe hUW).finrank_eq] at hr
  have hq := V.finrank_hermitianHNFlagQuotient_eq i
  change Module.finrank K (W ⧸ U.comap W.subtype) = Module.finrank K (W.map U.mkQ) at hq
  change Module.finrank K (W.map U.mkQ) = Module.finrank K W - Module.finrank K U
  omega

/-- Each ordered slot belongs to exactly the actual rank interval of its
factor, in both directions. -/
theorem hermitianHNFactorIndex_eq_iff_rank_interval
    (j : Fin (Module.finrank K V)) (i : Fin (V.hermitianHNLength)) :
    V.hermitianHNFactorIndex j = i ↔
      Module.finrank K (V.hermitianHNTerm i.val) ≤ j.val ∧
        j.val < Module.finrank K (V.hermitianHNTerm (i.val + 1)) := by
  constructor
  · rintro rfl
    exact V.hermitianHNFactorIndex_rank_interval j
  · exact V.hermitianHNFactorIndex_eq_of_rank_interval j i

/-- The number of actual ordered slots of a given factor is its actual
rank, including the final interval ending at the ambient rank. -/
theorem card_hermitianHNFactorIndex_fiber
    (i : Fin (V.hermitianHNLength)) :
    (Finset.univ.filter
      (fun j : Fin (Module.finrank K V) ↦ V.hermitianHNFactorIndex j = i)).card =
      Module.finrank K ((V.hermitianHNTerm (i.val + 1)).map
        (V.hermitianHNTerm i.val).mkQ) := by
  classical
  let a := Module.finrank K (V.hermitianHNTerm i.val)
  let b := Module.finrank K (V.hermitianHNTerm (i.val + 1))
  have hb : b ≤ Module.finrank K V := Submodule.finrank_le _
  have hc : (Finset.univ.filter
      (fun j : Fin (Module.finrank K V) ↦ V.hermitianHNFactorIndex j = i)).card =
      (Finset.Ico a b).card := by
    apply Finset.card_bij (fun j _ ↦ j.val)
    · intro j hj
      exact Finset.mem_Ico.mpr
        ((V.hermitianHNFactorIndex_eq_iff_rank_interval j i).mp
          (Finset.mem_filter.mp hj).2)
    · intro j _ k _ hjk
      exact Fin.ext hjk
    · intro k hk
      have hk' := Finset.mem_Ico.mp hk
      let j : Fin (Module.finrank K V) := ⟨k, hk'.2.trans_le hb⟩
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      exact (V.hermitianHNFactorIndex_eq_iff_rank_interval j i).mpr hk'
  rw [Nat.card_Ico] at hc
  exact hc.trans (V.finrank_hermitianHNFactor_eq_sub i).symm

/-- Summing any real function of the actual ordered slopes repeats each
actual factor mean with exactly its actual rank multiplicity. -/
theorem sum_hermitianHNOrderedSlope_apply (f : ℝ → ℝ) :
    (∑ j : Fin (Module.finrank K V), f (V.hermitianHNOrderedSlope j)) =
      ∑ i : Fin (V.hermitianHNLength),
        (Module.finrank K ((V.hermitianHNTerm (i.val + 1)).map
          (V.hermitianHNTerm i.val).mkQ) : ℝ) *
            f ((V.hermitianHNFactor i).slope) := by
  classical
  have hs := Finset.sum_fiberwise' (Finset.univ : Finset (Fin (Module.finrank K V)))
    (V.hermitianHNFactorIndex)
    (fun i ↦ f ((V.hermitianHNFactor i).slope))
  simpa only [Finset.sum_const, nsmul_eq_mul,
    V.card_hermitianHNFactorIndex_fiber, hermitianHNOrderedSlope] using hs.symm

/-- The actual ordered HN slopes sum to the original ordinary degree. -/
theorem sum_hermitianHNOrderedSlope_eq_degree :
    (∑ j : Fin (Module.finrank K V), V.hermitianHNOrderedSlope j) =
      V.degree :=
  (V.sum_hermitianHNOrderedSlope_apply id).trans
    (V.sum_hermitianHNFactor_rank_mul_slope_eq_degree)

/-- The positive parts of all actual ordered HN slopes sum to actual
positive degree; rank zero gives the genuine empty sum. -/
theorem positiveDegree_eq_sum_max_hermitianHNOrderedSlope :
    V.positiveDegree = ((∑ j : Fin (Module.finrank K V),
      max (V.hermitianHNOrderedSlope j) 0 : ℝ) : EReal) :=
  (V.positiveDegree_eq_sum_hermitianHNFactor_rank_mul_max_slope).trans
    (congrArg (fun x : ℝ ↦ (x : EReal))
      (V.sum_hermitianHNOrderedSlope_apply (fun x ↦ max x 0)).symm)

end

end ArakelovGeometry.AdelicVectorBundle
