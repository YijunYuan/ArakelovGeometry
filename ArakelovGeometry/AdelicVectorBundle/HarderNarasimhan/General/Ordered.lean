/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Basic

import ArakelovGeometry.AdelicVectorBundle.Slope.Finite
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# The actual ordered slopes of a general adelic bundle

Source Definition 4.3.47 is the literal real supremum of the actual
filtration rank cuts. Left constancy makes every such supremum attained.
-/

@[expose] public section

namespace ArakelovGeometry

noncomputable section

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace AdelicVectorBundle

variable [S.IsProper] (V : AdelicVectorBundle S)
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]


/-- The actual real rank cut is nonempty because the filtration attains top. -/
theorem hnRankCut_nonempty (j : Fin (Module.finrank K V)) :
    Set.Nonempty {t : ℝ | j.val < Module.finrank K (V.hnFiltration t)} := by
  obtain ⟨t, ht⟩ := V.exists_hnFiltration_eq_top
  refine ⟨t, ?_⟩
  change j.val < Module.finrank K (V.hnFiltration t)
  rw [ht, finrank_top]
  exact j.isLt

/-- The actual real rank cut is bounded above because the filtration attains zero. -/
theorem hnRankCut_bddAbove (j : Fin (Module.finrank K V)) :
    BddAbove {t : ℝ | j.val < Module.finrank K (V.hnFiltration t)} := by
  obtain ⟨b, hb⟩ := V.exists_hnFiltration_eq_bot
  refine ⟨b, fun t ht ↦ ?_⟩
  by_contra htb
  have hle := V.antitone_hnFiltration (le_of_not_ge htb)
  rw [hb] at hle
  have hr := Submodule.finrank_mono hle
  rw [finrank_bot] at hr
  exact (Nat.not_lt_zero j.val) (ht.trans_le hr)

/-- Source Definition 4.3.47, with a zero-based slot and the literal actual
rank-threshold supremum. No surrogate flag or supplied jump is used. -/
def hnSlope (j : Fin (Module.finrank K V)) : ℝ :=
  sSup {t : ℝ | j.val < Module.finrank K (V.hnFiltration t)}

/-- Left constancy of the actual epsilon filtration makes each supremum attained. -/
theorem lt_finrank_hnFiltration_orderedSlope (j : Fin (Module.finrank K V)) :
    j.val < Module.finrank K
      (V.hnFiltration (V.hnSlope j)) := by
  let c := V.hnSlope j
  obtain ⟨δ, hδ, hleft⟩ := V.hnFiltration_locallyConstant_left c
  have hbelow : c - δ / 2 < c := by linarith
  obtain ⟨a, ha, hac⟩ := exists_lt_of_lt_csSup (V.hnRankCut_nonempty j) hbelow
  have hle := V.antitone_hnFiltration hac.le
  have hr := ha.trans_le (Submodule.finrank_mono hle)
  rw [hleft (δ / 2) (by linarith) (by linarith)] at hr
  exact hr

/-- The actual rank cuts are precisely the closed rays below the produced slopes. -/
theorem le_hnSlope_iff_lt_filtration_finrank (t : ℝ)
    (j : Fin (Module.finrank K V)) :
    t ≤ V.hnSlope j ↔
      j.val < Module.finrank K (V.hnFiltration t) := by
  constructor
  · intro ht
    exact (V.lt_finrank_hnFiltration_orderedSlope j).trans_le
      (Submodule.finrank_mono (V.antitone_hnFiltration ht))
  · exact le_csSup (V.hnRankCut_bddAbove j)

/-- The actual general ordered slopes form a nonincreasing list. -/
theorem hnSlope_antitone : Antitone (V.hnSlope) := by
  intro i j hij
  change i.val ≤ j.val at hij
  apply (V.le_hnSlope_iff_lt_filtration_finrank _ i).mpr
  exact hij.trans_lt (V.lt_finrank_hnFiltration_orderedSlope j)


/-- The last source supremum is the actual minimal slope, with a positive-rank
 guard so that the zero-bundle top endpoint is never cast to a real number. -/
theorem hnSlope_last_eq_minimalSlope (hr : 0 < Module.finrank K V) :
    (V.hnSlope (⟨0, hr⟩ : Fin (Module.finrank K V)).rev : EReal) =
      V.minimalSlope := by
  let j : Fin (Module.finrank K V) := (⟨0, hr⟩ : Fin (Module.finrank K V)).rev
  have htop : V.hnFiltration (V.hnSlope j) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hj := V.lt_finrank_hnFiltration_orderedSlope j
    have hle := (V.hnFiltration (V.hnSlope j)).finrank_le
    change Module.finrank K V - (0 + 1) < _ at hj
    omega
  apply le_antisymm ((V.hnFiltration_eq_top_iff _).mp htop)
  obtain ⟨c, hc⟩ := V.exists_minimalSlope_eq_coe hr
  rw [hc]
  apply EReal.coe_le_coe
  apply (V.le_hnSlope_iff_lt_filtration_finrank c j).mpr
  have ht : V.hnFiltration c = ⊤ :=
    (V.hnFiltration_eq_top_iff c).mpr hc.ge
  rw [ht, finrank_top]
  exact j.isLt

/-- The true rank of the actual general filtration counts precisely its
ordered slopes above the real threshold, including an empty list. -/
theorem hnFiltration_finrank_eq_card (t : ℝ) :
    Module.finrank K (V.hnFiltration t) =
      (Finset.univ.filter (fun j : Fin (Module.finrank K V) ↦
        t ≤ V.hnSlope j)).card := by
  classical
  have hle := (V.hnFiltration t).finrank_le
  calc
    Module.finrank K (V.hnFiltration t) =
        min (Module.finrank K V) (Module.finrank K (V.hnFiltration t)) :=
      (min_eq_right hle).symm
    _ = (Finset.univ.filter (fun j : Fin (Module.finrank K V) ↦
        j.val < Module.finrank K (V.hnFiltration t))).card :=
      Fin.card_filter_val_lt.symm
    _ = _ := by
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        V.le_hnSlope_iff_lt_filtration_finrank]

/-- Every general ordered slope is bounded by the actual ambient maximum. -/
theorem hnSlope_le_maximalSlope (j : Fin (Module.finrank K V)) :
    (V.hnSlope j : EReal) ≤ V.maximalSlope := by
  have hr : 0 < Module.finrank K V := (Nat.zero_le j.val).trans_lt j.isLt
  obtain ⟨c, hc⟩ := V.exists_maximalSlope_eq_coe hr
  rw [hc]
  apply EReal.coe_le_coe
  by_contra hμ
  have hcμ : c < V.hnSlope j := lt_of_not_ge hμ
  have hz := V.hnFiltration_eq_bot_of_maximalSlope_lt
    (V.hnSlope j) (hc.trans_lt (EReal.coe_lt_coe hcμ))
  have hj := V.lt_finrank_hnFiltration_orderedSlope j
  rw [hz, finrank_bot] at hj
  exact Nat.not_lt_zero j.val hj

/-- Every actual general ordered slope is at least the actual minimal slope. -/
theorem minimalSlope_le_hnSlope (j : Fin (Module.finrank K V)) :
    V.minimalSlope ≤ (V.hnSlope j : EReal) := by
  have hr : 0 < Module.finrank K V := (Nat.zero_le j.val).trans_lt j.isLt
  rw [← V.hnSlope_last_eq_minimalSlope hr]
  apply EReal.coe_le_coe
  apply V.hnSlope_antitone
  change j.val ≤ Module.finrank K V - (0 + 1)
  have hj := j.isLt
  omega


/-- Every nonzero actual restricted minimum is bounded by the first general
ordered jump, whose criterion is positive actual filtration rank. -/
theorem minimalSlope_restrict_le_hnSlope_zero
    (hr : 0 < Module.finrank K V) (U : Submodule K V) (hU : U ≠ ⊥) :
    (V.restrictOfNormMeasurability U).minimalSlope ≤
      (V.hnSlope ⟨0, hr⟩ : EReal) := by
  have hrU : 0 < Module.finrank K U := Nat.pos_of_ne_zero
    (fun hz ↦ hU (Submodule.finrank_eq_zero.mp hz))
  obtain ⟨c, hc⟩ := (V.restrictOfNormMeasurability U).exists_minimalSlope_eq_coe hrU
  have hUF := V.le_hnFiltration_of_le_minimalSlope_restrict U c hc.ge
  rw [hc]
  apply EReal.coe_le_coe
  apply (V.le_hnSlope_iff_lt_filtration_finrank c ⟨0, hr⟩).mpr
  exact hrU.trans_le (Submodule.finrank_mono hUF)

/-- The first actual ordered jump is the greatest restricted minimal slope,
attained by its produced nonzero actual threshold subspace. -/
theorem isGreatest_minimalSlope_restrict_hnSlope_zero
    (hr : 0 < Module.finrank K V) :
    IsGreatest {m : EReal | ∃ U : Submodule K V, U ≠ ⊥ ∧
      (V.restrictOfNormMeasurability U).minimalSlope = m}
      (V.hnSlope ⟨0, hr⟩ : EReal) := by
  let U := V.hnFiltration (V.hnSlope ⟨0, hr⟩)
  have hU : U ≠ ⊥ := by
    intro hz
    have hpos := V.lt_finrank_hnFiltration_orderedSlope ⟨0, hr⟩
    change 0 < Module.finrank K U at hpos
    rw [hz, finrank_bot] at hpos
    exact Nat.not_lt_zero 0 hpos
  have he : (V.restrictOfNormMeasurability U).minimalSlope =
      (V.hnSlope ⟨0, hr⟩ : EReal) :=
    le_antisymm (V.minimalSlope_restrict_le_hnSlope_zero hr U hU)
      (V.le_minimalSlope_restrict_hnFiltration _)
  refine ⟨⟨U, hU, he⟩, ?_⟩
  rintro m ⟨M, hM, rfl⟩
  exact V.minimalSlope_restrict_le_hnSlope_zero hr M hM

section HermitianComparison

variable {E' : Type (max u w)} [AddCommGroup E'] [Module K E']
  [FiniteDimensional K E'] (W : AdelicVectorBundle.{max u w} S)

/-- The literal general ordered list agrees with the already produced actual
Hermitian list because their actual filtration rank cuts agree. -/
theorem hnSlope_eq_hermitianHNOrderedSlope
    [hW : W.toNormFamily.IsHermitian] (j : Fin (Module.finrank K W)) :
    W.hnSlope j = W.hermitianHNOrderedSlope j := by
  have hcut : ∀ t : ℝ, t ≤ W.hnSlope j ↔
      t ≤ W.hermitianHNOrderedSlope j := by
    intro t
    rw [W.le_hnSlope_iff_lt_filtration_finrank t j,
      W.hnFiltration_eq_hermitianHNFiltration t,
      W.le_hermitianHNOrderedSlope_iff_lt_filtration_finrank t j]
  exact le_antisymm ((hcut _).mp le_rfl) ((hcut _).mpr le_rfl)

end HermitianComparison

end AdelicVectorBundle

end

end ArakelovGeometry
