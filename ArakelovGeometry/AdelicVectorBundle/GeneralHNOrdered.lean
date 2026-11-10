/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.GeneralHN
import Mathlib.Data.Fintype.Fin

/-!
# The actual ordered slopes of a general adelic bundle

Source Definition 4.3.47 is the literal real supremum of the actual
filtration rank cuts. Left constancy makes every such supremum attained.
-/

namespace ArakelovGeometry

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace AdelicVectorBundle

variable [S.IsProper] (V : AdelicVectorBundle S E)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)


/-- The actual real rank cut is nonempty because the filtration attains top. -/
theorem generalHNRankCut_nonempty (j : Fin (Module.finrank K E)) :
    Set.Nonempty {t : ℝ | j.val < Module.finrank K (V.generalHNFiltration hS hN t)} := by
  obtain ⟨t, ht⟩ := V.exists_generalHNFiltration_eq_top hS hN
  refine ⟨t, ?_⟩
  change j.val < Module.finrank K (V.generalHNFiltration hS hN t)
  rw [ht, finrank_top]
  exact j.isLt

/-- The actual real rank cut is bounded above because the filtration attains zero. -/
theorem generalHNRankCut_bddAbove (j : Fin (Module.finrank K E)) :
    BddAbove {t : ℝ | j.val < Module.finrank K (V.generalHNFiltration hS hN t)} := by
  obtain ⟨b, hb⟩ := V.exists_generalHNFiltration_eq_bot hS hN
  refine ⟨b, fun t ht ↦ ?_⟩
  by_contra htb
  have hle := V.antitone_generalHNFiltration hS hN (le_of_not_ge htb)
  rw [hb] at hle
  have hr := Submodule.finrank_mono hle
  rw [finrank_bot] at hr
  exact (Nat.not_lt_zero j.val) (ht.trans_le hr)

/-- Source Definition 4.3.47, with a zero-based slot and the literal actual
rank-threshold supremum. No surrogate flag or supplied jump is used. -/
def generalHNOrderedSlope (j : Fin (Module.finrank K E)) : ℝ :=
  sSup {t : ℝ | j.val < Module.finrank K (V.generalHNFiltration hS hN t)}

/-- Left constancy of the actual epsilon filtration makes each supremum attained. -/
theorem lt_finrank_generalHNFiltration_orderedSlope (j : Fin (Module.finrank K E)) :
    j.val < Module.finrank K
      (V.generalHNFiltration hS hN (V.generalHNOrderedSlope hS hN j)) := by
  let c := V.generalHNOrderedSlope hS hN j
  obtain ⟨δ, hδ, hleft⟩ := V.generalHNFiltration_locallyConstant_left hS hN c
  have hbelow : c - δ / 2 < c := by linarith
  obtain ⟨a, ha, hac⟩ := exists_lt_of_lt_csSup (V.generalHNRankCut_nonempty hS hN j) hbelow
  have hle := V.antitone_generalHNFiltration hS hN hac.le
  have hr := ha.trans_le (Submodule.finrank_mono hle)
  rw [hleft (δ / 2) (by linarith) (by linarith)] at hr
  exact hr

/-- The actual rank cuts are precisely the closed rays below the produced slopes. -/
theorem le_generalHNOrderedSlope_iff_lt_filtration_finrank (t : ℝ)
    (j : Fin (Module.finrank K E)) :
    t ≤ V.generalHNOrderedSlope hS hN j ↔
      j.val < Module.finrank K (V.generalHNFiltration hS hN t) := by
  constructor
  · intro ht
    exact (V.lt_finrank_generalHNFiltration_orderedSlope hS hN j).trans_le
      (Submodule.finrank_mono (V.antitone_generalHNFiltration hS hN ht))
  · exact le_csSup (V.generalHNRankCut_bddAbove hS hN j)

/-- The actual general ordered slopes form a nonincreasing list. -/
theorem generalHNOrderedSlope_antitone : Antitone (V.generalHNOrderedSlope hS hN) := by
  intro i j hij
  change i.val ≤ j.val at hij
  apply (V.le_generalHNOrderedSlope_iff_lt_filtration_finrank hS hN _ i).mpr
  exact hij.trans_lt (V.lt_finrank_generalHNFiltration_orderedSlope hS hN j)


/-- The last source supremum is the actual minimal slope, with a positive-rank
 guard so that the zero-bundle top endpoint is never cast to a real number. -/
theorem generalHNOrderedSlope_last_eq_minimalSlope (hr : 0 < Module.finrank K E) :
    (V.generalHNOrderedSlope hS hN (⟨0, hr⟩ : Fin (Module.finrank K E)).rev : EReal) =
      V.minimalSlope hS hN := by
  let j : Fin (Module.finrank K E) := (⟨0, hr⟩ : Fin (Module.finrank K E)).rev
  have htop : V.generalHNFiltration hS hN (V.generalHNOrderedSlope hS hN j) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hj := V.lt_finrank_generalHNFiltration_orderedSlope hS hN j
    have hle := (V.generalHNFiltration hS hN (V.generalHNOrderedSlope hS hN j)).finrank_le
    change Module.finrank K E - (0 + 1) < _ at hj
    omega
  apply le_antisymm ((V.generalHNFiltration_eq_top_iff hS hN _).mp htop)
  obtain ⟨c, hc⟩ := V.exists_minimalSlope_eq_coe hS hN hr
  rw [hc]
  apply EReal.coe_le_coe
  apply (V.le_generalHNOrderedSlope_iff_lt_filtration_finrank hS hN c j).mpr
  have ht : V.generalHNFiltration hS hN c = ⊤ :=
    (V.generalHNFiltration_eq_top_iff hS hN c).mpr hc.ge
  rw [ht, finrank_top]
  exact j.isLt

/-- The true rank of the actual general filtration counts precisely its
ordered slopes above the real threshold, including an empty list. -/
theorem generalHNFiltration_finrank_eq_card (t : ℝ) :
    Module.finrank K (V.generalHNFiltration hS hN t) =
      (Finset.univ.filter (fun j : Fin (Module.finrank K E) ↦
        t ≤ V.generalHNOrderedSlope hS hN j)).card := by
  classical
  have hle := (V.generalHNFiltration hS hN t).finrank_le
  calc
    Module.finrank K (V.generalHNFiltration hS hN t) =
        min (Module.finrank K E) (Module.finrank K (V.generalHNFiltration hS hN t)) :=
      (min_eq_right hle).symm
    _ = (Finset.univ.filter (fun j : Fin (Module.finrank K E) ↦
        j.val < Module.finrank K (V.generalHNFiltration hS hN t))).card :=
      Fin.card_filter_val_lt.symm
    _ = _ := by
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        V.le_generalHNOrderedSlope_iff_lt_filtration_finrank hS hN]

/-- Every general ordered slope is bounded by the actual ambient maximum. -/
theorem generalHNOrderedSlope_le_maximalSlope (j : Fin (Module.finrank K E)) :
    (V.generalHNOrderedSlope hS hN j : EReal) ≤ V.maximalSlope hS hN := by
  have hr : 0 < Module.finrank K E := (Nat.zero_le j.val).trans_lt j.isLt
  obtain ⟨c, hc⟩ := V.exists_maximalSlope_eq_coe hS hN hr
  rw [hc]
  apply EReal.coe_le_coe
  by_contra hμ
  have hcμ : c < V.generalHNOrderedSlope hS hN j := lt_of_not_ge hμ
  have hz := V.generalHNFiltration_eq_bot_of_maximalSlope_lt hS hN
    (V.generalHNOrderedSlope hS hN j) (hc.trans_lt (EReal.coe_lt_coe hcμ))
  have hj := V.lt_finrank_generalHNFiltration_orderedSlope hS hN j
  rw [hz, finrank_bot] at hj
  exact Nat.not_lt_zero j.val hj

/-- Every actual general ordered slope is at least the actual minimal slope. -/
theorem minimalSlope_le_generalHNOrderedSlope (j : Fin (Module.finrank K E)) :
    V.minimalSlope hS hN ≤ (V.generalHNOrderedSlope hS hN j : EReal) := by
  have hr : 0 < Module.finrank K E := (Nat.zero_le j.val).trans_lt j.isLt
  rw [← V.generalHNOrderedSlope_last_eq_minimalSlope hS hN hr]
  apply EReal.coe_le_coe
  apply V.generalHNOrderedSlope_antitone hS hN
  change j.val ≤ Module.finrank K E - (0 + 1)
  have hj := j.isLt
  omega


/-- Every nonzero actual restricted minimum is bounded by the first general
ordered jump, whose criterion is positive actual filtration rank. -/
theorem minimalSlope_restrict_le_generalHNOrderedSlope_zero
    (hr : 0 < Module.finrank K E) (U : Submodule K E) (hU : U ≠ ⊥) :
    (V.restrictOfMeasurableBase U hS).minimalSlope hS hN ≤
      (V.generalHNOrderedSlope hS hN ⟨0, hr⟩ : EReal) := by
  have hrU : 0 < Module.finrank K U := Nat.pos_of_ne_zero
    (fun hz ↦ hU (Submodule.finrank_eq_zero.mp hz))
  obtain ⟨c, hc⟩ := (V.restrictOfMeasurableBase U hS).exists_minimalSlope_eq_coe hS hN hrU
  have hUF := V.le_generalHNFiltration_of_le_minimalSlope_restrict hS hN U c hc.ge
  rw [hc]
  apply EReal.coe_le_coe
  apply (V.le_generalHNOrderedSlope_iff_lt_filtration_finrank hS hN c ⟨0, hr⟩).mpr
  exact hrU.trans_le (Submodule.finrank_mono hUF)

/-- The first actual ordered jump is the greatest restricted minimal slope,
attained by its produced nonzero actual threshold subspace. -/
theorem isGreatest_minimalSlope_restrict_generalHNOrderedSlope_zero
    (hr : 0 < Module.finrank K E) :
    IsGreatest {m : EReal | ∃ U : Submodule K E, U ≠ ⊥ ∧
      (V.restrictOfMeasurableBase U hS).minimalSlope hS hN = m}
      (V.generalHNOrderedSlope hS hN ⟨0, hr⟩ : EReal) := by
  let U := V.generalHNFiltration hS hN (V.generalHNOrderedSlope hS hN ⟨0, hr⟩)
  have hU : U ≠ ⊥ := by
    intro hz
    have hpos := V.lt_finrank_generalHNFiltration_orderedSlope hS hN ⟨0, hr⟩
    change 0 < Module.finrank K U at hpos
    rw [hz, finrank_bot] at hpos
    exact Nat.not_lt_zero 0 hpos
  have he : (V.restrictOfMeasurableBase U hS).minimalSlope hS hN =
      (V.generalHNOrderedSlope hS hN ⟨0, hr⟩ : EReal) :=
    le_antisymm (V.minimalSlope_restrict_le_generalHNOrderedSlope_zero hS hN hr U hU)
      (V.le_minimalSlope_restrict_generalHNFiltration hS hN _)
  refine ⟨⟨U, hU, he⟩, ?_⟩
  rintro m ⟨M, hM, rfl⟩
  exact V.minimalSlope_restrict_le_generalHNOrderedSlope_zero hS hN hr M hM

section HermitianComparison

variable {E' : Type (max u w)} [AddCommGroup E'] [Module K E']
  [FiniteDimensional K E'] (W : AdelicVectorBundle S E')

/-- The literal general ordered list agrees with the already produced actual
Hermitian list because their actual filtration rank cuts agree. -/
theorem generalHNOrderedSlope_eq_hermitianHNOrderedSlope
    (hW : W.toNormFamily.IsHermitian hN) (j : Fin (Module.finrank K E')) :
    W.generalHNOrderedSlope hS hN j = W.hermitianHNOrderedSlope hS hN hW j := by
  have hcut : ∀ t : ℝ, t ≤ W.generalHNOrderedSlope hS hN j ↔
      t ≤ W.hermitianHNOrderedSlope hS hN hW j := by
    intro t
    rw [W.le_generalHNOrderedSlope_iff_lt_filtration_finrank hS hN t j,
      W.generalHNFiltration_eq_hermitianHNFiltration hS hN hW t,
      W.le_hermitianHNOrderedSlope_iff_lt_filtration_finrank hS hN hW t j]
  exact le_antisymm ((hcut _).mp le_rfl) ((hcut _).mpr le_rfl)

end HermitianComparison

end AdelicVectorBundle

end

end ArakelovGeometry
