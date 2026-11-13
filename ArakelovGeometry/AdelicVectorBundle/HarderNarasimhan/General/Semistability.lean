/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Modified

import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Restriction
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Upper
import ArakelovGeometry.AdelicVectorBundle.Slope.Finite
import ArakelovGeometry.AdelicVectorBundle.Slope.Quotient
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Semistability of actual general HN filtrations

Source semistability means a positive-rank bundle with a constant actual
general ordered-slope list. Its one-jump, actual restricted-minimum and
modified-mean characterizations retain this positive-rank scope. The
ordinary mean-slope predicate has its separate existing name.
-/

@[expose] public section

open scoped BigOperators

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle.{w} S)
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]

/-- Source general semistability: positive rank and a constant actual
general ordered-slope list. Rank zero is excluded rather than accepted
through a vacuously constant empty list. -/
class IsSemistable : Prop where
  /-- Semistability excludes the zero bundle. -/
  rank_pos : 0 < Module.finrank K V
  /-- All entries of the ordered slope list have the same value. -/
  constant_slopes : ∃ b : ℝ, ∀ j, V.generalHNOrderedSlope j = b

/-- The source nonzero convention excludes the zero bundle. -/
theorem not_isSemistable_of_finrank_eq_zero (hr : Module.finrank K V = 0) :
    ¬ V.IsSemistable := by
  intro h
  have hp := h.1
  omega

/-- Every actual rank-one bundle has a singleton ordered list and is
semistable, without a Hermitianity or characteristic assumption. -/
theorem isSemistable_of_finrank_eq_one (hr : Module.finrank K V = 1) :
    V.IsSemistable := by
  have hp : 0 < Module.finrank K V := by omega
  refine ⟨hp, V.generalHNOrderedSlope ⟨0, hp⟩, ?_⟩
  intro j
  have hj : j = ⟨0, hp⟩ := Fin.ext (by have hj := j.isLt; omega)
  rw [hj]

instance isSemistable_of_isLine [hV : V.IsLine] : V.IsSemistable :=
  V.isSemistable_of_finrank_eq_one hV.rank_eq_one

/-- A constant actual list has the actual minimum as its common value,
because its last entry is the true minimal slope. -/
theorem isSemistable_iff_generalHNOrderedSlope_eq_minimalSlope
    (hr : 0 < Module.finrank K V) :
    V.IsSemistable ↔
      ∀ j, (V.generalHNOrderedSlope j : EReal) = V.minimalSlope := by
  constructor
  · rintro ⟨hp, b, hb⟩ j
    have hm := V.generalHNOrderedSlope_last_eq_minimalSlope hp
    simpa only [hb] using hm
  · intro h
    let j := (⟨0, hr⟩ : Fin (Module.finrank K V)).rev
    refine ⟨hr, V.generalHNOrderedSlope j, ?_⟩
    intro i
    exact_mod_cast (h i).trans (h j).symm

/-- In positive rank, the source predicate is equivalent to the actual
filtration having one included jump and no other intermediate subspace. -/
theorem isSemistable_iff_exists_generalHNFiltration_eq_ite
    (hr : 0 < Module.finrank K V) :
    V.IsSemistable ↔ ∃ b : ℝ, ∀ t,
      V.generalHNFiltration t = if t ≤ b then ⊤ else ⊥ := by
  classical
  constructor
  · rintro ⟨hp, b, hb⟩
    have hm : (b : EReal) = V.minimalSlope := by
      simpa only [hb] using V.generalHNOrderedSlope_last_eq_minimalSlope hp
    refine ⟨b, fun t ↦ ?_⟩
    split_ifs with ht
    · exact (V.generalHNFiltration_eq_top_iff t).mpr
        ((EReal.coe_le_coe ht).trans hm.le)
    · apply Submodule.finrank_eq_zero.mp
      rw [V.generalHNFiltration_finrank_eq_card]
      simp only [hb]
      simp [ht]
  · rintro ⟨b, hb⟩
    refine ⟨hr, b, fun j ↦ le_antisymm ?_ ?_⟩
    · by_contra h
      have hj := V.lt_finrank_generalHNFiltration_orderedSlope j
      rw [hb, ite_eq_right h, finrank_bot] at hj
      exact Nat.not_lt_zero j.val hj
    · apply (V.le_generalHNOrderedSlope_iff_lt_filtration_finrank b j).mpr
      rw [hb, ite_eq_left le_rfl, finrank_top]
      exact j.isLt

/-- Source condition (2): semistability is equivalent to bounding the true
minimum of every actual nonzero restriction by the true ambient minimum.
The reverse implication consumes the produced first threshold subspace. -/
theorem isSemistable_iff_minimalSlope_restrict_le (hr : 0 < Module.finrank K V) :
    V.IsSemistable ↔ ∀ U : Submodule K V, U ≠ ⊥ →
      (V.restrictOfMeasurableBase U).minimalSlope ≤ V.minimalSlope := by
  constructor
  · intro h U hU
    have hm := (V.isSemistable_iff_generalHNOrderedSlope_eq_minimalSlope hr).mp h
    rw [← hm ⟨0, hr⟩]
    exact V.minimalSlope_restrict_le_generalHNOrderedSlope_zero hr U hU
  · intro h
    obtain ⟨U, hU, hm⟩ := (V.isGreatest_minimalSlope_restrict_generalHNOrderedSlope_zero
      hr).1
    have hf : (V.generalHNOrderedSlope ⟨0, hr⟩ : EReal) ≤ V.minimalSlope := by
      rw [← hm]
      exact h U hU
    refine ⟨hr, V.generalHNOrderedSlope ⟨0, hr⟩, fun j ↦ le_antisymm ?_ ?_⟩
    · exact V.generalHNOrderedSlope_antitone (Nat.zero_le _)
    · exact EReal.coe_le_coe_iff.mp
        (hf.trans (V.minimalSlope_le_generalHNOrderedSlope j))

/-- Source condition (3): in positive rank the actual modified mean equals
the true minimal slope exactly when the actual ordered list is constant.
The true minimum is proved finite before any real comparison. -/
theorem isSemistable_iff_modifiedSlope_eq_minimalSlope (hr : 0 < Module.finrank K V) :
    V.IsSemistable ↔ (V.modifiedSlope : EReal) = V.minimalSlope := by
  classical
  constructor
  · rintro ⟨hp, b, hb⟩
    have hm : (b : EReal) = V.minimalSlope := by
      simpa only [hb] using V.generalHNOrderedSlope_last_eq_minimalSlope hp
    have he : V.modifiedDegree = (Module.finrank K V : ℝ) * b := by
      simp only [modifiedDegree, hb, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have hs : V.modifiedSlope = b := by
      simp only [modifiedSlope, he]
      exact mul_div_cancel_left₀ b (Nat.cast_ne_zero.mpr hp.ne')
    simpa only [hs] using hm
  · intro h
    obtain ⟨b, hb⟩ := V.exists_minimalSlope_eq_coe hr
    have hs : V.modifiedSlope = b := by exact_mod_cast h.trans hb
    have he : (∑ j, V.generalHNOrderedSlope j) =
        ∑ _j : Fin (Module.finrank K V), b := by
      change V.modifiedDegree = _
      rw [V.modifiedDegree_eq_rank_mul_modifiedSlope, hs]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hj : ∀ j ∈ (Finset.univ : Finset (Fin (Module.finrank K V))),
        b ≤ V.generalHNOrderedSlope j := by
      intro j _
      have ht := V.minimalSlope_le_generalHNOrderedSlope j
      rw [hb] at ht
      exact EReal.coe_le_coe_iff.mp ht
    have hall := (Finset.sum_eq_sum_iff_of_le hj).mp he.symm
    exact ⟨hr, b, fun j ↦ (hall j (Finset.mem_univ j)).symm⟩

/-- The actual first threshold produces a positive-rank semistable
restriction: every intrinsic slot is squeezed between its true minimum
and the ambient first slot through the actual restriction comparison. -/
theorem isSemistable_restrict_generalHNFiltration_orderedSlope_zero
    (hr : 0 < Module.finrank K V) :
    (V.restrictOfMeasurableBase
      (V.generalHNFiltration (V.generalHNOrderedSlope ⟨0, hr⟩))).IsSemistable
        := by
  let U := V.generalHNFiltration (V.generalHNOrderedSlope ⟨0, hr⟩)
  have hp : 0 < Module.finrank K U :=
    V.lt_finrank_generalHNFiltration_orderedSlope ⟨0, hr⟩
  have hm := V.minimalSlope_restrict_generalHNFiltration_orderedSlope ⟨0, hr⟩
  refine ⟨hp, V.generalHNOrderedSlope ⟨0, hr⟩, fun j ↦ le_antisymm ?_ ?_⟩
  · exact (V.generalHNOrderedSlope_restrict_le U j).trans
      (V.generalHNOrderedSlope_antitone (Nat.zero_le _))
  · have hl := (V.restrictOfMeasurableBase U).minimalSlope_le_generalHNOrderedSlope
      j
    rw [hm] at hl
    exact EReal.coe_le_coe_iff.mp hl

/-- The actual first-threshold restriction has modified mean equal to
the actual ambient first slope, with no assumed factor semistability. -/
theorem modifiedSlope_restrict_generalHNFiltration_orderedSlope_zero
    (hr : 0 < Module.finrank K V) :
    (V.restrictOfMeasurableBase
      (V.generalHNFiltration (V.generalHNOrderedSlope ⟨0, hr⟩))).modifiedSlope
        = V.generalHNOrderedSlope ⟨0, hr⟩ := by
  have hs := V.isSemistable_restrict_generalHNFiltration_orderedSlope_zero hr
  let R := V.restrictOfMeasurableBase
    (V.generalHNFiltration (V.generalHNOrderedSlope ⟨0, hr⟩))
  have hm := (R.isSemistable_iff_modifiedSlope_eq_minimalSlope hs.1).mp hs
  rw [V.minimalSlope_restrict_generalHNFiltration_orderedSlope ⟨0, hr⟩] at hm
  exact_mod_cast hm

/-- Source Proposition 4.3.59, the actual nonzero-subspace modified-mean
criterion. The converse uses the produced first threshold, rather than
an assumed semistable flag. -/
theorem isSemistable_iff_modifiedSlope_restrict_le (hr : 0 < Module.finrank K V) :
    V.IsSemistable ↔ ∀ U : Submodule K V, U ≠ ⊥ →
      (V.restrictOfMeasurableBase U).modifiedSlope ≤ V.modifiedSlope := by
  classical
  constructor
  · intro h U hU
    have hp : 0 < Module.finrank K U := Nat.pos_of_ne_zero
      (fun hz ↦ hU (Submodule.finrank_eq_zero.mp hz))
    have hm := (V.isSemistable_iff_modifiedSlope_eq_minimalSlope hr).mp h
    have hf := (V.isSemistable_iff_generalHNOrderedSlope_eq_minimalSlope hr).mp h
      ⟨0, hr⟩
    have he : V.generalHNOrderedSlope ⟨0, hr⟩ = V.modifiedSlope := by
      exact_mod_cast hf.trans hm.symm
    exact ((V.restrictOfMeasurableBase U).modifiedSlope_le_generalHNOrderedSlope_zero
      hp).trans
      ((V.generalHNOrderedSlope_restrict_le U ⟨0, hp⟩).trans he.le)
  · intro h
    let U := V.generalHNFiltration (V.generalHNOrderedSlope ⟨0, hr⟩)
    have hp : 0 < Module.finrank K U :=
      V.lt_finrank_generalHNFiltration_orderedSlope ⟨0, hr⟩
    have hU : U ≠ ⊥ := fun hz ↦ by
      rw [hz, finrank_bot] at hp
      exact Nat.not_lt_zero 0 hp
    have hl := h U hU
    rw [V.modifiedSlope_restrict_generalHNFiltration_orderedSlope_zero hr] at hl
    have hm : V.modifiedSlope = V.generalHNOrderedSlope ⟨0, hr⟩ :=
      le_antisymm (V.modifiedSlope_le_generalHNOrderedSlope_zero hr) hl
    have he : (∑ j, V.generalHNOrderedSlope j) =
        ∑ _j : Fin (Module.finrank K V), V.generalHNOrderedSlope ⟨0, hr⟩ := by
      change V.modifiedDegree = _
      rw [V.modifiedDegree_eq_rank_mul_modifiedSlope, hm]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hj : ∀ j ∈ (Finset.univ : Finset (Fin (Module.finrank K V))),
        V.generalHNOrderedSlope j ≤ V.generalHNOrderedSlope ⟨0, hr⟩ :=
      fun j _ ↦ V.generalHNOrderedSlope_antitone (Nat.zero_le _)
    have hall := (Finset.sum_eq_sum_iff_of_le hj).mp he
    exact ⟨hr, V.generalHNOrderedSlope ⟨0, hr⟩,
      fun j ↦ hall j (Finset.mem_univ j)⟩

/-- Source Proposition 4.3.59, the actual positive-rank quotient
modified-mean criterion. The reverse implication consumes a genuine
near-minimal quotient from the defining infimum, with no factor hypothesis. -/
theorem isSemistable_iff_modifiedSlope_le_quotient (hr : 0 < Module.finrank K V) :
    V.IsSemistable ↔ ∀ U : Submodule K V, 0 < Module.finrank K (V ⧸ U) →
      V.modifiedSlope ≤ (V.quotientOfMeasurableBase U).modifiedSlope := by
  constructor
  · intro h U hU
    apply EReal.coe_le_coe_iff.mp
    rw [(V.isSemistable_iff_modifiedSlope_eq_minimalSlope hr).mp h]
    exact (V.minimalSlope_le_minimalSlope_quotient U).trans
      ((V.quotientOfMeasurableBase U).minimalSlope_le_modifiedSlope hU)
  · intro h
    apply (V.isSemistable_iff_modifiedSlope_eq_minimalSlope hr).mpr
    apply le_antisymm _ (V.minimalSlope_le_modifiedSlope hr)
    by_contra hn
    obtain ⟨U, hp, _, hmax, _⟩ := V.exists_quotient_maximalSlope_lt_of_minimalSlope_lt
      (V.modifiedSlope) (lt_of_not_ge hn)
    have hl := (EReal.coe_le_coe (h U hp)).trans
      ((EReal.coe_le_coe ((V.quotientOfMeasurableBase U).modifiedSlope_le_slope
)).trans ((V.quotientOfMeasurableBase U).slope_le_maximalSlope hp))
    exact not_lt_of_ge hl hmax

end

end ArakelovGeometry.AdelicVectorBundle
