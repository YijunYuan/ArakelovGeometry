/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Ordered
public import ArakelovGeometry.AdelicVectorBundle.Operator.Height

import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Degree
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Restriction
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.OrderedDegree
import ArakelovGeometry.AdelicVectorBundle.Slope.Finite
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Modified degrees of actual general HN filtrations

The modified degree is the actual ordered sum; its normalized slope is
used in positive rank. General filtration functoriality compares these
actual sums, and Hermitian bundles recover their ordinary degrees.
-/

@[expose] public section

open scoped BigOperators

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u w w'

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S)
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]

/-- Source modified degree: the genuine sum of actual general ordered slopes. -/
def modifiedDegree : ℝ := ∑ j, V.generalHNOrderedSlope j

/-- Source modified mean in positive rank, naturally extended by zero in rank zero. -/
def modifiedSlope : ℝ := V.modifiedDegree / Module.finrank K V

/-- The actual empty ordered list has modified degree zero. -/
theorem modifiedDegree_eq_zero_of_finrank_eq_zero (hr : Module.finrank K V = 0) :
    V.modifiedDegree = 0 := by
  have : IsEmpty (Fin (Module.finrank K V)) := ⟨fun j ↦ by have hj := j.isLt; omega⟩
  simp [modifiedDegree]

/-- The natural zero-rank extension of the modified mean is zero. -/
theorem modifiedSlope_eq_zero_of_finrank_eq_zero (hr : Module.finrank K V = 0) :
    V.modifiedSlope = 0 := by
  simp only [modifiedSlope, hr, Nat.cast_zero, div_zero]

/-- Rank times the actual modified mean is the actual modified degree, also in rank zero. -/
theorem modifiedDegree_eq_rank_mul_modifiedSlope :
    V.modifiedDegree = (Module.finrank K V : ℝ) * V.modifiedSlope := by
  by_cases hr : Module.finrank K V = 0
  · rw [V.modifiedDegree_eq_zero_of_finrank_eq_zero hr,
      V.modifiedSlope_eq_zero_of_finrank_eq_zero hr, hr, Nat.cast_zero, mul_zero]
  · symm
    exact mul_div_cancel₀ _ (by exact_mod_cast hr)

/-- The actual general flag lower bound compares modified and ordinary degrees. -/
theorem modifiedDegree_le_degree : V.modifiedDegree ≤ V.degree :=
  V.sum_generalHNOrderedSlope_le_degree

/-- Normalization gives the corresponding actual mean-slope comparison. -/
theorem modifiedSlope_le_slope : V.modifiedSlope ≤ V.slope :=
  div_le_div_of_nonneg_right (V.modifiedDegree_le_degree) (Nat.cast_nonneg _)

/-- Every actual ordered slope is above the true minimum, so their actual
mean is above it in positive rank. No infinite minimum is replaced by its real part. -/
theorem minimalSlope_le_modifiedSlope (hr : 0 < Module.finrank K V) :
    V.minimalSlope ≤ (V.modifiedSlope : EReal) := by
  obtain ⟨c, hc⟩ := V.exists_minimalSlope_eq_coe hr
  have hj : ∀ j, c ≤ V.generalHNOrderedSlope j := by
    intro j
    exact EReal.coe_le_coe_iff.mp (by
      simpa only [hc] using V.minimalSlope_le_generalHNOrderedSlope j)
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (Module.finrank K V))))
    (fun j _ ↦ hj j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  rw [hc]
  apply EReal.coe_le_coe
  apply (le_div_iff₀ (by exact_mod_cast hr : (0 : ℝ) < Module.finrank K V)).mpr
  simpa only [modifiedDegree, mul_comm] using hs

/-- The actual ordered list is decreasing, so its mean is at most its first term. -/
theorem modifiedSlope_le_generalHNOrderedSlope_zero (hr : 0 < Module.finrank K V) :
    V.modifiedSlope ≤ V.generalHNOrderedSlope ⟨0, hr⟩ := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (Module.finrank K V))))
    (fun j _ ↦ V.generalHNOrderedSlope_antitone
      (show (⟨0, hr⟩ : Fin (Module.finrank K V)) ≤ j from Nat.zero_le j.val))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  apply (div_le_iff₀ (by exact_mod_cast hr : (0 : ℝ) < Module.finrank K V)).mpr
  simpa only [modifiedDegree, mul_comm] using hs

variable {E' : Type (max u w)} [AddCommGroup E'] [Module K E'] [FiniteDimensional K E']

/-- Actual Hermitian/general filtration agreement and the genuine ordered
sum degree formula identify modified degree with ordinary degree. -/
theorem modifiedDegree_eq_degree_of_isHermitian (W : AdelicVectorBundle.{max u w} S)
    [hW : W.IsHermitian] : W.modifiedDegree = W.degree := by
  unfold modifiedDegree
  simp_rw [W.generalHNOrderedSlope_eq_hermitianHNOrderedSlope]
  exact W.sum_hermitianHNOrderedSlope_eq_degree

/-- The actual Hermitian modified mean is its ordinary mean. -/
theorem modifiedSlope_eq_slope_of_isHermitian (W : AdelicVectorBundle.{max u w} S)
    [hW : W.IsHermitian] : W.modifiedSlope = W.slope := by
  unfold modifiedSlope slope
  rw [W.modifiedDegree_eq_degree_of_isHermitian]

variable {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- Any actual real upper bound for the height of a bijection compares the
genuine modified degrees, including the empty-rank case. -/
theorem modifiedDegree_le_of_bijective_of_mapHeight_le
    (W : AdelicVectorBundle S) (f : V →ₗ[K] W) (hf : Function.Bijective f)
    (c : ℝ) (hh : V.mapHeight W f ≤ (c : EReal)) :
    V.modifiedDegree ≤ W.modifiedDegree + (Module.finrank K W : ℝ) * c := by
  have hr := (LinearEquiv.ofBijective f hf).finrank_eq
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (Module.finrank K V))))
    (fun j _ ↦ V.generalHNOrderedSlope_le_of_injective_of_mapHeight_le W f hf.1 c hh j)
  have hcast : (∑ j : Fin (Module.finrank K V), W.generalHNOrderedSlope
      (Fin.castLE (LinearMap.finrank_le_finrank_of_injective hf.1) j)) =
      W.modifiedDegree := by
    calc
      _ = ∑ j : Fin (Module.finrank K V), W.generalHNOrderedSlope (Fin.cast hr j) := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
      _ = W.modifiedDegree := Fin.sum_congr' (W.generalHNOrderedSlope) hr
  have hfactor : (Module.finrank K V : ℝ) * c = (Module.finrank K W : ℝ) * c :=
    congrArg (fun n : ℕ ↦ (n : ℝ) * c) hr
  simpa only [Finset.sum_add_distrib, hcast, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, hfactor, modifiedDegree] using hs

/-- Source Proposition 4.3.55(1) with the true extended-real height.
Positive rank is established before multiplication by an infinite height. -/
theorem modifiedDegree_le_of_bijective
    (W : AdelicVectorBundle S) (f : V →ₗ[K] W)
    (hf : Function.Bijective f) (hr : 0 < Module.finrank K W) :
    (V.modifiedDegree : EReal) ≤ (W.modifiedDegree : EReal) +
      ((Module.finrank K W : ℝ) : EReal) * V.mapHeight W f := by
  by_cases ht : V.mapHeight W f = ⊤
  · have hp : (0 : EReal) < ((Module.finrank K W : ℝ) : EReal) :=
      EReal.coe_pos.mpr (Nat.cast_pos.mpr hr)
    rw [ht, EReal.mul_top_of_pos hp, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
    exact le_top
  · have : Nontrivial W := Module.finrank_pos_iff.mp hr
    have hb : V.mapHeight W f ≠ ⊥ :=
      (V.bot_lt_mapHeight W (LinearMap.ne_zero_of_surjective hf.2)).ne'
    obtain ⟨c, hc⟩ : ∃ c : ℝ, V.mapHeight W f = (c : EReal) := by
      lift V.mapHeight W f to ℝ using ⟨ht, hb⟩ with c
      exact ⟨c, rfl⟩
    rw [hc, ← EReal.coe_mul, ← EReal.coe_add]
    exact EReal.coe_le_coe
      (V.modifiedDegree_le_of_bijective_of_mapHeight_le W f hf c hc.le)

/-- Source Proposition 4.3.55(2): an actual injection bounds the first
ordered slope with no finite-height hypothesis supplied. -/
theorem generalHNOrderedSlope_zero_le_of_injective
    (W : AdelicVectorBundle S) (f : V →ₗ[K] W)
    (hi : Function.Injective f) (hr : 0 < Module.finrank K V) :
    (V.generalHNOrderedSlope ⟨0, hr⟩ : EReal) ≤
      (W.generalHNOrderedSlope
        ⟨0, hr.trans_le (LinearMap.finrank_le_finrank_of_injective hi)⟩ : EReal) +
      V.mapHeight W f := by
  by_cases ht : V.mapHeight W f = ⊤
  · rw [ht, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
    exact le_top
  · exact V.generalHNOrderedSlope_le_of_injective W f hi ht ⟨0, hr⟩

end

end ArakelovGeometry.AdelicVectorBundle
