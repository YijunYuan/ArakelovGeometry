/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.GeneralHNDegree
import ArakelovGeometry.AdelicVectorBundle.HermitianHNOrderedDegree

/-!
# Modified degrees of actual general HN filtrations

The modified degree is the actual ordered sum; its normalized slope is
used in positive rank. General filtration functoriality compares these
actual sums, and Hermitian bundles recover their ordinary degrees.
-/

open scoped BigOperators

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S E)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)

/-- Source modified degree: the genuine sum of actual general ordered slopes. -/
def modifiedDegree : ℝ := ∑ j, V.generalHNOrderedSlope hS hN j

/-- Source modified mean in positive rank, naturally extended by zero in rank zero. -/
def modifiedSlope : ℝ := V.modifiedDegree hS hN / Module.finrank K E

/-- The actual empty ordered list has modified degree zero. -/
theorem modifiedDegree_eq_zero_of_finrank_eq_zero (hr : Module.finrank K E = 0) :
    V.modifiedDegree hS hN = 0 := by
  have : IsEmpty (Fin (Module.finrank K E)) := ⟨fun j ↦ by have hj := j.isLt; omega⟩
  simp [modifiedDegree]

/-- The natural zero-rank extension of the modified mean is zero. -/
theorem modifiedSlope_eq_zero_of_finrank_eq_zero (hr : Module.finrank K E = 0) :
    V.modifiedSlope hS hN = 0 := by
  simp only [modifiedSlope, hr, Nat.cast_zero, div_zero]

/-- Rank times the actual modified mean is the actual modified degree, also in rank zero. -/
theorem modifiedDegree_eq_rank_mul_modifiedSlope :
    V.modifiedDegree hS hN = (Module.finrank K E : ℝ) * V.modifiedSlope hS hN := by
  by_cases hr : Module.finrank K E = 0
  · rw [V.modifiedDegree_eq_zero_of_finrank_eq_zero hS hN hr,
      V.modifiedSlope_eq_zero_of_finrank_eq_zero hS hN hr, hr, Nat.cast_zero, mul_zero]
  · symm
    exact mul_div_cancel₀ _ (by exact_mod_cast hr)

/-- The actual general flag lower bound compares modified and ordinary degrees. -/
theorem modifiedDegree_le_degree : V.modifiedDegree hS hN ≤ V.degree hS hN :=
  V.sum_generalHNOrderedSlope_le_degree hS hN

/-- Normalization gives the corresponding actual mean-slope comparison. -/
theorem modifiedSlope_le_slope : V.modifiedSlope hS hN ≤ V.slope hS hN :=
  div_le_div_of_nonneg_right (V.modifiedDegree_le_degree hS hN) (Nat.cast_nonneg _)

/-- Every actual ordered slope is above the true minimum, so their actual
mean is above it in positive rank. No infinite minimum is replaced by its real part. -/
theorem minimalSlope_le_modifiedSlope (hr : 0 < Module.finrank K E) :
    V.minimalSlope hS hN ≤ (V.modifiedSlope hS hN : EReal) := by
  obtain ⟨c, hc⟩ := V.exists_minimalSlope_eq_coe hS hN hr
  have hj : ∀ j, c ≤ V.generalHNOrderedSlope hS hN j := by
    intro j
    exact EReal.coe_le_coe_iff.mp (by
      simpa only [hc] using V.minimalSlope_le_generalHNOrderedSlope hS hN j)
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (Module.finrank K E))))
    (fun j _ ↦ hj j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  rw [hc]
  apply EReal.coe_le_coe
  apply (le_div_iff₀ (by exact_mod_cast hr : (0 : ℝ) < Module.finrank K E)).mpr
  simpa only [modifiedDegree, mul_comm] using hs

/-- The actual ordered list is decreasing, so its mean is at most its first term. -/
theorem modifiedSlope_le_generalHNOrderedSlope_zero (hr : 0 < Module.finrank K E) :
    V.modifiedSlope hS hN ≤ V.generalHNOrderedSlope hS hN ⟨0, hr⟩ := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (Module.finrank K E))))
    (fun j _ ↦ V.generalHNOrderedSlope_antitone hS hN
      (show (⟨0, hr⟩ : Fin (Module.finrank K E)) ≤ j from Nat.zero_le j.val))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  apply (div_le_iff₀ (by exact_mod_cast hr : (0 : ℝ) < Module.finrank K E)).mpr
  simpa only [modifiedDegree, mul_comm] using hs

variable {E' : Type (max u w)} [AddCommGroup E'] [Module K E'] [FiniteDimensional K E']

/-- Actual Hermitian/general filtration agreement and the genuine ordered
sum degree formula identify modified degree with ordinary degree. -/
theorem modifiedDegree_eq_degree_of_isHermitian (W : AdelicVectorBundle S E')
    (hW : W.IsHermitian hN) : W.modifiedDegree hS hN = W.degree hS hN := by
  unfold modifiedDegree
  simp_rw [W.generalHNOrderedSlope_eq_hermitianHNOrderedSlope hS hN hW]
  exact W.sum_hermitianHNOrderedSlope_eq_degree hS hN hW

/-- The actual Hermitian modified mean is its ordinary mean. -/
theorem modifiedSlope_eq_slope_of_isHermitian (W : AdelicVectorBundle S E')
    (hW : W.IsHermitian hN) : W.modifiedSlope hS hN = W.slope hS hN := by
  unfold modifiedSlope slope
  rw [W.modifiedDegree_eq_degree_of_isHermitian hS hN hW]

variable {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- Any actual real upper bound for the height of a bijection compares the
genuine modified degrees, including the empty-rank case. -/
theorem modifiedDegree_le_of_bijective_of_mapHeight_le
    (W : AdelicVectorBundle S F) (f : E →ₗ[K] F) (hf : Function.Bijective f)
    (c : ℝ) (hh : V.mapHeight W f ≤ (c : EReal)) :
    V.modifiedDegree hS hN ≤ W.modifiedDegree hS hN + (Module.finrank K F : ℝ) * c := by
  have hr := (LinearEquiv.ofBijective f hf).finrank_eq
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (Module.finrank K E))))
    (fun j _ ↦ V.generalHNOrderedSlope_le_of_injective_of_mapHeight_le hS hN W f hf.1 c hh j)
  have hcast : (∑ j : Fin (Module.finrank K E), W.generalHNOrderedSlope hS hN
      (Fin.castLE (LinearMap.finrank_le_finrank_of_injective hf.1) j)) =
      W.modifiedDegree hS hN := by
    calc
      _ = ∑ j : Fin (Module.finrank K E), W.generalHNOrderedSlope hS hN (Fin.cast hr j) := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
      _ = W.modifiedDegree hS hN := Fin.sum_congr' (W.generalHNOrderedSlope hS hN) hr
  have hfactor : (Module.finrank K E : ℝ) * c = (Module.finrank K F : ℝ) * c :=
    congrArg (fun n : ℕ ↦ (n : ℝ) * c) hr
  simpa only [Finset.sum_add_distrib, hcast, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, hfactor, modifiedDegree] using hs

/-- Source Proposition 4.3.55(1) with the true extended-real height.
Positive rank is established before multiplication by an infinite height. -/
theorem modifiedDegree_le_of_bijective
    (W : AdelicVectorBundle S F) (f : E →ₗ[K] F)
    (hf : Function.Bijective f) (hr : 0 < Module.finrank K F) :
    (V.modifiedDegree hS hN : EReal) ≤ (W.modifiedDegree hS hN : EReal) +
      ((Module.finrank K F : ℝ) : EReal) * V.mapHeight W f := by
  by_cases ht : V.mapHeight W f = ⊤
  · have hp : (0 : EReal) < ((Module.finrank K F : ℝ) : EReal) :=
      EReal.coe_pos.mpr (Nat.cast_pos.mpr hr)
    rw [ht, EReal.mul_top_of_pos hp, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
    exact le_top
  · have : Nontrivial F := Module.finrank_pos_iff.mp hr
    have hb : V.mapHeight W f ≠ ⊥ :=
      (V.bot_lt_mapHeight W (LinearMap.ne_zero_of_surjective hf.2)).ne'
    obtain ⟨c, hc⟩ : ∃ c : ℝ, V.mapHeight W f = (c : EReal) := by
      lift V.mapHeight W f to ℝ using ⟨ht, hb⟩ with c
      exact ⟨c, rfl⟩
    rw [hc, ← EReal.coe_mul, ← EReal.coe_add]
    exact EReal.coe_le_coe
      (V.modifiedDegree_le_of_bijective_of_mapHeight_le hS hN W f hf c hc.le)

/-- Source Proposition 4.3.55(2): an actual injection bounds the first
ordered slope with no finite-height hypothesis supplied. -/
theorem generalHNOrderedSlope_zero_le_of_injective
    (W : AdelicVectorBundle S F) (f : E →ₗ[K] F)
    (hi : Function.Injective f) (hr : 0 < Module.finrank K E) :
    (V.generalHNOrderedSlope hS hN ⟨0, hr⟩ : EReal) ≤
      (W.generalHNOrderedSlope hS hN
        ⟨0, hr.trans_le (LinearMap.finrank_le_finrank_of_injective hi)⟩ : EReal) +
      V.mapHeight W f := by
  by_cases ht : V.mapHeight W f = ⊤
  · rw [ht, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
    exact le_top
  · exact V.generalHNOrderedSlope_le_of_injective hS hN W f hi ht ⟨0, hr⟩

end

end ArakelovGeometry.AdelicVectorBundle
