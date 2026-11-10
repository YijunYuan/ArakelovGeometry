/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite-dimensional normed spaces over complete normed fields

The closedness result needed for quotient norm families includes trivially
normed fields. No ultrametric condition on the vector-space norm is imposed.
-/

namespace ArakelovGeometry

open Module

variable {L V : Type*} [NormedField L] [NormedAddCommGroup V] [NormedSpace L V]

private theorem norm_le_finrank_mul_of_mem_span [FiniteDimensional L V]
    (hL : ∀ a : L, ‖a‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε) (s : Set V)
    (hs : ∀ x ∈ s, ‖x‖ ≤ ε) {x : V} (hx : x ∈ Submodule.span L s) :
    ‖x‖ ≤ (finrank L V : ℝ) * ε := by
  classical
  let W := Submodule.span L s
  let t : Set W := Subtype.val ⁻¹' s
  have ht : (⊤ : Submodule L W) ≤ Submodule.span L t := by
    rw [show Submodule.span L t = ⊤ from Submodule.span_span_coe_preimage]
  let ι := (linearIndepOn_empty L (id : W → W)).extend (Set.empty_subset t)
  let b : Basis ι L W := Basis.ofSpan ht
  let : Finite ι := b.linearIndependent.finite
  let : Fintype ι := Fintype.ofFinite ι
  have hb (i : ι) : ‖b i‖ ≤ ε :=
    hs (b i) (Basis.ofSpan_subset ht (Set.mem_range_self i))
  calc
    ‖x‖ = ‖(⟨x, hx⟩ : W)‖ := rfl
    _ = ‖∑ i, (b.repr ⟨x, hx⟩) i • b i‖ := congrArg norm (b.sum_repr _).symm
    _ ≤ ∑ i, ‖(b.repr ⟨x, hx⟩) i • b i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ε := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_right (hL _) (norm_nonneg _)).trans (by simpa using hb i)
    _ = (finrank L W : ℝ) * ε := by simp [Module.finrank_eq_card_basis b]
    _ ≤ (finrank L V : ℝ) * ε :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr W.finrank_le) hε

/-- A finite-dimensional normed space over a trivially normed field has a
positive lower bound on the norms of all its nonzero vectors. -/
theorem exists_pos_norm_lt_imp_eq_zero [FiniteDimensional L V]
    (hL : ∀ a : L, ‖a‖ ≤ 1) :
    ∃ ε > 0, ∀ x : V, ‖x‖ < ε → x = 0 := by
  classical
  let W (ε : ℝ) := Submodule.span L {x : V | ‖x‖ < ε}
  have hex : ∃ n : ℕ, ∃ ε > 0, finrank L (W ε) = n :=
    ⟨finrank L (W 1), 1, zero_lt_one, rfl⟩
  obtain ⟨ε, hε, hmin⟩ := Nat.find_spec hex
  refine ⟨ε, hε, fun x hx ↦ ?_⟩
  by_contra hx0
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let δ := min ε (‖x‖ / ((finrank L V : ℝ) + 1))
  have hden : 0 < (finrank L V : ℝ) + 1 := by positivity
  have hδ : 0 < δ := lt_min hε (div_pos hxpos hden)
  have hle : W δ ≤ W ε := by
    apply Submodule.span_mono
    intro y hy
    exact lt_of_lt_of_le (show ‖y‖ < δ from hy) (min_le_left _ _)
  have heq : W δ = W ε := Submodule.eq_of_le_of_finrank_eq hle
    (Nat.le_antisymm (Submodule.finrank_mono hle) (by
      rw [hmin]
      exact Nat.find_min' hex ⟨δ, hδ, rfl⟩))
  have hxδ : x ∈ W δ := heq.symm ▸ Submodule.subset_span hx
  have hbound : ‖x‖ ≤ (finrank L V : ℝ) * δ :=
    norm_le_finrank_mul_of_mem_span hL hδ.le _ (fun _ hy ↦ le_of_lt hy) hxδ
  have hδle : δ ≤ ‖x‖ / ((finrank L V : ℝ) + 1) := min_le_right _ _
  have hmul := mul_le_mul_of_nonneg_left hδle (Nat.cast_nonneg (finrank L V))
  have hid : ‖x‖ / ((finrank L V : ℝ) + 1) * ((finrank L V : ℝ) + 1) = ‖x‖ :=
    div_mul_cancel₀ _ hden.ne'
  have hdiv : 0 < ‖x‖ / ((finrank L V : ℝ) + 1) := div_pos hxpos hden
  nlinarith

/-- Uniform discreteness includes non-ultrametric vector-space norms over a
trivially normed field. -/
theorem finiteDimensional_discreteUniformity [FiniteDimensional L V]
    (hL : ∀ a : L, ‖a‖ ≤ 1) : DiscreteUniformity V := by
  apply (discreteUniformity_iff_eq_bot V).mpr
  apply Metric.uniformSpace_eq_bot.mpr
  obtain ⟨ε, hε, hsmall⟩ := exists_pos_norm_lt_imp_eq_zero (V := V) hL
  refine ⟨ε, hε, fun x y hxy ↦ ?_⟩
  change ε ≤ dist x y
  rw [dist_eq_norm]
  exact le_of_not_gt fun h ↦ hxy (sub_eq_zero.mp (hsmall (x - y) h))

/-- Completeness of finite-dimensional normed spaces, also over trivially
normed complete fields. -/
theorem finiteDimensional_complete [CompleteSpace L] [FiniteDimensional L V] :
    CompleteSpace V := by
  classical
  by_cases h : ∃ a : L, a ≠ 0 ∧ ‖a‖ ≠ 1
  · let : NontriviallyNormedField L := NontriviallyNormedField.ofNormNeOne h
    exact FiniteDimensional.complete L V
  · have hL (a : L) : ‖a‖ ≤ 1 := by
      by_cases ha : a = 0
      · simp [ha]
      · exact le_of_eq (not_not.mp fun hn ↦ h ⟨a, ha, hn⟩)
    let : DiscreteUniformity V := finiteDimensional_discreteUniformity hL
    infer_instance

/-- A finite-dimensional subspace is closed over any complete normed field.
The ambient normed space need not itself be complete or finite-dimensional. -/
theorem finiteDimensional_submodule_isClosed [CompleteSpace L]
    (W : Submodule L V) [FiniteDimensional L W] : IsClosed (W : Set V) := by
  let : CompleteSpace W := finiteDimensional_complete (L := L)
  exact (completeSpace_coe_iff_isComplete.mp inferInstance).isClosed

end ArakelovGeometry
