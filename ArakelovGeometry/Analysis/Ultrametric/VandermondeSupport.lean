/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.Ultrametric.Vandermonde

/-!
# The weighted Vandermonde estimate on an actual coordinate support

Support restriction identifies the first rows of the ambient Vandermonde
matrix with the checked square block. Real weights are the reciprocals of
row numbers, rather than absolute values of field scalars.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace ArakelovGeometry.VandermondeUltrametric

variable {k : Type*} [NormedField k]

/-- The ambient matrix has entry j^(i-1), in one-based coordinates. -/
def matrix (n : ℕ) : Matrix (Fin n) (Fin n) k := block id

/-- The maximum of coordinate norms divided by positive real row numbers.
The maximum of an empty vector is zero. -/
def weightedMaximum {n : ℕ} (y : Fin n → k) : ℝ :=
  ‖fun i => ‖y i‖ / (i.val + 1 : ℝ)‖

@[simp]
theorem weightedMaximum_zero (n : ℕ) : weightedMaximum (0 : Fin n → k) = 0 := by
  simp only [weightedMaximum, Pi.zero_apply, norm_zero, zero_div]
  exact norm_zero

/-- Restricting to any set containing the support preserves the coordinate maximum. -/
theorem norm_restrict_support {n t : ℕ} (s : Fin t → Fin n) (x : Fin n → k)
    (hx : ∀ j, j ∉ Set.range s → x j = 0) : ‖x ∘ s‖ = ‖x‖ := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun j => norm_le_pi_norm x (s j)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x ∘ s))).mpr
    intro j
    by_cases hj : j ∈ Set.range s
    · obtain ⟨a, rfl⟩ := hj
      exact norm_le_pi_norm (x ∘ s) a
    · rw [hx j hj, norm_zero]
      exact norm_nonneg _

/-- Each of the first t ambient rows is the square support block applied to the restriction. -/
theorem prefix_mulVec_eq {n t : ℕ} (s : Fin t ↪ Fin n) (htn : t ≤ n)
    (x : Fin n → k) (hx : ∀ j, j ∉ Set.range s → x j = 0) (i : Fin t) :
    (matrix (k := k) n).mulVec x (Fin.castLE htn i) =
      (block (k := k) s).mulVec (x ∘ s) i := by
  classical
  change (∑ j : Fin n, ((j.val + 1 : k) ^ i.val) * x j) =
    ∑ j : Fin t, (((s j).val + 1 : k) ^ i.val) * x (s j)
  calc
    _ = ∑ j ∈ Finset.univ.map s, ((j.val + 1 : k) ^ i.val) * x j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      have hjs : j ∉ Set.range s := by
        rintro ⟨a, rfl⟩
        exact hj (Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩)
      rw [hx j hjs, mul_zero]
    _ = _ := Finset.sum_map _ _ _

/-- The coordinate maximum of the actual first t output rows is the input maximum. -/
theorem norm_prefix_mulVec {p n t : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] k]
    (hnp : n < p) (s : Fin t ↪ Fin n) (htn : t ≤ n)
    (x : Fin n → k) (hx : ∀ j, j ∉ Set.range s → x j = 0) :
    ‖fun i : Fin t => (matrix (k := k) n).mulVec x (Fin.castLE htn i)‖ = ‖x‖ := by
  have he : (fun i : Fin t => (matrix (k := k) n).mulVec x (Fin.castLE htn i)) =
      (block (k := k) s).mulVec (x ∘ s) := by
    funext i
    exact prefix_mulVec_eq s htn x hx i
  rw [he, norm_block_mulVec hnp s s.injective, norm_restrict_support s x hx]

/-- A single weighted coordinate is at most the weighted maximum. -/
theorem coordinate_div_le_weightedMaximum {n : ℕ} (y : Fin n → k) (i : Fin n) :
    ‖y i‖ / (i.val + 1 : ℝ) ≤ weightedMaximum y := by
  have hnonneg : 0 ≤ ‖y i‖ / (i.val + 1 : ℝ) := div_nonneg (norm_nonneg _) (by positivity)
  simpa only [weightedMaximum, Real.norm_eq_abs, abs_of_nonneg hnonneg] using
    norm_le_pi_norm (fun j => ‖y j‖ / (j.val + 1 : ℝ)) i

/-- The literal weighted Vandermonde bound for any nonempty containing support. -/
theorem norm_div_card_le_weightedMaximum {p n t : ℕ} [Fact p.Prime]
    [NormedAlgebra ℚ_[p] k] (hnp : n < p) (ht : 0 < t) (s : Fin t ↪ Fin n)
    (x : Fin n → k) (hx : ∀ j, j ∉ Set.range s → x j = 0) :
    ‖x‖ / (t : ℝ) ≤ weightedMaximum ((matrix (k := k) n).mulVec x) := by
  have htn : t ≤ n := by simpa using Fintype.card_le_of_injective s s.injective
  let y := (matrix (k := k) n).mulVec x
  have hmax : ‖x‖ ≤ (t : ℝ) * weightedMaximum y := by
    rw [← norm_prefix_mulVec hnp s htn x hx]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (norm_nonneg _))).mpr
    intro i
    have hi : 0 < (i.val + 1 : ℝ) := by positivity
    have hit : (i.val + 1 : ℝ) ≤ t := by exact_mod_cast i.isLt
    calc
      ‖y (Fin.castLE htn i)‖ =
          (i.val + 1 : ℝ) * (‖y (Fin.castLE htn i)‖ / (i.val + 1 : ℝ)) := by
            field_simp
      _ ≤ (i.val + 1 : ℝ) * weightedMaximum y :=
        mul_le_mul_of_nonneg_left (coordinate_div_le_weightedMaximum y
          (Fin.castLE htn i)) hi.le
      _ ≤ (t : ℝ) * weightedMaximum y :=
        mul_le_mul_of_nonneg_right hit (norm_nonneg _)
  exact (div_le_iff₀ (Nat.cast_pos.mpr ht)).mpr (by simpa [mul_comm] using hmax)

/-- A set of coordinates, rather than an enumeration, suffices for the weighted bound. -/
theorem norm_div_card_le_weightedMaximum_of_support_subset {p n : ℕ} [Fact p.Prime]
    [NormedAlgebra ℚ_[p] k] (hnp : n < p) (J : Finset (Fin n)) (hJ : J.Nonempty)
    (x : Fin n → k) (hx : ∀ j, j ∉ J → x j = 0) :
    ‖x‖ / (J.card : ℝ) ≤ weightedMaximum ((matrix (k := k) n).mulVec x) := by
  let s : Fin J.card ↪ Fin n :=
    (J.equivFin.symm.toEmbedding).trans (Function.Embedding.subtype (· ∈ J))
  apply norm_div_card_le_weightedMaximum hnp (Finset.card_pos.mpr hJ) s x
  intro j hj
  apply hx j
  intro hjJ
  apply hj
  exact ⟨J.equivFin ⟨j, hjJ⟩, by simp [s]⟩

/-- The exact support cardinality gives the desired nonzero-vector bound. -/
theorem norm_div_support_card_le_weightedMaximum {p n : ℕ} [Fact p.Prime]
    [NormedAlgebra ℚ_[p] k] (hnp : n < p) (x : Fin n → k) (hx : x ≠ 0) :
    ‖x‖ / ((Function.support x).toFinite.toFinset.card : ℝ) ≤
      weightedMaximum ((matrix (k := k) n).mulVec x) := by
  classical
  let J := (Function.support x).toFinite.toFinset
  have hJ : J.Nonempty := by
    by_contra h
    apply hx
    funext j
    have hnot : j ∉ J := by rw [Finset.not_nonempty_iff_eq_empty.mp h]; simp
    change x j = 0
    simpa only [J, Set.Finite.mem_toFinset, Function.mem_support, not_not] using hnot
  apply norm_div_card_le_weightedMaximum_of_support_subset hnp J hJ x
  intro j hj
  simpa only [J, Set.Finite.mem_toFinset, Function.mem_support, not_not] using hj

/-- A zero-dimensional vector and its Vandermonde image have zero weighted maximum. -/
theorem rank_zero (x : Fin 0 → k) : x = 0 ∧
    weightedMaximum ((matrix (k := k) 0).mulVec x) = 0 := by
  have hx : x = 0 := Subsingleton.elim _ _
  refine ⟨hx, ?_⟩
  rw [hx, Matrix.mulVec_zero]
  exact weightedMaximum_zero 0

/-- The prime required by the construction exists in every rank. -/
theorem exists_prime_gt (n : ℕ) : ∃ p, p.Prime ∧ n < p := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (n + 1)
  exact ⟨p, hprime, lt_of_lt_of_le (Nat.lt_succ_self n) hp⟩

end ArakelovGeometry.VandermondeUltrametric
