/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Fintype.Order
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# Power sums and ordered absolute values

Power sums recover the largest absolute value; maximal subset products control
ordered evaluations. These are the analytic tools for Chen–Moriwaki, Lemma 3.3.5.
-/

@[expose] public section

namespace ArakelovGeometry

open MeasureTheory AbsoluteValue
open scoped ENNReal

/-- Every power of a member of a finite distinct family is a fixed linear combination
of consecutive power sums of that family. The coefficients come from the inverse Vandermonde
matrix. -/
theorem exists_pow_eq_sum_shifted_sum_pow {F : Type*} [Field F] {d : ℕ} (α : Fin d → F)
    (hα : Function.Injective α) :
    ∃ c : Matrix (Fin d) (Fin d) F, ∀ i N, α i ^ N =
      ∑ r : Fin d, c i r * ∑ j, α j ^ (N + r.val) := by
  classical
  let V := (Matrix.vandermonde α).transpose
  have hV : IsUnit V.det := by
    change IsUnit (Matrix.vandermonde α).transpose.det
    rw [Matrix.det_transpose, isUnit_iff_ne_zero, Matrix.det_vandermonde_ne_zero_iff]
    exact hα
  refine ⟨V⁻¹, fun i N ↦ ?_⟩
  have hs : (fun r : Fin d ↦ ∑ j, α j ^ (N + r.val)) =
      V.mulVec (fun j ↦ α j ^ N) := by
    ext r
    simp [V, Matrix.mulVec, dotProduct, pow_add, mul_comm]
  change α i ^ N = ((V⁻¹).mulVec (fun r : Fin d ↦ ∑ j, α j ^ (N + r.val))) i
  rw [hs, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hV, Matrix.one_mulVec]

open Filter Topology in
/-- If the power sums of a finite distinct family in a normed field tend to zero, then each
individual power sequence tends to zero. -/
theorem tendsto_pow_zero_of_tendsto_sum_pow_zero {F : Type*} [NormedField F] {d : ℕ} (α : Fin d → F)
    (hα : Function.Injective α)
    (hs : Tendsto (fun N : ℕ ↦ ∑ i, α i ^ N) atTop (𝓝 0)) (i : Fin d) :
    Tendsto (fun N : ℕ ↦ α i ^ N) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := exists_pow_eq_sum_shifted_sum_pow α hα
  have ht (r : Fin d) : Tendsto (fun N : ℕ ↦ c i r * ∑ j, α j ^ (N + r.val))
      atTop (𝓝 (c i r * 0)) :=
    tendsto_const_nhds.mul (hs.comp (tendsto_add_atTop_nat r.val))
  have h := tendsto_finsetSum Finset.univ (fun r _ ↦ ht r)
  simpa only [mul_zero, Finset.sum_const_zero, ← hc] using h

open Filter Topology in
/-- Chen--Moriwaki, Lemma 3.3.5(1), formula (3.5): for finitely many distinct elements of a
field with an absolute value, the maximum of their absolute values is recovered from power
sums: `max_j |α_j| = limsup_N |α_1^N + ⋯ + α_d^N|^{1/N}`. -/
theorem _root_.AbsoluteValue.iSup_eq_limsup_sum_pow_rpow {F : Type*} [Field F]
    (v : AbsoluteValue F ℝ) {d : ℕ} (hd : 1 ≤ d) {α : Fin d → F}
    (hα : Function.Injective α) :
    (⨆ i, v (α i)) =
      Filter.limsup (fun N : ℕ ↦ (v (∑ i, α i ^ N)) ^ ((N : ℝ)⁻¹)) Filter.atTop := by
  let := v.toNormedField
  change (⨆ i, ‖α i‖) = limsup (fun N : ℕ ↦ ‖∑ i, α i ^ N‖ ^ ((N : ℝ)⁻¹)) atTop
  classical
  let i₀ : Fin d := ⟨0, hd⟩
  let : Nonempty (Fin d) := ⟨i₀⟩
  let M := ⨆ i, ‖α i‖
  let u (N : ℕ) := ‖∑ i, α i ^ N‖ ^ ((N : ℝ)⁻¹)
  let g (N : ℕ) := (d : ℝ) ^ ((N : ℝ)⁻¹) * M
  have hM : 0 ≤ M :=
    (norm_nonneg (α i₀)).trans (le_ciSup (Finite.bddAbove_range (fun j ↦ ‖α j‖)) i₀)
  have hbound (N : ℕ) : ‖∑ i, α i ^ N‖ ≤ (d : ℝ) * M ^ N := by
    calc
      ‖∑ i, α i ^ N‖ ≤ ∑ i, ‖α i ^ N‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin d, M ^ N := Finset.sum_le_sum fun i _ ↦ by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _)
          (le_ciSup (Finite.bddAbove_range (fun j ↦ ‖α j‖)) i) N
      _ = (d : ℝ) * M ^ N := by simp
  have hug : u ≤ᶠ[atTop] g := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : N ≠ 0 := by omega
    dsimp [u, g]
    calc
      _ ≤ ((d : ℝ) * M ^ N) ^ ((N : ℝ)⁻¹) :=
        Real.rpow_le_rpow (norm_nonneg _) (hbound N) (by positivity)
      _ = (d : ℝ) ^ ((N : ℝ)⁻¹) * M := by
        rw [Real.mul_rpow (Nat.cast_nonneg _) (pow_nonneg hM _),
          Real.pow_rpow_inv_natCast hM hN0]
  have hg : Tendsto g atTop (𝓝 M) := by
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    have ht := (Real.continuous_const_rpow hd0).continuousAt.tendsto.comp
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    simpa [g] using ht.mul_const M
  have hu_bdd := hg.isBoundedUnder_le.mono_le hug
  have hu_cobdd : IsCoboundedUnder (· ≤ ·) atTop u :=
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall
      (fun N : ℕ ↦ Real.rpow_nonneg (norm_nonneg (∑ i, α i ^ N)) ((N : ℝ)⁻¹)))).isCoboundedUnder_le
  apply le_antisymm
  · apply le_limsup_of_le hu_bdd
    intro b hb
    have hb0 : 0 ≤ b := by
      obtain ⟨N, hN⟩ := hb.exists
      exact (Real.rpow_nonneg (norm_nonneg _) _).trans hN
    refine ciSup_le fun i ↦ ?_
    by_contra hi
    have hib : b < ‖α i‖ := lt_of_not_ge hi
    have hi0 : 0 < ‖α i‖ := lt_of_le_of_lt hb0 hib
    have hia : α i ≠ 0 := norm_pos_iff.mp hi0
    have hβ : Function.Injective (fun j ↦ α j / α i) :=
      fun _ _ h ↦ hα ((div_left_inj' hia).mp h)
    have hp : ∀ᶠ N : ℕ in atTop, ‖∑ j, α j ^ N‖ ≤ b ^ N := by
      filter_upwards [hb, eventually_ge_atTop 1] with N hNb hN
      have hN0 : N ≠ 0 := by omega
      have hh := pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _) hNb N
      simpa only [u, Real.rpow_inv_natCast_pow (norm_nonneg _) hN0] using hh
    have hβnorm : ∀ᶠ N : ℕ in atTop,
        ‖∑ j, (α j / α i) ^ N‖ ≤ (b / ‖α i‖) ^ N := by
      filter_upwards [hp] with N hN
      simp_rw [div_pow]
      rw [← Finset.sum_div, norm_div, norm_pow]
      exact div_le_div_of_nonneg_right hN (pow_nonneg (norm_nonneg _) _)
    have ht : Tendsto (fun N : ℕ ↦ ∑ j, (α j / α i) ^ N) atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      exact squeeze_zero' (Eventually.of_forall (fun N ↦ norm_nonneg _)) hβnorm
        (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hb0 (norm_nonneg _))
          ((div_lt_one hi0).mpr hib))
    have ht' := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp
      (tendsto_pow_zero_of_tendsto_sum_pow_zero (fun j ↦ α j / α i) hβ ht i)
    simp [div_self hia] at ht'
  · exact (limsup_le_limsup hug hu_cobdd hg.isBoundedUnder_le).trans_eq hg.limsup_eq


/-- The product over any fixed-size subset of a decreasing nonnegative tuple is bounded
by the product over its initial segment. -/
theorem prod_le_prod_initial_of_antitone {n k : ℕ} (hk : k ≤ n)
    {s : Fin n → ℝ} (hs : Antitone s) (hs0 : ∀ i, 0 ≤ s i)
    (J : Finset (Fin n)) (hJ : J.card = k) :
    (∏ j ∈ J, s j) ≤ ∏ i : Fin k, s (i.castLE hk) := by
  classical
  have hindex (i : Fin k) : i.val ≤ (J.orderEmbOfFin hJ i).val := by
    cases k with
    | zero => exact i.elim0
    | succ k =>
      induction i using Fin.induction with
      | zero => exact Nat.zero_le _
      | succ i ih =>
        exact Nat.succ_le_of_lt (lt_of_le_of_lt ih
          ((J.orderEmbOfFin hJ).strictMono (Fin.castSucc_lt_succ (i := i))))
  calc
    _ = ∏ i : Fin k, s (J.orderEmbOfFin hJ i) := by
      calc
        _ = ∏ j ∈ Finset.univ.image (J.orderEmbOfFin hJ), s j := by simp
        _ = _ := Finset.prod_image (J.orderEmbOfFin hJ).injective.injOn
    _ ≤ _ := Finset.prod_le_prod₀ (fun i _ ↦ hs0 _) (fun i _ ↦ hs (hindex i))

/-- An initial product in a decreasing nonnegative tuple is the largest subset product
of the same size. -/
theorem prod_initial_eq_iSup_prod {n k : ℕ} (hk : k ≤ n)
    {s : Fin n → ℝ} (hs : Antitone s) (hs0 : ∀ i, 0 ≤ s i) :
    (∏ i : Fin k, s (i.castLE hk)) =
      ⨆ J : {J : Finset (Fin n) // J.card = k}, ∏ j ∈ J.val, s j := by
  classical
  let J₀ : {J : Finset (Fin n) // J.card = k} :=
    ⟨Finset.univ.map (Fin.castLEEmb hk), by simp⟩
  let : Nonempty {J : Finset (Fin n) // J.card = k} := ⟨J₀⟩
  apply le_antisymm
  · apply Finite.le_ciSup_of_le J₀
    simp [J₀, Finset.prod_map]
  · apply ciSup_le
    intro J
    exact prod_le_prod_initial_of_antitone hk hs hs0 J.val J.property

/-- Sorting a tuple identifies its initial products with the largest subset products. -/
theorem prod_initial_comp_perm_eq_iSup_prod {n k : ℕ} (hk : k ≤ n)
    {s : Fin n → ℝ} (hs0 : ∀ i, 0 ≤ s i) (π : Equiv.Perm (Fin n))
    (hπ : Antitone (s ∘ π)) :
    (∏ i : Fin k, s (π (i.castLE hk))) =
      ⨆ J : {J : Finset (Fin n) // J.card = k}, ∏ j ∈ J.val, s j := by
  classical
  let e := π.finsetCongr.subtypeEquiv
    (p := fun J : Finset (Fin n) ↦ J.card = k)
    (q := fun J : Finset (Fin n) ↦ J.card = k) (by intro J; simp)
  calc
    _ = ⨆ J : {J : Finset (Fin n) // J.card = k}, ∏ j ∈ J.val, s (π j) :=
      prod_initial_eq_iSup_prod hk hπ (fun i ↦ hs0 (π i))
    _ = ⨆ J : {J : Finset (Fin n) // J.card = k}, ∏ j ∈ (e J).val, s j := by
      apply iSup_congr
      intro J
      simp [e, Equiv.subtypeEquiv, Finset.prod_map]
    _ = _ := e.iSup_comp (g := fun J ↦ ∏ j ∈ J.val, s j)

/-- A positive tuple has measurable ordered entries when its maximal subset products
are measurable, without any measurability assumption on the sorting permutations. -/
theorem measurable_perm_eval_of_measurable_iSup_prod
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (s : Ω → Fin n → ℝ) (hs : ∀ ω i, 0 < s ω i)
    (π : Ω → Equiv.Perm (Fin n)) (hπ : ∀ ω, Antitone (s ω ∘ π ω))
    (hP : ∀ k ≤ n, Measurable fun ω ↦
      ⨆ J : {J : Finset (Fin n) // J.card = k}, ∏ j ∈ J.val, s ω j)
    (i : Fin n) :
    Measurable fun ω ↦ s ω (π ω i) := by
  have hprefix (k : ℕ) (hk : k ≤ n) :
      Measurable fun ω ↦ ∏ j : Fin k, s ω (π ω (j.castLE hk)) := by
    have heq (ω : Ω) := prod_initial_comp_perm_eq_iSup_prod hk
      (fun j ↦ (hs ω j).le) (π ω) (hπ ω)
    simp_rw [heq]
    exact hP k hk
  have heq (ω : Ω) :
      s ω (π ω i) =
        (∏ j : Fin (i.val + 1), s ω (π ω (j.castLE i.isLt))) /
          ∏ j : Fin i.val, s ω (π ω (j.castLE i.isLt.le)) := by
    rw [Fin.prod_univ_castSucc]
    change s ω (π ω i) = ((∏ j : Fin i.val, s ω (π ω (j.castLE i.isLt.le))) *
      s ω (π ω i)) / _
    exact (mul_div_cancel_left₀ _ (ne_of_gt (Finset.prod_pos (fun _ _ ↦ hs ω _)))).symm
  simp_rw [heq]
  exact (hprefix (i.val + 1) i.isLt).div (hprefix i.val i.isLt.le)

end ArakelovGeometry
