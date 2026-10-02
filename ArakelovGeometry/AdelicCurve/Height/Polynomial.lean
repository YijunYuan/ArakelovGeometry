/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Height.Affine
import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.ExternalResults.AbsoluteValueRootBounds

/-!
# Heights of polynomials

The polynomial height is the height of its coefficient tuple. Monic coefficients
have affine height at most that of the polynomial. A product estimate retains the
local archimedean exponent, giving a finite integrated error term.
-/

namespace ArakelovGeometry.AdelicStructure

open MeasureTheory Polynomial

variable {K : Type*} [Field K] (AS : AdelicStructure K)

/-- The maximum of the absolute values of all coefficients of a polynomial. -/
noncomputable def polynomialLocalHeight (p : K[X]) (ω : AS.Ω) : ℝ :=
  AS.localHeight (fun i : Fin (p.natDegree + 1) ↦ p.coeff i) ω

/-- The logarithmic height of the coefficient tuple. -/
noncomputable def polynomialHeight (p : K[X]) : ℝ :=
  AS.logHeight (fun i : Fin (p.natDegree + 1) ↦ p.coeff i)

theorem polynomialLocalHeight_nonneg (p : K[X]) (ω : AS.Ω) :
    0 ≤ AS.polynomialLocalHeight p ω :=
  ((AS.ϕ ω).nonneg (p.coeff 0)).trans
    (AS.eval_le_localHeight (fun i : Fin (p.natDegree + 1) ↦ p.coeff i) ω 0)

theorem coeff_le_polynomialLocalHeight (p : K[X]) (ω : AS.Ω) (i : ℕ) :
    AS.ϕ ω (p.coeff i) ≤ AS.polynomialLocalHeight p ω := by
  by_cases hi : i ≤ p.natDegree
  · exact AS.eval_le_localHeight (fun j : Fin (p.natDegree + 1) ↦ p.coeff j)
      ω ⟨i, by omega⟩
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hi), map_zero]
    exact AS.polynomialLocalHeight_nonneg p ω

theorem polynomialLocalHeight_le {p : K[X]} {ω : AS.Ω} {M : ℝ}
    (hM : ∀ i, AS.ϕ ω (p.coeff i) ≤ M) : AS.polynomialLocalHeight p ω ≤ M := by
  unfold polynomialLocalHeight localHeight
  exact Finset.sup'_le _ _ (fun i _ ↦ hM i)

theorem polynomialLocalHeight_pos {p : K[X]} (hp : p ≠ 0) (ω : AS.Ω) :
    0 < AS.polynomialLocalHeight p ω := by
  have hlead : p.coeff p.natDegree ≠ 0 := by
    simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hp
  exact ((AS.ϕ ω).pos hlead).trans_le (AS.coeff_le_polynomialLocalHeight p ω _)

theorem polynomialHeight_eq_integral (p : K[X]) :
    AS.polynomialHeight p = ∫ ω, Real.log (AS.polynomialLocalHeight p ω) ∂AS.v := rfl

theorem integrable_log_polynomialLocalHeight (p : K[X]) :
    Integrable (fun ω ↦ Real.log (AS.polynomialLocalHeight p ω)) AS.v :=
  AS.integrable_log_localHeight _

/-- Any coefficient tuple through a degree bound gives the same local maximum. -/
theorem polynomialLocalHeight_eq_localHeight (p : K[X]) {n : ℕ}
    (hn : p.natDegree ≤ n) (ω : AS.Ω) :
    AS.polynomialLocalHeight p ω =
      AS.localHeight (fun i : Fin (n + 1) ↦ p.coeff i) ω := by
  apply le_antisymm
  · unfold polynomialLocalHeight localHeight
    apply Finset.sup'_le
    intro i _
    exact AS.eval_le_localHeight (fun j : Fin (n + 1) ↦ p.coeff j) ω ⟨i, by omega⟩
  · unfold localHeight
    apply Finset.sup'_le
    intro i _
    exact AS.coeff_le_polynomialLocalHeight p ω i

/-- Appending zero coefficients leaves the polynomial height unchanged. -/
theorem polynomialHeight_eq_logHeight (p : K[X]) {n : ℕ} (hn : p.natDegree ≤ n) :
    AS.polynomialHeight p = AS.logHeight (fun i : Fin (n + 1) ↦ p.coeff i) := by
  simp only [polynomialHeight_eq_integral, logHeight,
    AS.polynomialLocalHeight_eq_localHeight p hn]

/-- A permutation of a coefficient tuple leaves its local maximum unchanged. -/
theorem polynomialLocalHeight_eq_localHeight_reindex (p : K[X]) {n : ℕ}
    (hn : p.natDegree ≤ n) {ι : Type*} [Fintype ι] [Nonempty ι]
    (e : ι ≃ Fin (n + 1)) (ω : AS.Ω) :
    AS.polynomialLocalHeight p ω = AS.localHeight (fun i ↦ p.coeff (e i)) ω := by
  apply le_antisymm
  · unfold polynomialLocalHeight localHeight
    apply Finset.sup'_le
    intro i _
    simpa only [Equiv.apply_symm_apply, localHeight] using
      AS.eval_le_localHeight (fun j ↦ p.coeff (e j)) ω (e.symm ⟨i, by omega⟩)
  · unfold localHeight
    exact Finset.sup'_le _ _ (fun i _ ↦ AS.coeff_le_polynomialLocalHeight p ω (e i))

/-- Polynomial height is independent of the ordering of the coefficients. -/
theorem polynomialHeight_eq_logHeight_reindex (p : K[X]) {n : ℕ}
    (hn : p.natDegree ≤ n) {ι : Type*} [Fintype ι] [Nonempty ι]
    (e : ι ≃ Fin (n + 1)) :
    AS.polynomialHeight p = AS.logHeight (fun i ↦ p.coeff (e i)) := by
  simp only [polynomialHeight_eq_integral, logHeight,
    AS.polynomialLocalHeight_eq_localHeight_reindex p hn e]

theorem polynomialLocalHeight_C_mul (p : K[X]) (t : K) (ω : AS.Ω) :
    AS.polynomialLocalHeight (C t * p) ω = AS.ϕ ω t * AS.polynomialLocalHeight p ω := by
  rw [AS.polynomialLocalHeight_eq_localHeight (C t * p) (natDegree_C_mul_le t p)]
  have he : (fun i : Fin (p.natDegree + 1) ↦ (C t * p).coeff i) =
      t • (fun i : Fin (p.natDegree + 1) ↦ p.coeff i) := by
    ext i
    simp
  rw [he, AS.localHeight_smul]
  rfl

theorem polynomialLocalHeight_X_sub_C (a : K) (ω : AS.Ω) :
    AS.polynomialLocalHeight (X - C a) ω = max 1 (AS.ϕ ω a) := by
  rw [AS.polynomialLocalHeight_eq_localHeight (X - C a) (n := 1) (by simp)]
  have he : (fun i : Fin 2 ↦ (X - C a).coeff i) = ![-a, 1] := by
    ext i
    fin_cases i <;> simp
  rw [he, AS.localHeight_pair]
  simp [max_comm]

/-- A monic linear factor has the affine height of its root. -/
theorem polynomialHeight_X_sub_C (a : K) :
    AS.polynomialHeight (X - C a) = AS.affineHeight a := by
  simp only [AS.polynomialHeight_eq_integral, AS.polynomialLocalHeight_X_sub_C,
    AS.affineHeight_eq_integral]

/-- Every coefficient of a monic polynomial has affine height at most its height. -/
theorem affineHeight_coeff_le_polynomialHeight {p : K[X]} (hp : p.Monic) (i : ℕ) :
    AS.affineHeight (p.coeff i) ≤ AS.polynomialHeight p := by
  rw [AS.affineHeight_eq_integral, AS.polynomialHeight_eq_integral]
  apply integral_mono (AS.integrable_log_max_one _) (AS.integrable_log_polynomialLocalHeight p)
  intro ω
  apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  apply max_le
  · simpa only [hp.coeff_natDegree, map_one] using
      AS.coeff_le_polynomialLocalHeight p ω p.natDegree
  · exact AS.coeff_le_polynomialLocalHeight p ω i

/-- The finite integrated archimedean exponent, used in polynomial-height estimates. -/
noncomputable def heightArchimedeanConstant : ℝ := ∫ ω, AS.κ ω ∂AS.v

theorem heightArchimedeanConstant_nonneg : 0 ≤ AS.heightArchimedeanConstant :=
  integral_nonneg (fun ω ↦ (AS.κ_mem_Icc ω).1)

/-- A finite sum costs the cardinality raised to the local archimedean exponent. -/
theorem sum_le_card_rpow_mul (ω : AS.Ω) {ι : Type*} (t : Finset ι) (ht : t.Nonempty)
    (f : ι → K) {M : ℝ} (hM : ∀ i ∈ t, AS.ϕ ω (f i) ≤ M) :
    AS.ϕ ω (∑ i ∈ t, f i) ≤ (t.card : ℝ) ^ AS.κ ω * M := by
  by_cases hna : IsNonarchimedean (AS.ϕ ω)
  · have hk : AS.κ ω = 0 := (AS.κ_eq_zero_iff ω).mpr hna
    rw [hk, Real.rpow_zero, one_mul]
    exact (hna.apply_sum_le_sup ht).trans (Finset.sup'_le _ _ hM)
  · obtain ⟨σ, s, hs, hσ⟩ :=
      AbsoluteValue.exists_complex_embedding_of_not_isNonarchimedean (AS.ϕ ω) hna
    have hk : s = AS.κ ω := by
      apply (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (2 : ℝ) ≠ 1)).mp
      have h1 := hσ (2 : K)
      have h2 := AS.κ_def hna 2
      norm_num [map_ofNat, Rat.AbsoluteValue.real_eq_abs] at h1 h2
      exact h1.symm.trans h2
    simpa only [hk] using AbsoluteValue.sum_le_card_rpow_mul_of_complex_embedding
      (AS.ϕ ω) σ hs.1.le hσ t ht f hM

private theorem coeff_mul_sum_range_min (p q : K[X]) (n : ℕ) :
    (p * q).coeff n = ∑ i ∈ Finset.range (min n p.natDegree + 1),
      p.coeff i * q.coeff (n - i) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro i hi hin
  simp only [Finset.mem_range, not_lt] at hi hin
  rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

/-- The convolution has at most `p.natDegree + 1` potentially nonzero summands. -/
theorem polynomialLocalHeight_mul_le_left (p q : K[X]) (ω : AS.Ω) :
    AS.polynomialLocalHeight (p * q) ω ≤ (p.natDegree + 1 : ℕ) ^ AS.κ ω *
      AS.polynomialLocalHeight p ω * AS.polynomialLocalHeight q ω := by
  apply AS.polynomialLocalHeight_le
  intro n
  rw [coeff_mul_sum_range_min p q n]
  have hM (i : ℕ) (_ : i ∈ Finset.range (min n p.natDegree + 1)) :
      AS.ϕ ω (p.coeff i * q.coeff (n - i)) ≤
        AS.polynomialLocalHeight p ω * AS.polynomialLocalHeight q ω := by
    rw [map_mul]
    exact mul_le_mul (AS.coeff_le_polynomialLocalHeight p ω i)
      (AS.coeff_le_polynomialLocalHeight q ω (n - i)) ((AS.ϕ ω).nonneg _)
      (AS.polynomialLocalHeight_nonneg p ω)
  have h := AS.sum_le_card_rpow_mul ω (Finset.range (min n p.natDegree + 1))
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _))
    (fun i ↦ p.coeff i * q.coeff (n - i)) hM
  simp only [Finset.card_range] at h
  refine h.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (Nat.cast_nonneg _)
      (by exact_mod_cast Nat.add_le_add_right (min_le_right n p.natDegree) 1)
      (AS.κ_mem_Icc ω).1)
    (mul_nonneg (AS.polynomialLocalHeight_nonneg p ω) (AS.polynomialLocalHeight_nonneg q ω))

/-- The smaller coefficient count gives the sharp local product estimate. -/
theorem polynomialLocalHeight_mul_le (p q : K[X]) (ω : AS.Ω) :
    AS.polynomialLocalHeight (p * q) ω ≤
      (min (p.natDegree + 1) (q.natDegree + 1) : ℕ) ^ AS.κ ω *
        AS.polynomialLocalHeight p ω * AS.polynomialLocalHeight q ω := by
  rcases le_total (p.natDegree + 1) (q.natDegree + 1) with h | h
  · rw [min_eq_left h]
    exact AS.polynomialLocalHeight_mul_le_left p q ω
  · rw [min_eq_right h]
    simpa only [mul_comm p q, mul_right_comm] using AS.polynomialLocalHeight_mul_le_left q p ω

/-- Integrating the local estimate gives a finite error even when archimedean mass is infinite. -/
theorem polynomialHeight_mul_le {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    AS.polynomialHeight (p * q) ≤ AS.polynomialHeight p + AS.polynomialHeight q +
      Real.log (min (p.natDegree + 1) (q.natDegree + 1) : ℕ) *
        AS.heightArchimedeanConstant := by
  let m := min (p.natDegree + 1) (q.natDegree + 1)
  have hm : 0 < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlocal (ω : AS.Ω) : Real.log (AS.polynomialLocalHeight (p * q) ω) ≤
      Real.log (AS.polynomialLocalHeight p ω) + Real.log (AS.polynomialLocalHeight q ω) +
      Real.log m * AS.κ ω := by
    have h := Real.log_le_log (AS.polynomialLocalHeight_pos (mul_ne_zero hp hq) ω)
      (AS.polynomialLocalHeight_mul_le p q ω)
    change Real.log (AS.polynomialLocalHeight (p * q) ω) ≤
      Real.log ((m : ℝ) ^ AS.κ ω * AS.polynomialLocalHeight p ω *
        AS.polynomialLocalHeight q ω) at h
    rw [Real.log_mul (mul_ne_zero (Real.rpow_pos_of_pos hm _).ne'
      (AS.polynomialLocalHeight_pos hp ω).ne') (AS.polynomialLocalHeight_pos hq ω).ne',
      Real.log_mul (Real.rpow_pos_of_pos hm _).ne' (AS.polynomialLocalHeight_pos hp ω).ne',
      Real.log_rpow hm] at h
    convert h using 1
    ring
  have hip := AS.integrable_log_polynomialLocalHeight p
  have hiq := AS.integrable_log_polynomialLocalHeight q
  have hik := AS.integrable_κ.const_mul (Real.log m)
  have hiadd : Integrable (fun ω ↦ Real.log (AS.polynomialLocalHeight p ω) +
      Real.log (AS.polynomialLocalHeight q ω)) AS.v := hip.add hiq
  calc
    AS.polynomialHeight (p * q) ≤ ∫ ω, Real.log (AS.polynomialLocalHeight p ω) +
      Real.log (AS.polynomialLocalHeight q ω) + Real.log m * AS.κ ω ∂AS.v :=
        integral_mono (AS.integrable_log_polynomialLocalHeight (p * q))
          (hiadd.add hik) hlocal
    _ = _ := by
      rw [integral_add hiadd hik, integral_add hip hiq, integral_const_mul]
      rfl

section Proper

variable [AS.toAdelicCurve.IsProper]

theorem polynomialHeight_nonneg (p : K[X]) : 0 ≤ AS.polynomialHeight p :=
  AS.logHeight_nonneg _

/-- The product formula makes nonzero scalar multiplication preserve polynomial height. -/
theorem polynomialHeight_C_mul {p : K[X]} (hp : p ≠ 0) {t : K} (ht : t ≠ 0) :
    AS.polynomialHeight (C t * p) = AS.polynomialHeight p := by
  rw [AS.polynomialHeight_eq_logHeight (C t * p) (natDegree_C_mul_le t p)]
  have he : (fun i : Fin (p.natDegree + 1) ↦ (C t * p).coeff i) =
      t • (fun i : Fin (p.natDegree + 1) ↦ p.coeff i) := by
    ext i
    simp
  rw [he, AS.logHeight_smul_eq (t := t) ?_ ht]
  · rfl
  · intro h
    have hh := congrFun h ⟨p.natDegree, Nat.lt_succ_self _⟩
    exact (leadingCoeff_ne_zero.mpr hp) (by simpa using hh)

end Proper

end ArakelovGeometry.AdelicStructure
