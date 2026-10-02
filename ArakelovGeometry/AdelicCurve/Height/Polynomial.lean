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
have affine height at most that of the polynomial.
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
