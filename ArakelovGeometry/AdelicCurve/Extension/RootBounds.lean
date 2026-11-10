/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Basic
public import ArakelovGeometry.ExternalResults.AbsoluteValueRootBounds

/-!
# Logarithmic root bounds over an adelic structure

The coefficient maximum and archimedean exponent give the integrable majorant
in Chen–Moriwaki, Theorem 3.3.7, formulas (3.11)–(3.12).
-/

@[expose] public section

open MeasureTheory

namespace ArakelovGeometry.AdelicStructure

variable {K : Type*} [Field K] (AS : AdelicStructure K)

/-- Maximum of the coefficient logarithms, with zero coefficients assigned logarithm zero. -/
noncomputable def coefficientLogBound (p : Polynomial K) : AS.Ω → ℝ :=
  (Finset.range (p.natDegree + 1)).sup'
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _))
    (fun i ω ↦ Real.log (AS.ϕ ω (p.coeff i)))
theorem coefficient_log_le (p : Polynomial K) {i : ℕ} (hi : i ≤ p.natDegree) (ω : AS.Ω) :
    Real.log (AS.ϕ ω (p.coeff i)) ≤ coefficientLogBound AS p ω :=
  Finset.le_sup' (fun i ω ↦ Real.log (AS.ϕ ω (p.coeff i)))
    (Finset.mem_range.mpr (by omega)) ω

/-- Every coefficient logarithm is measurable, including the zero-coefficient convention. -/
theorem measurable_coefficientLogBound (p : Polynomial K) :
    Measurable (coefficientLogBound AS p) := by
  apply Finset.measurable_sup'
  intro i _
  by_cases hi : p.coeff i = 0
  · simp [hi]
  · exact AS.measurable_log _ hi

/-- Finite maxima preserve integrability without a finiteness assumption on the measure. -/
theorem integrable_coefficientLogBound (p : Polynomial K) :
    Integrable (coefficientLogBound AS p) AS.v := by
  refine Finset.sup'_induction _ _ (p := fun f ↦ Integrable f AS.v)
    (fun a ha b hb ↦ ha.sup hb) ?_
  intro i _
  by_cases hi : p.coeff i = 0
  · simp [hi]
  · exact AS.integrable_log _ hi

/-- The logarithm of the leading coefficient of a monic polynomial is zero. -/
theorem coefficientLogBound_nonneg (p : Polynomial K) (hp : p.Monic) (ω : AS.Ω) :
    0 ≤ coefficientLogBound AS p ω := by
  simpa only [hp.coeff_natDegree, map_one, Real.log_one] using
    coefficient_log_le AS p le_rfl ω

/-- The complete logarithmic root majorant is measurable. -/
theorem measurable_logarithmicRootBound (p : Polynomial K) :
    Measurable (fun ω ↦ Real.log (p.natDegree : ℝ) * AS.κ ω + coefficientLogBound AS p ω) :=
  ((measurable_κ AS).const_mul _).add (measurable_coefficientLogBound AS p)

/-- The complete logarithmic root majorant is integrable. -/
theorem integrable_logarithmicRootBound (p : Polynomial K) :
    Integrable (fun ω ↦ Real.log (p.natDegree : ℝ) * AS.κ ω + coefficientLogBound AS p ω)
      AS.v :=
  ((integrable_κ AS).const_mul _).add (integrable_coefficientLogBound AS p)

/-- The logarithmic root envelope of a monic polynomial is nonnegative. -/
theorem logarithmicRootBound_nonneg (p : Polynomial K) (hp : p.Monic) (ω : AS.Ω) :
    0 ≤ Real.log (p.natDegree : ℝ) * AS.κ ω + AS.coefficientLogBound p ω := by
  exact add_nonneg (mul_nonneg (Real.log_natCast_nonneg _) (AS.κ_mem_Icc ω).1)
    (AS.coefficientLogBound_nonneg p hp ω)

/-- The source root estimate, including the archimedean exponent of the base place. -/
theorem log_apply_le_rootBound (p : Polynomial K) (hp : p.Monic) {L : Type*} [Field L] [Algebra K L]
    (a : L) (ha : Polynomial.aeval a p = 0) (ha0 : a ≠ 0)
    (ω : AS.Ω) (w : AbsoluteValue L ℝ) (hw : w.under K = AS.ϕ ω) :
    Real.log (w a) ≤ Real.log (p.natDegree : ℝ) * AS.κ ω + coefficientLogBound AS p ω := by
  have hm : 0 < p.natDegree := Polynomial.natDegree_pos_of_monic_of_aeval_eq_zero hp ha
  have hgnonneg : 0 ≤ coefficientLogBound AS p ω := by
    simpa only [hp.coeff_natDegree, map_one, Real.log_one] using
      coefficient_log_le AS p le_rfl ω
  let M := Real.exp (coefficientLogBound AS p ω)
  have hM : 1 ≤ M := Real.one_le_exp_iff.mpr hgnonneg
  have hcoeff (i : ℕ) (hi : i < p.natDegree) :
      w (algebraMap K L (p.coeff i)) ≤ M := by
    have heq : w (algebraMap K L (p.coeff i)) = AS.ϕ ω (p.coeff i) :=
      congrArg (fun v : AbsoluteValue K ℝ ↦ v (p.coeff i)) hw
    rw [heq]
    by_cases hc : p.coeff i = 0
    · simp only [hc, map_zero]
      exact (Real.exp_pos _).le
    · exact (Real.log_le_iff_le_exp ((AS.ϕ ω).pos hc)).mp (coefficient_log_le AS p hi.le ω)
  by_cases hna : IsNonarchimedean w
  · have hbase : ω ∈ AS.Ωfin := by
      change IsNonarchimedean (AS.ϕ ω)
      rw [← hw]
      exact (AbsoluteValue.isNonarchimedean_restriction_iff w).mpr hna
    have hκ : AS.κ ω = 0 := (AS.κ_eq_zero_iff ω).mpr hbase
    rw [hκ, mul_zero, zero_add]
    have hr := AbsoluteValue.apply_root_le_of_isNonarchimedean w hna hp ha hM hcoeff
    exact (Real.log_le_iff_le_exp (w.pos ha0)).mpr hr
  · obtain ⟨σ, s, hs, hσ⟩ :=
      AbsoluteValue.exists_complex_embedding_of_not_isNonarchimedean w hna
    have hbase : ω ∈ AS.Ωinf := by
      change ¬IsNonarchimedean (AS.ϕ ω)
      rw [← hw, AbsoluteValue.isNonarchimedean_restriction_iff w]
      exact hna
    have hk : s = AS.κ ω := by
      apply (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)).mp
      have h1 := hσ (2 : L)
      have h2 := AS.κ_def hbase 2
      have h3 := congrArg (fun v : AbsoluteValue K ℝ ↦ v 2) hw
      change w (algebraMap K L 2) = AS.ϕ ω 2 at h3
      rw [map_ofNat] at h3
      norm_num [map_ofNat, Rat.AbsoluteValue.real_eq_abs] at h1 h2 h3
      exact h1.symm.trans (h3.trans h2)
    have hr := AbsoluteValue.apply_root_le_of_complex_embedding w σ hs.1.le hσ hp ha hM hcoeff
    have hmreal : 0 < (p.natDegree : ℝ) := Nat.cast_pos.mpr hm
    have hle := Real.log_le_log (w.pos ha0) hr
    rw [Real.log_mul (Real.rpow_pos_of_pos hmreal _).ne' (Real.exp_pos _).ne',
      Real.log_rpow hmreal, Real.log_exp, hk, mul_comm (AS.κ ω)] at hle
    exact hle

end ArakelovGeometry.AdelicStructure
