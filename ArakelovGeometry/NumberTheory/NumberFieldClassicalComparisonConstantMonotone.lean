/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NumberFieldClassicalComparisonConstants
import ArakelovGeometry.NumberTheory.NumberFieldPureMinkowskiLevels
import Mathlib.Data.Nat.Choose.Multinomial

/-! # Rank monotonicity of the exact classical comparison constant -/

noncomputable section
open NumberField MeasureTheory

namespace ArakelovGeometry.NumberFieldClassicalComparisonConstantMonotone

open NumberFieldClassicalComparisonConstants WeightedEuclideanSumBall

/-- Gamma recurrence gives the actual ordinary two-dimensional volume step. -/
theorem euclideanUnitBallVolume_add_two (n : ℕ) :
    euclideanUnitBallVolume (n + 2) =
      (2 * Real.pi / ((n : ℝ) + 2)) * euclideanUnitBallVolume n := by
  rw [euclideanUnitBallVolume_eq, euclideanUnitBallVolume_eq]
  have harg : ((n + 2 : ℕ) : ℝ) / 2 + 1 = ((n : ℝ) / 2 + 1) + 1 := by
    push_cast
    ring
  rw [harg, Real.Gamma_add_one (by positivity : (n : ℝ) / 2 + 1 ≠ 0), pow_add,
    Real.sq_sqrt Real.pi_pos.le]
  field_simp [(Real.Gamma_pos_of_pos (by positivity : 0 < (n : ℝ) / 2 + 1)).ne']

/-- The actual one-dimensional ordinary unit ball has length two. -/
theorem euclideanUnitBallVolume_one : euclideanUnitBallVolume 1 = 2 := by
  rw [euclideanUnitBallVolume_eq]
  norm_num only [pow_one, Nat.cast_one]
  rw [show (3 : ℝ) / 2 = (1 / 2) + 1 by ring,
    Real.Gamma_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0), Real.Gamma_one_half_eq]
  field_simp [Real.sqrt_ne_zero'.mpr Real.pi_pos]

/-- The native ordinary ball volume grows by at most a factor two in one rank step. -/
theorem euclideanUnitBallVolume_succ_le (n : ℕ) :
    euclideanUnitBallVolume (n + 1) ≤ 2 * euclideanUnitBallVolume n := by
  induction n using Nat.twoStepInduction with
  | zero => rw [euclideanUnitBallVolume_one, euclideanUnitBallVolume_zero]; norm_num
  | one =>
    rw [show 1 + 1 = 0 + 2 by omega, euclideanUnitBallVolume_add_two,
      euclideanUnitBallVolume_zero, euclideanUnitBallVolume_one]
    nlinarith [Real.pi_lt_four]
  | more n hn _ =>
    have hv : 0 ≤ euclideanUnitBallVolume n := by
      unfold euclideanUnitBallVolume Measure.real
      positivity
    have hstep := mul_le_mul_of_nonneg_left hn
      (by positivity : 0 ≤ 2 * Real.pi / ((n : ℝ) + 3))
    rw [show n + 2 + 1 = (n + 1) + 2 by omega, euclideanUnitBallVolume_add_two,
      euclideanUnitBallVolume_add_two]
    push_cast
    rw [show (n : ℝ) + 1 + 2 = (n : ℝ) + 3 by ring]
    have hden : 2 * Real.pi / ((n : ℝ) + 3) ≤ 2 * Real.pi / ((n : ℝ) + 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hden hv]

/-- Multinomial coefficients are monotone in each literal multiplicity. -/
theorem multinomial_mono {ι : Type*} (s : Finset ι) {a b : ι → ℕ}
    (h : ∀ i ∈ s, a i ≤ b i) : Nat.multinomial s a ≤ Nat.multinomial s b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Nat.multinomial_insert hi, Nat.multinomial_insert hi]
    have hsum : ∑ j ∈ s, a j ≤ ∑ j ∈ s, b j :=
      Finset.sum_le_sum fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hc : (a i + ∑ j ∈ s, a j).choose (a i) ≤
        (b i + ∑ j ∈ s, b j).choose (b i) := by
      calc
        _ ≤ (a i + ∑ j ∈ s, b j).choose (a i) :=
          Nat.choose_le_choose _ (Nat.add_le_add_left hsum _)
        _ = (a i + ∑ j ∈ s, b j).choose (∑ j ∈ s, b j) := Nat.choose_symm_add
        _ ≤ (b i + ∑ j ∈ s, b j).choose (∑ j ∈ s, b j) :=
          Nat.choose_le_choose _ (Nat.add_le_add_right (h i (Finset.mem_insert_self _ _)) _)
        _ = _ := Nat.choose_symm_add.symm
    exact Nat.mul_le_mul hc (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

variable (K : Type*) [Field K] [NumberField K]

/-- The exact integer multinomial part of the source rank constant. -/
def rankMultinomial (n : ℕ) : ℕ :=
  Nat.multinomial Finset.univ (fun w : InfinitePlace K => w.mult * n)

theorem rankMultinomial_pos (n : ℕ) : 0 < rankMultinomial K n := Nat.multinomial_pos _ _

theorem rankMultinomial_mono : Monotone (rankMultinomial K) := by
  intro m n h
  exact multinomial_mono _ (fun w _ => Nat.mul_le_mul_left w.mult h)

/-- Its real value is the literal factorial quotient occurring in the printed constant. -/
theorem rankMultinomial_eq (n : ℕ) :
    (rankMultinomial K n : ℝ) = ((n * Module.finrank ℚ K).factorial : ℝ) /
      ((n.factorial : ℝ) ^ InfinitePlace.nrRealPlaces K *
        ((2 * n).factorial : ℝ) ^ InfinitePlace.nrComplexPlaces K) := by
  classical
  have hs : (∑ w : InfinitePlace K, w.mult * n) = n * Module.finrank ℚ K := by
    rw [← Finset.sum_mul, InfinitePlace.sum_mult_eq, Nat.mul_comm]
  have hp : (∏ w : InfinitePlace K, (w.mult * n).factorial) =
      n.factorial ^ InfinitePlace.nrRealPlaces K *
        (2 * n).factorial ^ InfinitePlace.nrComplexPlaces K := by
    rw [InfinitePlace.prod_eq_prod_mul_prod]
    simp only [fun w : {w : InfinitePlace K // w.IsReal} => w.property.mult_eq_one,
      fun w : {w : InfinitePlace K // w.IsComplex} => w.property.mult_eq_two,
      one_mul, Finset.prod_const, Finset.card_univ]
  have h := Nat.multinomial_spec Finset.univ (fun w : InfinitePlace K => w.mult * n)
  rw [hs, hp] at h
  apply (eq_div_iff (by positivity)).mpr
  have hc : ((n.factorial : ℝ) ^ InfinitePlace.nrRealPlaces K *
      ((2 * n).factorial : ℝ) ^ InfinitePlace.nrComplexPlaces K) *
      (rankMultinomial K n : ℝ) = ((n * Module.finrank ℚ K).factorial : ℝ) := by
    exact_mod_cast h
  simpa only [mul_comm] using hc

/-- Ordinary unit-ball volumes are strictly positive, including dimension zero. -/
theorem euclideanUnitBallVolume_pos (n : ℕ) : 0 < euclideanUnitBallVolume n := by
  rw [euclideanUnitBallVolume_eq]
  exact div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) _)
    (Real.Gamma_pos_of_pos (by positivity))

/-- Split the source constant into volume logarithms and its actual integer multinomial. -/
theorem comparisonConstant_eq_log_multinomial (n : ℕ) :
    comparisonConstant K n =
      (n : ℝ) * (Module.finrank ℚ K : ℝ) * Real.log 3 +
        (n : ℝ) * ((InfinitePlace.nrRealPlaces K : ℝ) +
          (InfinitePlace.nrComplexPlaces K : ℝ)) * Real.log 2 +
        (n : ℝ) / 2 * Real.log |(NumberField.discr K : ℝ)| -
        (InfinitePlace.nrRealPlaces K : ℝ) * Real.log (euclideanUnitBallVolume n) -
        (InfinitePlace.nrComplexPlaces K : ℝ) * Real.log (euclideanUnitBallVolume (2 * n)) +
        Real.log (rankMultinomial K n : ℝ) := by
  have hB := congrArg Real.log (rankMultinomial_eq K n)
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hB
  rw [comparisonConstant_eq, Real.log_mul (euclideanUnitBallVolume_pos n).ne' (by positivity),
    Real.log_mul (euclideanUnitBallVolume_pos (2 * n)).ne' (by positivity)]
  linarith

/-- One actual rank step increases the exact printed classical comparison constant. -/
theorem comparisonConstant_le_succ (n : ℕ) :
    comparisonConstant K n ≤ comparisonConstant K (n + 1) := by
  have hV : Real.log (euclideanUnitBallVolume (n + 1)) ≤
      Real.log 2 + Real.log (euclideanUnitBallVolume n) := by
    have h := Real.log_le_log (euclideanUnitBallVolume_pos (n + 1))
      (euclideanUnitBallVolume_succ_le n)
    rwa [Real.log_mul (by norm_num) (euclideanUnitBallVolume_pos n).ne'] at h
  have hV₂ : euclideanUnitBallVolume (2 * (n + 1)) ≤
      4 * euclideanUnitBallVolume (2 * n) := by
    have h := euclideanUnitBallVolume_succ_le (2 * n + 1)
    have h' := euclideanUnitBallVolume_succ_le (2 * n)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    linarith
  have hlogV₂ : Real.log (euclideanUnitBallVolume (2 * (n + 1))) ≤
      2 * Real.log 2 + Real.log (euclideanUnitBallVolume (2 * n)) := by
    have h := Real.log_le_log (euclideanUnitBallVolume_pos _) hV₂
    rw [Real.log_mul (by norm_num) (euclideanUnitBallVolume_pos (2 * n)).ne',
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
    exact h
  have hB : Real.log (rankMultinomial K n : ℝ) ≤
      Real.log (rankMultinomial K (n + 1) : ℝ) :=
    Real.log_le_log (Nat.cast_pos.mpr (rankMultinomial_pos K n))
      (Nat.cast_le.mpr (rankMultinomial_mono K (Nat.le_succ n)))
  have hD := NumberFieldPureMinkowskiLevels.log_abs_discriminant_nonneg (K := K)
  have hd : (InfinitePlace.nrRealPlaces K : ℝ) +
      2 * (InfinitePlace.nrComplexPlaces K : ℝ) = (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast InfinitePlace.card_add_two_mul_card_eq_rank K
  have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  have hpos₁ := mul_nonneg (show 0 ≤ (InfinitePlace.nrRealPlaces K : ℝ) by positivity) h3
  have hpos₂ := mul_nonneg (show 0 ≤ (InfinitePlace.nrComplexPlaces K : ℝ) by positivity)
    (show 0 ≤ 2 * Real.log 3 - Real.log 2 by linarith)
  have hV' := mul_le_mul_of_nonneg_left hV
    (show 0 ≤ (InfinitePlace.nrRealPlaces K : ℝ) by positivity)
  have hV₂' := mul_le_mul_of_nonneg_left hlogV₂
    (show 0 ≤ (InfinitePlace.nrComplexPlaces K : ℝ) by positivity)
  rw [comparisonConstant_eq_log_multinomial, comparisonConstant_eq_log_multinomial]
  push_cast
  nlinarith [congrArg (fun x : ℝ => x * Real.log 3) hd]

/-- The exact printed source constant is monotone in the original arithmetic rank. -/
theorem comparisonConstant_monotone : Monotone (comparisonConstant K) :=
  monotone_nat_of_le_succ (comparisonConstant_le_succ K)

/-- The exact source comparison constant is nonnegative in every rank. -/
theorem comparisonConstant_nonneg (n : ℕ) : 0 ≤ comparisonConstant K n := by
  simpa only [comparisonConstant_zero] using comparisonConstant_monotone K (Nat.zero_le n)

/-- The final source error term is monotone in rank, with every factorial retained. -/
theorem rank_error_monotone : Monotone (fun n : ℕ =>
    (n : ℝ) * Real.log |(NumberField.discr K : ℝ)| + comparisonConstant K n) := by
  intro m n h
  exact add_le_add (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h)
    (NumberFieldPureMinkowskiLevels.log_abs_discriminant_nonneg (K := K)))
    (comparisonConstant_monotone K h)

end ArakelovGeometry.NumberFieldClassicalComparisonConstantMonotone
