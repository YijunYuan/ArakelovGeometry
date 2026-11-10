/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! # Actual volumes of finite weighted sums of Euclidean norms -/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.WeightedEuclideanSumBall

open MeasureTheory MeasureTheory.Measure Module
open scoped ENNReal

/-- The actual radial exponential integral, in every finite real dimension. -/
theorem integral_exp_neg_norm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [IsAddHaarMeasure μ] :
    (∫ x : F, Real.exp (-‖x‖) ∂μ) =
      μ.real (Metric.ball 0 1) * (finrank ℝ F).factorial := by
  have h := measure_unitBall_eq_integral_div_gamma (E := F) μ (p := 1) zero_lt_one
  simp only [Real.rpow_one, div_one, Real.Gamma_nat_eq_factorial] at h
  have hi : 0 ≤ ∫ x : F, Real.exp (-‖x‖) ∂μ :=
    integral_nonneg (fun x => (Real.exp_pos _).le)
  have ht := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal (div_nonneg hi (Nat.cast_nonneg _))] at ht
  exact ((eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))).mp ht).symm

/-- Positive dilation of the actual exponential integral, including dimension zero. -/
theorem integral_exp_neg_mul_norm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [IsAddHaarMeasure μ] {w : ℝ} (hw : 0 < w) :
    (∫ x : F, Real.exp (-(w * ‖x‖)) ∂μ) =
      μ.real (Metric.ball 0 1) * (finrank ℝ F).factorial / w ^ finrank ℝ F := by
  have h := μ.integral_comp_smul_of_nonneg (fun x : F => Real.exp (-‖x‖)) w (hR := hw.le)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hw, smul_eq_mul,
    integral_exp_neg_norm, div_eq_mul_inv, mul_comm] using h

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ j, NormedAddCommGroup (E j)]

/-- The weighted sum of the original component norms on the original product. -/
def weightedNorm (w : ι → ℝ) (x : ∀ j, E j) : ℝ := ∑ j, w j * ‖x j‖

/-- The original weighted product body, without replacing its product measure. -/
def weightedBall (w : ι → ℝ) : Set (∀ j, E j) := {x | weightedNorm w x ≤ 1}

variable [∀ j, NormedSpace ℝ (E j)] [∀ j, FiniteDimensional ℝ (E j)]
  [∀ j, MeasureSpace (E j)] [∀ j, BorelSpace (E j)]
  [∀ j, IsAddHaarMeasure (volume : Measure (E j))]

/-- Actual finite-product Fubini and actual radial integrals produce the numerator. -/
theorem integral_exp_neg_weightedNorm {w : ι → ℝ} (hw : ∀ j, 0 < w j) :
    (∫ x : ∀ j, E j, Real.exp (-weightedNorm w x)) =
      ∏ j, volume.real (Metric.ball (0 : E j) 1) *
        (finrank ℝ (E j)).factorial / w j ^ finrank ℝ (E j) := by
  simp_rw [weightedNorm, ← Finset.sum_neg_distrib, Real.exp_sum]
  rw [integral_fintype_prod_volume_eq_prod
    (fun j (x : E j) => Real.exp (-(w j * ‖x‖)))]
  exact Finset.prod_congr rfl fun j _ => integral_exp_neg_mul_norm volume (hw j)

/-- The actual product Haar volume, in all block dimensions, including empty products. -/
theorem volume_weightedBall {w : ι → ℝ} (hw : ∀ j, 0 < w j) :
    volume (weightedBall (E := E) w) = ENNReal.ofReal
      ((∏ j, volume.real (Metric.ball (0 : E j) 1) *
        (finrank ℝ (E j)).factorial / w j ^ finrank ℝ (E j)) /
          (∑ j, finrank ℝ (E j)).factorial) := by
  classical
  have hzero : weightedNorm w (0 : ∀ j, E j) = 0 := by simp [weightedNorm]
  have hneg : ∀ x : ∀ j, E j, weightedNorm w (-x) = weightedNorm w x := by
    intro x
    simp [weightedNorm]
  have hadd : ∀ x y : ∀ j, E j,
      weightedNorm w (x + y) ≤ weightedNorm w x + weightedNorm w y := by
    intro x y
    simp only [weightedNorm, Pi.add_apply, ← Finset.sum_add_distrib, ← mul_add]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (norm_add_le _ _) (hw j).le
  have hdef : ∀ {x : ∀ j, E j}, weightedNorm w x = 0 → x = 0 := by
    intro x hx
    ext j
    have hj : w j * ‖x j‖ ≤ 0 := by
      apply (Finset.single_le_sum
        (fun k _ => mul_nonneg (hw k).le (norm_nonneg (x k))) (Finset.mem_univ j)).trans_eq
      exact hx
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (x j), hw j])
  have hsmul : ∀ (r : ℝ) (x : ∀ j, E j),
      weightedNorm w (r • x) ≤ |r| * weightedNorm w x := by
    intro r x
    simp only [weightedNorm, Pi.smul_apply, norm_smul, Real.norm_eq_abs, Finset.mul_sum]
    exact le_of_eq (Finset.sum_congr rfl fun j _ => by ring)
  have hopen : volume (weightedBall (E := E) w) =
      volume {x : ∀ j, E j | weightedNorm w x < 1} := by
    obtain hs | hn := subsingleton_or_nontrivial (∀ j, E j)
    · congr 1
      ext x
      rw [Subsingleton.elim x 0]
      simp [weightedBall, hzero]
    · exact measure_le_eq_lt volume hzero hneg hadd hdef hsmul 1
  rw [hopen, measure_lt_one_eq_integral_div_gamma volume hzero hneg hadd hdef hsmul zero_lt_one]
  simp only [Real.rpow_one, div_one, Module.finrank_pi_fintype, Real.Gamma_nat_eq_factorial]
  rw [integral_exp_neg_weightedNorm hw]

/-- Ordinary Euclidean volume of the actual unit ball, with the native canonical volume. -/
def euclideanUnitBallVolume (m : ℕ) : ℝ :=
  volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1)

/-- The source factorial formula on the original product of ordinary Euclidean blocks. -/
theorem euclidean_volume_weightedBall (m : ι → ℕ) {w : ι → ℝ} (hw : ∀ j, 0 < w j) :
    volume (weightedBall (E := fun j => EuclideanSpace ℝ (Fin (m j))) w) =
      ENNReal.ofReal ((∏ j, euclideanUnitBallVolume (m j) * (m j).factorial / w j ^ m j) /
        (∑ j, m j).factorial) := by
  simpa [euclideanUnitBallVolume] using
    volume_weightedBall (E := fun j => EuclideanSpace ℝ (Fin (m j))) hw

end ArakelovGeometry.WeightedEuclideanSumBall
