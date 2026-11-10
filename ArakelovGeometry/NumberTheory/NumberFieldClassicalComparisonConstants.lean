/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NumberFieldClassicalCountComparison

/-! # The exact source constants in classical arithmetic comparison -/

noncomputable section

namespace ArakelovGeometry.NumberFieldClassicalComparisonConstants

open NumberField MeasureTheory
open NumberFieldArithmeticPolarVolume WeightedEuclideanSumBall

/-- The corrected Gillet–Soulé duality error, using the ordinary polar volume. -/
def correctedDualityConstant (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℝ :=
  (Module.finrank ℚ K : ℝ) * (n : ℝ) * Real.log 6 -
    Real.log (arithmeticPolarNumerator K n / (n * Module.finrank ℚ K).factorial)

/-- The signed covolume correction gives the exact Chen–Moriwaki comparison constant. -/
def comparisonConstant (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℝ :=
  correctedDualityConstant K n - (n : ℝ) *
    ((InfinitePlace.nrComplexPlaces K : ℝ) * Real.log 2 -
      Real.log |(NumberField.discr K : ℝ)| / 2)

variable (K : Type*) [Field K] [NumberField K]

/-- The corrected error retains the ordinary real and complex Euclidean volumes
and all factorial factors from the source. -/
theorem correctedDualityConstant_eq (n : ℕ) :
    correctedDualityConstant K n =
      (n : ℝ) * (Module.finrank ℚ K : ℝ) * Real.log 6 -
        (InfinitePlace.nrRealPlaces K : ℝ) * Real.log (euclideanUnitBallVolume n * n.factorial) -
        (InfinitePlace.nrComplexPlaces K : ℝ) *
          Real.log (euclideanUnitBallVolume (2 * n) * (2 * n).factorial) +
        Real.log ((n * Module.finrank ℚ K).factorial : ℝ) := by
  have hv (m : ℕ) : 0 < euclideanUnitBallVolume m := by
    unfold euclideanUnitBallVolume Measure.real
    exact ENNReal.toReal_pos
      (Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr zero_lt_one)).ne'
      measure_ball_lt_top.ne
  unfold correctedDualityConstant
  rw [Real.log_div (NumberFieldClassicalCountComparison.arithmeticPolarNumerator_pos n).ne'
    (by positivity)]
  unfold arithmeticPolarNumerator
  rw [Real.log_mul (pow_pos (mul_pos (hv n) (by positivity)) _).ne'
    (pow_pos (mul_pos (hv (2 * n)) (by positivity)) _).ne', Real.log_pow, Real.log_pow]
  ring

/-- Exactly the constant printed in Chen–Moriwaki Theorem 4.3.24, expressed with
the native ordinary Euclidean unit-ball volumes. -/
theorem comparisonConstant_eq (n : ℕ) :
    comparisonConstant K n =
      (n : ℝ) * (Module.finrank ℚ K : ℝ) * Real.log 3 +
        (n : ℝ) * ((InfinitePlace.nrRealPlaces K : ℝ) +
          (InfinitePlace.nrComplexPlaces K : ℝ)) * Real.log 2 +
        (n : ℝ) / 2 * Real.log |(NumberField.discr K : ℝ)| -
        (InfinitePlace.nrRealPlaces K : ℝ) * Real.log (euclideanUnitBallVolume n * n.factorial) -
        (InfinitePlace.nrComplexPlaces K : ℝ) *
          Real.log (euclideanUnitBallVolume (2 * n) * (2 * n).factorial) +
        Real.log ((n * Module.finrank ℚ K).factorial : ℝ) := by
  have hd : (InfinitePlace.nrRealPlaces K : ℝ) +
      2 * (InfinitePlace.nrComplexPlaces K : ℝ) = (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast InfinitePlace.card_add_two_mul_card_eq_rank K
  have h6 : Real.log 6 = Real.log 3 + Real.log 2 := by
    rw [show (6 : ℝ) = 3 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [comparisonConstant, correctedDualityConstant_eq, h6]
  nlinarith [congrArg (fun x : ℝ => (n : ℝ) * x * Real.log 2) hd]

/-- Rank-zero ordinary Euclidean unit-ball volume has its actual canonical value one. -/
theorem euclideanUnitBallVolume_zero : euclideanUnitBallVolume 0 = 1 := by
  simp [euclideanUnitBallVolume, Measure.real, volume_euclideanSpace_eq_dirac]

/-- The native ordinary unit-ball volume has its standard Gamma formula in all ranks. -/
theorem euclideanUnitBallVolume_eq (m : ℕ) :
    euclideanUnitBallVolume m =
      Real.sqrt Real.pi ^ m / Real.Gamma ((m : ℝ) / 2 + 1) := by
  by_cases hm : m = 0
  · subst m
    simp [euclideanUnitBallVolume_zero]
  let : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
  unfold euclideanUnitBallVolume Measure.real
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  exact ENNReal.toReal_ofReal (div_nonneg (by positivity)
    (Real.Gamma_pos_of_pos (by positivity)).le)

/-- The source duality constant is exactly zero in rank zero. -/
theorem correctedDualityConstant_zero : correctedDualityConstant K 0 = 0 := by
  simp [correctedDualityConstant, arithmeticPolarNumerator, euclideanUnitBallVolume_zero]

/-- The source classical comparison constant is exactly zero in rank zero. -/
theorem comparisonConstant_zero : comparisonConstant K 0 = 0 := by
  simp [comparisonConstant, correctedDualityConstant_zero]

end ArakelovGeometry.NumberFieldClassicalComparisonConstants
