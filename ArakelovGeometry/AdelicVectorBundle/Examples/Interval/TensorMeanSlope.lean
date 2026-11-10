/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Interval.TensorGlobalDegree
public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.AdelicVectorBundle.Examples.Interval.Degrees

/-!
# The rational interval tensor mean-slope counterexample

The actual interval factors have mean slope zero. Their rank-six mixed tensor
has mean slope at least `Real.log 2 / 6`, refuting the general equality printed
in Chen–Moriwaki Proposition 4.3.34 (PDF278, printed262).
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

open AdelicStructure Module

/-- The actual rational interval plane has mean slope zero. -/
theorem rationalIntervalPlaneBundle_slope_eq_zero :
    rationalIntervalPlaneBundle.slope (Or.inl inferInstance)
      rationalAdelicStructure_isRCLike = 0 := by
  simp only [AdelicVectorBundle.slope, rationalIntervalPlaneBundle_degree_eq_zero, zero_div]

/-- The actual rational interval three-space has mean slope zero. -/
theorem rationalIntervalThreeBundle_slope_eq_zero :
    rationalIntervalThreeBundle.slope (Or.inl inferInstance)
      rationalAdelicStructure_isRCLike = 0 := by
  simp only [AdelicVectorBundle.slope, rationalIntervalThreeBundle_degree_eq_zero, zero_div]

/-- The native tensor degree bound gives the concrete rank-six mean-slope bound. -/
theorem rationalIntervalTensorBundle_log_two_div_six_le_slope :
    Real.log 2 / 6 ≤ rationalIntervalTensorBundle.slope (Or.inl inferInstance)
      rationalAdelicStructure_isRCLike := by
  have hr : Module.finrank ℚ ((Fin 2 → ℚ) ⊗[ℚ] (Fin 3 → ℚ)) = 6 := by
    rw [← finrank_mul_eq_tensor]
    simp
  simp only [AdelicVectorBundle.slope, hr, Nat.cast_ofNat]
  exact div_le_div_of_nonneg_right rationalIntervalTensorBundle_log_two_le_degree
    (by norm_num)

/-- The actual mixed tensor has strictly positive mean slope. -/
theorem rationalIntervalTensorBundle_slope_pos :
    0 < rationalIntervalTensorBundle.slope (Or.inl inferInstance)
      rationalAdelicStructure_isRCLike :=
  (div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (by norm_num)).trans_le
    rationalIntervalTensorBundle_log_two_div_six_le_slope

/-- The mixed tensor mean strictly exceeds the sum of its two actual factor means. -/
theorem rationalIntervalTensorBundle_slope_strict :
    rationalIntervalPlaneBundle.slope (Or.inl inferInstance)
        rationalAdelicStructure_isRCLike +
      rationalIntervalThreeBundle.slope (Or.inl inferInstance)
        rationalAdelicStructure_isRCLike <
    rationalIntervalTensorBundle.slope (Or.inl inferInstance)
      rationalAdelicStructure_isRCLike := by
  simpa only [rationalIntervalPlaneBundle_slope_eq_zero,
    rationalIntervalThreeBundle_slope_eq_zero, zero_add] using
      rationalIntervalTensorBundle_slope_pos

/-- The unrestricted printed tensor mean-slope equality fails for these actual bundles. -/
theorem rationalIntervalTensorBundle_slope_ne_factor_sum :
    rationalIntervalTensorBundle.slope (Or.inl inferInstance)
        rationalAdelicStructure_isRCLike ≠
      rationalIntervalPlaneBundle.slope (Or.inl inferInstance)
        rationalAdelicStructure_isRCLike +
      rationalIntervalThreeBundle.slope (Or.inl inferInstance)
        rationalAdelicStructure_isRCLike :=
  ne_of_gt rationalIntervalTensorBundle_slope_strict

end ArakelovGeometry
