/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Model.Sections
public import ArakelovGeometry.NumberTheory.NumberField.Model.TraceDual.Basic
public import ArakelovGeometry.NumberTheory.NumberField.Model.TraceDual.Projective.OriginalCovolume
public import ArakelovGeometry.NumberTheory.NumberField.RiemannRoch.ComparisonConstants

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.NumberTheory.NumberField.RiemannRoch.CountComparison
import Mathlib.Topology.Sheaves.Init

/-! # The reverse arithmetic count bound on the actual second trace tensor -/

@[expose] public section

noncomputable section
open NumberField MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldClassicalDualCountComparison

open AdelicStructure NumberFieldProjectiveGeneric NumberFieldCodifferentDual
  NumberFieldProjectiveTraceDualGeneric NumberFieldProjectiveTraceDualOriginalCovolume
  NumberFieldClassicalTraceDual NumberFieldClassicalCountComparison
  NumberFieldClassicalComparisonConstants NumberFieldArithmeticPolarVolume
  NumberFieldArchimedeanCovolume
open NumberFieldInvertibleGeneric (genericImage genericImage_fullSpan)

attribute [local instance] traceTensor_finite traceTensor_projective

universe u
variable {K : Type u} [Field K] [NumberField K]
  (M : Type u) [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Apply the actual arithmetic polar inequality to the actual original trace
tensor, retaining its actual second trace-dual section count. -/
theorem traceTensor_count_inequality
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    [hη : η.IsHermitian] :
    let T := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M
    let δ := originalPrescribedTraceDualFamily M (η := η) (hη := hη)
    let hδ := originalPrescribedTraceDualFamily_isHermitian M (η := η) (hη := hη)
    originalTensorCovolume M η (hη := hη) *
        (arithmeticPolarNumerator K (Module.finrank K (K ⊗[𝓞 K] M)) /
          (Module.finrank K (K ⊗[𝓞 K] M) * Module.finrank ℚ K).factorial) *
        (Nat.card (effectiveSections T δ) : ℝ) ≤
      6 ^ (Module.finrank ℚ K * Module.finrank K (K ⊗[𝓞 K] M)) *
        (Nat.card (effectiveSections (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) T)
          (originalPrescribedTraceDualFamily T (hη := hδ))) : ℝ) := by
  let T := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M
  let δ := originalPrescribedTraceDualFamily M (η := η) (hη := hη)
  let hδ := originalPrescribedTraceDualFamily_isHermitian M (η := η) (hη := hη)
  have h := nativePolar_mul_original_count_le_traceDual_count T δ (hη := hδ)
  erw [traceTensor_generic_finrank M] at h
  exact h

/-- Reciprocal actual trace covolume and the actual second-tensor count give the
reverse logarithmic comparison before the metric bidual count is substituted. -/
theorem logTraceDual_sub_logTraceBidual_sub_logCovolume_le
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    [hη : η.IsHermitian] :
    let T := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M
    let δ := originalPrescribedTraceDualFamily M (η := η) (hη := hη)
    let hδ := originalPrescribedTraceDualFamily_isHermitian M (η := η) (hη := hη)
    logSectionCount T δ -
        logSectionCount (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) T)
          (originalPrescribedTraceDualFamily T (hη := hδ)) -
        Real.log (euclideanCovolume η (genericImage (K := K) M)) ≤
      correctedDualityConstant K (Module.finrank K (K ⊗[𝓞 K] M)) := by
  let n := Module.finrank K (K ⊗[𝓞 K] M)
  let d := Module.finrank ℚ K
  let T := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M
  let δ := originalPrescribedTraceDualFamily M (η := η) (hη := hη)
  let hδ := originalPrescribedTraceDualFamily_isHermitian M (η := η) (hη := hη)
  let TT := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) T
  let ε := originalPrescribedTraceDualFamily T (hη := hδ)
  let c := euclideanCovolume η (genericImage (K := K) M)
  let Q := arithmeticPolarNumerator K n / (n * d).factorial
  have hc : 0 < c := euclideanCovolume_pos η _ (genericImage_fg (K := K) M)
    (genericImage_fullSpan (K := K) M)
  have hQ : 0 < Q := div_pos (arithmeticPolarNumerator_pos n) (by positivity)
  have hT : 0 < (Nat.card (effectiveSections T δ) : ℝ) :=
    Nat.cast_pos.mpr (card_effectiveSections_pos T δ)
  have hcount := traceTensor_count_inequality M η
  change originalTensorCovolume M η (hη := hη) * Q * (Nat.card (effectiveSections T δ) : ℝ) ≤
    6 ^ (d * n) * (Nat.card (effectiveSections TT ε) : ℝ) at hcount
  rw [originalTensorCovolume_eq_inv M η (hη := hη)] at hcount
  change c⁻¹ * Q * (Nat.card (effectiveSections T δ) : ℝ) ≤
    6 ^ (d * n) * (Nat.card (effectiveSections TT ε) : ℝ) at hcount
  have hTT : 0 < (Nat.card (effectiveSections TT ε) : ℝ) := by
    have hp := lt_of_lt_of_le (by positivity : 0 <
      c⁻¹ * Q * (Nat.card (effectiveSections T δ) : ℝ)) hcount
    exact pos_of_mul_pos_right hp (by positivity)
  have hlog := Real.log_le_log (by positivity : 0 <
    c⁻¹ * Q * (Nat.card (effectiveSections T δ) : ℝ)) hcount
  rw [Real.log_mul (mul_pos (inv_pos.mpr hc) hQ).ne' hT.ne',
    Real.log_mul (inv_ne_zero hc.ne') hQ.ne',
    Real.log_mul (pow_pos (by norm_num : (0 : ℝ) < 6) _).ne' hTT.ne',
    Real.log_inv, Real.log_pow] at hlog
  change Real.log (Nat.card (effectiveSections T δ) : ℝ) -
      Real.log (Nat.card (effectiveSections TT ε) : ℝ) - Real.log c ≤
    (d : ℝ) * (n : ℝ) * Real.log 6 - Real.log Q
  push_cast at hlog
  linarith

end ArakelovGeometry.NumberFieldClassicalDualCountComparison
