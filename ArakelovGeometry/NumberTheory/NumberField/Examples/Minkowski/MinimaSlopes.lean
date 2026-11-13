/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Destabilizing
public import ArakelovGeometry.AdelicVectorBundle.Minima.Basic
public import ArakelovGeometry.NumberTheory.NumberField.Examples.Minkowski.Determinant

import ArakelovGeometry.AdelicVectorBundle.Degree.LineVector
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Semistability
import ArakelovGeometry.AdelicVectorBundle.Minima.Restriction
import ArakelovGeometry.NumberTheory.NumberField.Examples.Minkowski.Degree

/-! # Exact actual minima and slopes of the nonpure rational plane -/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NonpureNumberFieldMinkowskiObstruction

open AdelicStructure AdelicVectorBundle NormFamily

theorem standardBasis_zero : standardBasis 0 = (![1, 0] : Plane) := by
  ext i
  fin_cases i <;> norm_num [standardBasis, Pi.basisFun_apply, Pi.single_apply]

theorem standardBasis_one : standardBasis 1 = (![0, 1] : Plane) := by
  ext i
  fin_cases i <;> norm_num [standardBasis, Pi.basisFun_apply, Pi.single_apply]

theorem bundle_standardBasis_vectorDegree (p : Nat.Primes) (a : ℤ)
    (ha : (p.val : ℤ) ∣ a ^ 2 + 1) (i : Fin 2) :
    (bundle p a).vectorDegree ⟨standardBasis i, standardBasis.ne_zero i⟩ =
      -Real.log (p.val : ℝ) / 2 := by
  fin_cases i
  · simpa only [Fin.zero_eta, standardBasis_zero] using bundle_axis_zero_vectorDegree p a ha
  · simpa only [Fin.mk_one, standardBasis_one] using bundle_axis_one_vectorDegree p a

theorem bundle_degreeThresholdSpan_eq_top (p : Nat.Primes) (a : ℤ)
    (ha : (p.val : ℤ) ∣ a ^ 2 + 1) (t : ℝ) (ht : t ≤ -Real.log (p.val : ℝ) / 2) :
    (bundle p a).degreeThresholdSpan t = ⊤ := by
  apply top_unique
  rw [← standardBasis.span_eq]
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  apply (bundle p a).mem_degreeThresholdSpan ⟨standardBasis i, standardBasis.ne_zero i⟩
  rw [bundle_standardBasis_vectorDegree p a ha]
  exact ht

theorem bundle_degreeThresholdSpan_eq_bot (p : Nat.Primes) (a : ℤ)
    (ha : (p.val : ℤ) ∣ a ^ 2 + 1) (t : ℝ) (ht : -Real.log (p.val : ℝ) / 2 < t) :
    (bundle p a).degreeThresholdSpan t = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro x ⟨hx, htx⟩
  exact False.elim ((not_le_of_gt ht) (htx.trans (bundle_vectorDegree_le p a ha ⟨x, hx⟩)))

theorem bundle_logarithmicMinimum (p : Nat.Primes) (a : ℤ)
    (ha : (p.val : ℤ) ∣ a ^ 2 + 1) (i : ℕ) (hi : 1 ≤ i) (hi2 : i ≤ 2) :
    (bundle p a).logarithmicMinimum i = (-Real.log (p.val : ℝ) / 2 : ℝ) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    apply EReal.coe_le_coe_iff.mpr
    by_contra! hgt
    rw [bundle_degreeThresholdSpan_eq_bot p a ha t hgt, finrank_bot] at ht
    omega
  · apply (bundle p a).coe_le_logarithmicMinimum_of_finrank_le
    rw [bundle_degreeThresholdSpan_eq_top p a ha _ le_rfl, finrank_top, finrank_plane]
    exact hi2

theorem bundle_maximalLogarithmicMinimum (p : Nat.Primes) (a : ℤ)
    (ha : (p.val : ℤ) ∣ a ^ 2 + 1) :
    (bundle p a).maximalLogarithmicMinimum = (-Real.log (p.val : ℝ) / 2 : ℝ) :=
  bundle_logarithmicMinimum p a ha 1 le_rfl (by norm_num)

theorem bundle_minimalLogarithmicMinimum (p : Nat.Primes) (a : ℤ)
    (ha : (p.val : ℤ) ∣ a ^ 2 + 1) :
    (bundle p a).minimalLogarithmicMinimum = (-Real.log (p.val : ℝ) / 2 : ℝ) := by
  rw [minimalLogarithmicMinimum, finrank_plane]
  exact bundle_logarithmicMinimum p a ha 2 (by norm_num) le_rfl

theorem bundle_slope (p : Nat.Primes) (a : ℤ) :
    (bundle p a).slope (hS := ⟨rationalCurveRegularity⟩)
      (hN := ⟨(normalizedNumberFieldArchimedeanCompletions
          (K := ℚ))⟩) = -Real.log (p.val : ℝ) / 4 := by
  rw [AdelicVectorBundle.slope, bundle_degree, finrank_plane]
  norm_num
  ring

theorem bundle_isMeanSlopeSemistable (p : Nat.Primes) (a : ℤ)
    (ha : (p.val : ℤ) ∣ a ^ 2 + 1) :
    (bundle p a).IsMeanSlopeSemistable (hS := ⟨rationalCurveRegularity⟩)
      (hN := ⟨(normalizedNumberFieldArchimedeanCompletions (K := ℚ))⟩) := by
  refine ⟨by rw [finrank_plane]; norm_num, fun F hF => ?_⟩
  by_cases he : F = ⊤
  · subst F
    rw [(bundle p a).slope_restrict_top]
  · have hle : Module.finrank ℚ F ≤ 2 := by simpa only [finrank_plane] using F.finrank_le
    have hne : Module.finrank ℚ F ≠ 2 := by
      intro h
      exact he (Submodule.eq_top_of_finrank_eq (h.trans finrank_plane.symm))
    have hF1 : Module.finrank ℚ F = 1 := by omega
    let R := (bundle p a).restrictOfNormMeasurability F (hS := ⟨rationalCurveRegularity⟩)
    let s := R.lineGenerator (hV := ⟨hF1⟩)
    have hb : R.slope (hS := ⟨rationalCurveRegularity⟩)
        (hN := ⟨(normalizedNumberFieldArchimedeanCompletions
            (K := ℚ))⟩) ≤ -Real.log (p.val : ℝ) / 2 := by
      rw [R.slope_eq_degree_of_finrank_one (hS := ⟨rationalCurveRegularity⟩)
        (hN := ⟨(normalizedNumberFieldArchimedeanCompletions (K := ℚ))⟩) hF1,
        R.degree_eq_vectorDegree_of_finrank_one (hS := ⟨rationalCurveRegularity⟩)
          (hN := ⟨(normalizedNumberFieldArchimedeanCompletions (K := ℚ))⟩) hF1 s]
      change ((bundle p a).restrictOfNormMeasurability F
          (hS := ⟨rationalCurveRegularity⟩)).vectorDegree s ≤ _
      rw [(bundle p a).vectorDegree_restrictOfNormMeasurability]
      exact bundle_vectorDegree_le p a ha _
    rw [bundle_slope]
    have hlog : 0 ≤ Real.log (p.val : ℝ) :=
      Real.log_nonneg (by exact_mod_cast p.property.one_le)
    exact hb.trans (by linarith)

theorem bundle_maximalSlope (p : Nat.Primes) (a : ℤ)
    (ha : (p.val : ℤ) ∣ a ^ 2 + 1) :
    (bundle p a).maximalSlope (hS := ⟨rationalCurveRegularity⟩)
      (hN := ⟨(normalizedNumberFieldArchimedeanCompletions (K := ℚ))⟩) =
      (-Real.log (p.val : ℝ) / 4 : ℝ) := by
  have h := ((bundle p a).isMeanSlopeSemistable_iff_maximalSlope_eq_slope
    (hS := ⟨rationalCurveRegularity⟩) (hN := ⟨(normalizedNumberFieldArchimedeanCompletions
        (K := ℚ))⟩)
    (by rw [finrank_plane]; norm_num)).mp (bundle_isMeanSlopeSemistable p a ha)
  simpa only [bundle_slope] using h

theorem bundle_minimalSlope (p : Nat.Primes) (a : ℤ)
    (ha : (p.val : ℤ) ∣ a ^ 2 + 1) :
    (bundle p a).minimalSlope (hS := ⟨rationalCurveRegularity⟩)
      (hN := ⟨(normalizedNumberFieldArchimedeanCompletions (K := ℚ))⟩) =
      (-Real.log (p.val : ℝ) / 4 : ℝ) := by
  have h := ((bundle p a).isMeanSlopeSemistable_iff_minimalSlope_eq_slope_of_isHermitian
    (hS := ⟨rationalCurveRegularity⟩) (hN := ⟨(normalizedNumberFieldArchimedeanCompletions
        (K := ℚ))⟩)
    (hV := (family_isHermitian p a)) (by rw [finrank_plane]; norm_num)).mp
      (bundle_isMeanSlopeSemistable p a ha)
  simpa only [bundle_slope] using h

theorem bundle_maximalSlope_sub_maximalLogarithmicMinimum (p : Nat.Primes) (a : ℤ)
    (ha : (p.val : ℤ) ∣ a ^ 2 + 1) :
    (bundle p a).maximalSlope (hS := ⟨rationalCurveRegularity⟩)
      (hN := ⟨(normalizedNumberFieldArchimedeanCompletions (K := ℚ))⟩) -
      (bundle p a).maximalLogarithmicMinimum = (Real.log (p.val : ℝ) / 4 : ℝ) := by
  rw [bundle_maximalSlope p a ha, bundle_maximalLogarithmicMinimum p a ha, ← EReal.coe_sub]
  congr 1
  ring

theorem bundle_minimalSlope_sub_minimalLogarithmicMinimum (p : Nat.Primes) (a : ℤ)
    (ha : (p.val : ℤ) ∣ a ^ 2 + 1) :
    (bundle p a).minimalSlope (hS := ⟨rationalCurveRegularity⟩)
      (hN := ⟨(normalizedNumberFieldArchimedeanCompletions (K := ℚ))⟩) -
      (bundle p a).minimalLogarithmicMinimum = (Real.log (p.val : ℝ) / 4 : ℝ) := by
  rw [bundle_minimalSlope p a ha, bundle_minimalLogarithmicMinimum p a ha, ← EReal.coe_sub]
  congr 1
  ring

end ArakelovGeometry.NonpureNumberFieldMinkowskiObstruction
