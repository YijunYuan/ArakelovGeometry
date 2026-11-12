/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Minkowski.Basic
public import ArakelovGeometry.NumberTheory.NumberField.Examples.Minkowski.Determinant

import ArakelovGeometry.NumberTheory.NumberField.Examples.Minkowski.Arithmetic
import ArakelovGeometry.NumberTheory.NumberField.Examples.Minkowski.MinimaSlopes

/-! # No unrestricted finite Minkowski level on the actual rational curve -/

@[expose] public section

open NumberField
open scoped NumberField

noncomputable section

namespace ArakelovGeometry.NonpureNumberFieldMinkowskiObstruction

open AdelicStructure AdelicVectorBundle

theorem exists_prime_gap_gt (C : ℝ) :
    ∃ (p : Nat.Primes) (a : ℤ), Odd p.val ∧ (p.val : ℤ) ∣ a ^ 2 + 1 ∧
      C * Real.log 2 < Real.log (p.val : ℝ) / 4 := by
  obtain ⟨B, hB⟩ := exists_nat_gt (max (2 : ℝ) (Real.exp (4 * C * Real.log 2)))
  have hB2 : 2 ≤ B := by
    have h := (le_max_left (2 : ℝ) _).trans_lt hB
    exact_mod_cast h.le
  obtain ⟨p, hp, ho, a, ha⟩ := exists_large_prime_minus_one_square B hB2
  have hpR : (B : ℝ) < p.val := by exact_mod_cast hp
  have hexp : Real.exp (4 * C * Real.log 2) < p.val :=
    ((le_max_right (2 : ℝ) _).trans_lt hB).trans hpR
  have hl := Real.log_lt_log (Real.exp_pos _) hexp
  rw [Real.log_exp] at hl
  exact ⟨p, a, ho, ha, by linarith⟩

theorem bundle_violates_ordinary_level (p : Nat.Primes) (a : ℤ)
    (ha : (p.val : ℤ) ∣ a ^ 2 + 1) (C : ℝ)
    (hgap : C * Real.log 2 < Real.log (p.val : ℝ) / 4) :
    ¬ (bundle p a).maximalSlope (hS := ⟨rationalCurveRegularity⟩)
      (hN := ⟨(normalizedNumberFieldArchimedeanCompletions (K := ℚ))⟩) -
      (C * Real.log (Module.finrank ℚ Plane) : ℝ) ≤
        (bundle p a).maximalLogarithmicMinimum := by
  rw [bundle_maximalSlope p a ha, bundle_maximalLogarithmicMinimum p a ha,
    finrank_plane, Nat.cast_ofNat, ← EReal.coe_sub, EReal.coe_le_coe_iff]
  linarith

theorem bundle_violates_strong_level (p : Nat.Primes) (a : ℤ)
    (ha : (p.val : ℤ) ∣ a ^ 2 + 1) (C : ℝ)
    (hgap : C * Real.log 2 < Real.log (p.val : ℝ) / 4) :
    ¬ (bundle p a).minimalSlope (hS := ⟨rationalCurveRegularity⟩)
      (hN := ⟨(normalizedNumberFieldArchimedeanCompletions (K := ℚ))⟩) -
      (C * Real.log (Module.finrank ℚ Plane) : ℝ) ≤
        (bundle p a).minimalLogarithmicMinimum := by
  rw [bundle_minimalSlope p a ha, bundle_minimalLogarithmicMinimum p a ha,
    finrank_plane, Nat.cast_ofNat, ← EReal.coe_sub, EReal.coe_le_coe_iff]
  linarith

theorem rationalCurve_not_minkowski (C : ℝ) :
    ¬ S.HasMinkowskiPropertyAtLevel.{0,0,0} C := by
  intro h
  obtain ⟨p, a, _, ha, hgap⟩ := exists_prime_gap_gt C
  exact bundle_violates_ordinary_level p a ha C hgap
    (h.2 Plane (bundle p a) (by rw [finrank_plane]; norm_num) (family_isUltrametric p a))

theorem rationalCurve_not_strongMinkowski (C : ℝ) :
    ¬ S.HasStrongMinkowskiPropertyAtLevel.{0,0,0} C := by
  intro h
  obtain ⟨p, a, _, ha, hgap⟩ := exists_prime_gap_gt C
  exact bundle_violates_strong_level p a ha C hgap
    (h.2 Plane (bundle p a) (by rw [finrank_plane]; norm_num) (family_isUltrametric p a))

def workedPrime : Nat.Primes := ⟨101, by decide⟩

theorem workedRoot : (workedPrime.val : ℤ) ∣ (10 : ℤ) ^ 2 + 1 := by
  norm_num [workedPrime]

theorem worked_gap_gt_half_log_two :
    (1 / 2 : ℝ) * Real.log 2 < Real.log (workedPrime.val : ℝ) / 4 := by
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2 ^ 2)
    (by norm_num : (2 : ℝ) ^ 2 < 101)
  rw [Real.log_pow] at h
  change (1 / 2 : ℝ) * Real.log 2 < Real.log (101 : ℝ) / 4
  norm_num at h
  linarith

theorem worked_violates_ordinary_half :
    ¬ (bundle workedPrime 10).maximalSlope (hS := ⟨rationalCurveRegularity⟩)
      (hN := ⟨(normalizedNumberFieldArchimedeanCompletions (K := ℚ))⟩) -
      ((1 / 2 : ℝ) * Real.log (Module.finrank ℚ Plane) : ℝ) ≤
        (bundle workedPrime 10).maximalLogarithmicMinimum :=
  bundle_violates_ordinary_level workedPrime 10 workedRoot (1 / 2) worked_gap_gt_half_log_two

theorem worked_violates_strong_half :
    ¬ (bundle workedPrime 10).minimalSlope (hS := ⟨rationalCurveRegularity⟩)
      (hN := ⟨(normalizedNumberFieldArchimedeanCompletions (K := ℚ))⟩) -
      ((1 / 2 : ℝ) * Real.log (Module.finrank ℚ Plane) : ℝ) ≤
        (bundle workedPrime 10).minimalLogarithmicMinimum :=
  bundle_violates_strong_level workedPrime 10 workedRoot (1 / 2) worked_gap_gt_half_log_two

end ArakelovGeometry.NonpureNumberFieldMinkowskiObstruction
