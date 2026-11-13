/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Basic
public import ArakelovGeometry.AdelicVectorBundle.Examples.Domination.Distance
public import ArakelovGeometry.AdelicVectorBundle.Examples.Minkowski.Norm

import Mathlib.CategoryTheory.Category.Init

/-!
# Actual finite cheap-place bundles on the rational counting curve

Finite-distance domination and discrete measurability produce the analytic
fields of each actual truncated bundle. The cost is arbitrary in `(0, 1]`.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.MinkowskiCounting

noncomputable section
open AdelicStructure CountingDominationCounterexample

local instance : DecidablePred (fun x : ℚ ↦ x = 0) :=
  fun _ ↦ Classical.propDecidable _

open Classical in
/-- Finite truncation of the generic cheap-line family on actual completed fibres. -/
def truncatedFamily (s : Finset ℚ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    NormFamily countingCurve Plane where
  norm a := if a ∈ s then (normFamily c hc hc1).norm a
    else CountingDistanceCounterexample.basisFamily.norm a
  norm_eq_zero_iff a z := by
    split_ifs
    · exact (normFamily c hc hc1).norm_eq_zero_iff a z
    · exact CountingDistanceCounterexample.basisFamily.norm_eq_zero_iff a z

open Classical in
/-- The completed branch formula retains every actual vector. -/
theorem truncatedFamily_norm (s : Finset ℚ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (a : countingCurve.Ω) (z : (countingCurve.ϕ a).Completion ⊗[ℚ] Plane) :
    (truncatedFamily s c hc hc1).norm a z =
      if a ∈ s then (normFamily c hc hc1).norm a z
      else CountingDistanceCounterexample.basisFamily.norm a z := by
  simp only [truncatedFamily]
  split_ifs <;> rfl

/-- The actual finite truncation is ultrametric. -/
theorem truncatedFamily_isUltrametric (s : Finset ℚ) (c : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) :
    (truncatedFamily s c hc hc1).IsUltrametric := by
  constructor
  classical
  intro a ha x y
  rw [truncatedFamily_norm s c hc hc1 a (x + y),
    truncatedFamily_norm s c hc hc1 a x, truncatedFamily_norm s c hc hc1 a y]
  by_cases hs : a ∈ s
  · simp only [ite_eq_left hs]
    exact normFamily_isUltrametric c hc hc1 a ha x y
  · simp only [ite_eq_right hs]
    by_cases hx : x = 0
    · rw [hx, zero_add]
      have hz : CountingDistanceCounterexample.basisFamily.norm a 0 = 0 :=
        (CountingDistanceCounterexample.basisFamily.norm_eq_zero_iff a 0).mpr rfl
      rw [hz]
      exact le_max_right _ _
    have hsum : CountingDistanceCounterexample.basisFamily.norm a (x + y) ≤ 1 := by
      rw [CountingDistanceCounterexample.basisFamily_norm_completed]
      split_ifs <;> norm_num
    have hn : CountingDistanceCounterexample.basisFamily.norm a x = 1 := by
      rw [CountingDistanceCounterexample.basisFamily_norm_completed, ite_eq_right hx]
    rw [hn]
    exact hsum.trans (le_max_left _ _)

/-- A genuinely finite-support nonnegative logarithmic distance envelope. -/
def distanceEnvelope (s : Finset ℚ) (c : ℝ) (a : countingCurve.Ω) : ℝ :=
  if a ∈ s then -Real.log c else 0

/-- The original infinite counting measure integrates the actual finite envelope. -/
theorem integrable_distanceEnvelope (s : Finset ℚ) (c : ℝ) :
    Integrable (distanceEnvelope s c) countingCurve.v := by
  apply integrable_count_iff.mpr
  apply summable_of_ne_finset_zero (s := s)
  intro a ha
  simp [distanceEnvelope, ha]

/-- The supremum over all completed vectors is bounded by the produced finite envelope. -/
theorem basisFamily_localDist_truncatedFamily_le (s : Finset ℚ) (c : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (a : countingCurve.Ω) :
    CountingDistanceCounterexample.basisFamily.localDist (truncatedFamily s c hc hc1) a ≤
      distanceEnvelope s c a := by
  classical
  have hlog : Real.log c ≤ 0 := Real.log_nonpos hc.le hc1
  have hd : 0 ≤ -Real.log c := neg_nonneg.mpr hlog
  apply NormFamily.localDist_le
  intro z
  rw [CountingDistanceCounterexample.basisFamily_norm_completed, truncatedFamily_norm]
  by_cases ha : a ∈ s
  · simp only [ite_eq_left ha, distanceEnvelope]
    rw [normFamily_norm c hc hc1 a z]
    have he : trivialCompletedTensorEquiv ℚ Plane z = 0 ↔ z = 0 :=
      LinearEquiv.map_eq_zero_iff _
    simp only [rawNorm, he]
    split_ifs <;>
      simp only [Real.log_zero, Real.log_one, sub_self, zero_sub, abs_zero, abs_of_nonneg hd]
    all_goals first | exact hd | exact le_rfl
  · simp only [ite_eq_right ha, distanceEnvelope]
    rw [CountingDistanceCounterexample.basisFamily_norm_completed a z]
    simp

/-- The genuine distance is attained by the actual cheap vector at selected places. -/
theorem basisFamily_localDist_truncatedFamily_eq (s : Finset ℚ) (c : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (a : countingCurve.Ω) :
    CountingDistanceCounterexample.basisFamily.localDist (truncatedFamily s c hc hc1) a =
      distanceEnvelope s c a := by
  classical
  apply le_antisymm (basisFamily_localDist_truncatedFamily_le s c hc hc1 a)
  by_cases ha : a ∈ s
  · rw [distanceEnvelope, ite_eq_left ha]
    have hz : ((1, a) : Plane) ≠ 0 := by simp
    have hb := CountingDistanceCounterexample.basisFamily.log_norm_sub_le_localDist
      (truncatedFamily s c hc hc1) a
      ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] ((1, a) : Plane))
    rw [CountingDistanceCounterexample.basisFamily_norm_rational a ((1, a) : Plane),
      ite_eq_right hz, truncatedFamily_norm s c hc hc1 a _, ite_eq_left ha,
      normFamily_norm_rational c hc hc1 a ((1, a) : Plane), rawNorm,
      ite_eq_right hz, ite_eq_left (by simp : ((1, a) : Plane).2 = a * ((1, a) : Plane).1),
      Real.log_one, zero_sub,
      abs_of_nonneg (neg_nonneg.mpr (Real.log_nonpos hc.le hc1))] at hb
    exact hb
  · rw [distanceEnvelope, ite_eq_right ha]
    exact CountingDistanceCounterexample.basisFamily.localDist_nonneg _ a

/-- Finite distance from the actual dominated flat family produces primal and dual domination. -/
theorem truncatedFamily_isDominated (s : Finset ℚ) (c : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) :
    (truncatedFamily s c hc hc1).IsDominated :=
  CountingDistanceCounterexample.basisFamily_isDominated.of_localDist
    ⟨distanceEnvelope s c, integrable_distanceEnvelope s c,
      Filter.Eventually.of_forall (basisFamily_localDist_truncatedFamily_le s c hc hc1)⟩

/-- Primal measurability is produced on the original discrete rational place space. -/
theorem truncatedFamily_isMeasurable (s : Finset ℚ) (c : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) :
    (truncatedFamily s c hc hc1).IsMeasurable := by
  constructor
  intro x
  exact measurable_of_countable _

/-- The genuine completed operator dual has measurable rational evaluations. -/
theorem truncatedFamily_dual_isMeasurable (s : Finset ℚ) (c : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) :
    (truncatedFamily s c hc hc1).dual.IsMeasurable := by
  constructor
  intro ℓ
  exact measurable_of_countable _

/-- Every finite truncation is an actual adelic bundle with all analytic fields produced. -/
abbrev bundle (s : Finset ℚ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    AdelicVectorBundle countingCurve where
  carrier := Plane
  toNormFamily := truncatedFamily s c hc hc1
  toIsAdelic := {
    isMeasurable := truncatedFamily_isMeasurable s c hc hc1
    dual_isMeasurable := truncatedFamily_dual_isMeasurable s c hc hc1
    isDominated := truncatedFamily_isDominated s c hc hc1
  }

@[simp]
theorem bundle_toNormFamily (s : Finset ℚ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    (bundle s c hc hc1).toNormFamily = truncatedFamily s c hc hc1 := rfl

open Classical in
/-- The exact rational truncation formula, including zero and all outside places. -/
theorem truncatedFamily_norm_rational (s : Finset ℚ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (a : countingCurve.Ω) (x : Plane) :
    (truncatedFamily s c hc hc1).norm a ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] x) =
      if x = 0 then 0 else if a ∈ s ∧ x.2 = a * x.1 then c else 1 := by
  rw [truncatedFamily_norm s c hc hc1 a _]
  by_cases ha : a ∈ s
  · rw [ite_eq_left ha, normFamily_norm_rational c hc hc1 a x]
    simp [rawNorm, ha]
  · rw [ite_eq_right ha, CountingDistanceCounterexample.basisFamily_norm_rational a x]
    simp [ha]

/-- Each genuine nonzero rational log profile records one possible selected cheap line. -/
theorem truncatedFamily_logNorm (s : Finset ℚ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (a : countingCurve.Ω) {x : Plane} (hx : x ≠ 0) :
    (truncatedFamily s c hc hc1).logNorm x a =
      if a ∈ s ∧ x.2 = a * x.1 then Real.log c else 0 := by
  change Real.log _ = _
  rw [truncatedFamily_norm_rational s c hc hc1 a x, ite_eq_right hx]
  split_ifs <;> simp

end
end ArakelovGeometry.MinkowskiCounting
