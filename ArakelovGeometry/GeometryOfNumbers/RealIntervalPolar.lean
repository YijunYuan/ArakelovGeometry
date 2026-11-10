/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.GeometryOfNumbers.ConvexBodyPolar
public import ArakelovGeometry.GeometryOfNumbers.ConvexIntegerCount
public import ArakelovGeometry.GeometryOfNumbers.IntegralDualCovolume
public import ArakelovGeometry.GeometryOfNumbers.PrimitiveLineMeasure
public import Mathlib.Analysis.Normed.Operator.Mul

/-! # The actual continuous-dual polar of a real interval -/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.GeometryOfNumbers.RealIntervalPolar

open MeasureTheory Set PrimitiveLineMeasure

/-- The canonical scalar-to-functional coordinate pulls the actual interval polar back
to the reciprocal interval. -/
theorem preimage_polar_Icc {r : ℝ} (hr : 0 < r) :
    (ContinuousLinearMap.toSpanSingletonCLE : ℝ ≃L[ℝ] StrongDual ℝ ℝ) ⁻¹'
      StrongDual.polar ℝ (Icc (-r) r) = Icc (-r⁻¹) r⁻¹ := by
  ext t
  change (ContinuousLinearMap.toSpanSingleton ℝ t) ∈
    StrongDual.polar ℝ (Icc (-r) r) ↔ _
  rw [StrongDual.mem_polar_iff]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, Real.norm_eq_abs]
  constructor
  · intro ht
    have h := ht r ⟨by linarith, le_rfl⟩
    rw [abs_mul, abs_of_pos hr] at h
    have habs : |t| ≤ r⁻¹ := by
      rw [← one_div]
      exact (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using h)
    exact abs_le.mp habs
  · intro ht x hx
    rw [abs_mul]
    have hx' : |x| ≤ r := abs_le.mpr hx
    have ht' : |t| ≤ r⁻¹ := abs_le.mpr ht
    calc
      |x| * |t| ≤ r * r⁻¹ := mul_le_mul hx' ht' (abs_nonneg _) hr.le
      _ = 1 := mul_inv_cancel₀ hr.ne'

/-- The literal integral dual of the unit integer lattice has unit integer coordinates
under Mathlib's canonical scalar-to-functional equivalence. -/
theorem comap_integralDual_integerLattice :
    ZLattice.comap ℝ (integralDual (ℤ ∙ (1 : ℝ)))
      (ContinuousLinearMap.toSpanSingletonCLE : ℝ ≃L[ℝ] StrongDual ℝ ℝ).toLinearMap =
        ℤ ∙ (1 : ℝ) := by
  ext t
  change (∀ x ∈ (ℤ ∙ (1 : ℝ) : Submodule ℤ ℝ),
    x * t ∈ LinearMap.range (Algebra.linearMap ℤ ℝ)) ↔ t ∈ ℤ ∙ (1 : ℝ)
  constructor
  · intro ht
    obtain ⟨n, hn⟩ := ht 1 (Submodule.mem_span_singleton_self _)
    exact Submodule.mem_span_singleton.mpr ⟨n, by simpa using hn⟩
  · intro ht x hx
    obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp ht
    obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.mp hx
    refine ⟨m * n, ?_⟩
    simpa using congrArg₂ (fun a b : ℝ => a * b) hm hn

/-- A compact convex symmetric real set containing one is its own positive-radius
centered interval; the radius is produced from the actual set. -/
theorem exists_eq_centered_Icc {S : Set ℝ} (hS : IsCompact S) (hcS : Convex ℝ S)
    (hsS : ∀ x ∈ S, -x ∈ S) (h1 : (1 : ℝ) ∈ S) :
    ∃ r : ℝ, 1 ≤ r ∧ S = Icc (-r) r := by
  have hne : S.Nonempty := ⟨1, h1⟩
  have hi := ArakelovGeometry.ConvexIntegerCount.eq_Icc_sInf_sSup hS hcS hne
  have hab := csInf_le_csSup hne hS.bddBelow hS.bddAbove
  have ha : sInf S ∈ S := (Set.ext_iff.mp hi _).mpr ⟨le_rfl, hab⟩
  have hb : sSup S ∈ S := (Set.ext_iff.mp hi _).mpr ⟨hab, le_rfl⟩
  have hnegB := csInf_le hS.bddBelow (hsS _ hb)
  have hnegA := le_csSup hS.bddAbove (hsS _ ha)
  have he : sInf S = -sSup S := by linarith
  exact ⟨sSup S, le_csSup hS.bddAbove h1, by simpa only [he] using hi⟩

section Measure

variable [MeasurableSpace (StrongDual ℝ ℝ)] [BorelSpace (StrongDual ℝ ℝ)]
  (μ : Measure (StrongDual ℝ ℝ)) [μ.IsAddHaarMeasure]

/-- Ordinary real Lebesgue measure is transported to the actual integral-dual
lattice-normalized Haar measure. -/
theorem measurePreserving_scalarToDual :
    MeasurePreserving (ContinuousLinearMap.toSpanSingletonCLE : ℝ ≃L[ℝ] StrongDual ℝ ℝ)
      volume (latticeNormalizedMeasure (integralDual (ℤ ∙ (1 : ℝ))) μ) := by
  let := integerLattice_discrete
  let := integerLattice_isZLattice
  let := integralDual_discrete (ℤ ∙ (1 : ℝ))
  let := integralDual_isZLattice (ℤ ∙ (1 : ℝ))
  have h := measurePreserving_latticeNormalizedMeasure_comap
    (integralDual (ℤ ∙ (1 : ℝ)))
    (ContinuousLinearMap.toSpanSingletonCLE : ℝ ≃L[ℝ] StrongDual ℝ ℝ) μ volume
  rw [comap_integralDual_integerLattice, integerLattice_normalizedMeasure_eq_volume] at h
  exact h

/-- The actual normalized continuous-dual polar volume of `[-r,r]` is `2/r`. -/
theorem normalizedMeasure_polar_Icc {r : ℝ} (hr : 0 < r) :
    latticeNormalizedMeasure (integralDual (ℤ ∙ (1 : ℝ))) μ
      (StrongDual.polar ℝ (Icc (-r) r)) = ENNReal.ofReal (2 / r) := by
  have h := (measurePreserving_scalarToDual μ).measure_preimage
    (NormedSpace.isClosed_polar ℝ (Icc (-r) r)).measurableSet.nullMeasurableSet
  rw [preimage_polar_Icc hr, Real.volume_Icc] at h
  convert h.symm using 1
  congr 1
  ring

/-- The primal length and actual integral-dual polar length multiply to four. -/
theorem volume_mul_normalizedMeasure_polar_Icc {r : ℝ} (hr : 0 < r) :
    volume (Icc (-r) r) *
      latticeNormalizedMeasure (integralDual (ℤ ∙ (1 : ℝ))) μ
        (StrongDual.polar ℝ (Icc (-r) r)) = 4 := by
  rw [normalizedMeasure_polar_Icc μ hr, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by linarith : 0 ≤ r - -r)]
  have h : (r - -r) * (2 / r) = 4 := by field_simp; ring
  rw [h]
  norm_num

/-- The actual compact symmetric convex set and its actual normalized dual polar
have product four, with the interval representation derived rather than assumed. -/
theorem volume_mul_normalizedMeasure_polar {S : Set ℝ} (hS : IsCompact S)
    (hcS : Convex ℝ S) (hsS : ∀ x ∈ S, -x ∈ S) (h1 : (1 : ℝ) ∈ S) :
    volume S * latticeNormalizedMeasure (integralDual (ℤ ∙ (1 : ℝ))) μ
      (StrongDual.polar ℝ S) = 4 := by
  obtain ⟨r, hr, rfl⟩ := exists_eq_centered_Icc hS hcS hsS h1
  exact volume_mul_normalizedMeasure_polar_Icc μ (by linarith)

/-- The exact real factor needed by primitive-line polar induction. -/
theorem normalizedMeasure_polar_toReal_eq_four_div {S : Set ℝ} (hS : IsCompact S)
    (hcS : Convex ℝ S) (hsS : ∀ x ∈ S, -x ∈ S) (h1 : (1 : ℝ) ∈ S) :
    (latticeNormalizedMeasure (integralDual (ℤ ∙ (1 : ℝ))) μ
      (StrongDual.polar ℝ S)).toReal = 4 / (volume S).toReal := by
  obtain ⟨r, hr, rfl⟩ := exists_eq_centered_Icc hS hcS hsS h1
  have hr0 : 0 < r := by linarith
  rw [normalizedMeasure_polar_Icc μ hr0, Real.volume_Icc,
    ENNReal.toReal_ofReal (div_nonneg (by norm_num) hr0.le),
    ENNReal.toReal_ofReal (by linarith : 0 ≤ r - -r)]
  field_simp
  ring

end Measure

end ArakelovGeometry.GeometryOfNumbers.RealIntervalPolar
