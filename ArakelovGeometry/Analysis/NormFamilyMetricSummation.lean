/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.NormFamilyMetricEnvelope
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Summable majorants for norm-family metric completeness

Nonnegative measurable majorants with summable integrals are pointwise
summable almost everywhere. Their sum and every tail are integrable, and
the integrals of the tails tend to zero.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace ArakelovGeometry

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Nonnegative measurable functions with summable integrals have an almost-everywhere
summable, integrable pointwise sum, with the expected integral. -/
theorem nonneg_summable_integral_majorants (A : ℕ → Ω → ℝ)
    (hAm : ∀ n, Measurable (A n)) (hAi : ∀ n, Integrable (A n) μ)
    (hAp : ∀ n ω, 0 ≤ A n ω) (hAs : Summable fun n ↦ ∫ ω, A n ω ∂μ) :
    (∀ᵐ ω ∂μ, Summable fun n ↦ A n ω) ∧
      Integrable (fun ω ↦ ∑' n, A n ω) μ ∧
      (∫ ω, ∑' n, A n ω ∂μ) = ∑' n, ∫ ω, A n ω ∂μ := by
  let B : Ω → ℝ≥0∞ := fun ω ↦ ∑' n, ENNReal.ofReal (A n ω)
  have hBm : Measurable B := Measurable.tsum fun n ↦ (hAm n).ennreal_ofReal
  have hBint : ∫⁻ ω, B ω ∂μ = ENNReal.ofReal (∑' n, ∫ ω, A n ω ∂μ) := by
    rw [lintegral_tsum (fun n ↦ (hAm n).ennreal_ofReal.aemeasurable)]
    simp_rw [← ofReal_integral_eq_lintegral_ofReal (hAi _)
      (Eventually.of_forall (hAp _))]
    exact (ENNReal.ofReal_tsum_of_nonneg
      (fun n ↦ integral_nonneg (hAp n)) hAs).symm
  have hBfinite : ∫⁻ ω, B ω ∂μ ≠ ⊤ := by rw [hBint]; exact ENNReal.ofReal_ne_top
  have hBae := ae_lt_top hBm hBfinite
  have heq (ω : Ω) : (B ω).toReal = ∑' n, A n ω := by
    dsimp only [B]
    rw [ENNReal.tsum_toReal_eq (fun _ ↦ ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_ofReal (hAp _ _)]
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hBae] with ω hω
    let a : ℕ → ℝ≥0 := fun n ↦ ⟨A n ω, hAp n ω⟩
    have hs : ∑' n, (a n : ℝ≥0∞) ≠ ⊤ := by
      have he : (∑' n, (a n : ℝ≥0∞)) = B ω :=
        tsum_congr fun n ↦ ENNReal.coe_nnreal_eq (a n)
      rw [he]
      exact hω.ne
    exact NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp hs)
  · simpa only [heq] using integrable_toReal_of_lintegral_ne_top hBm.aemeasurable hBfinite
  · rw [← integral_congr_ae (Eventually.of_forall heq), integral_toReal hBm.aemeasurable hBae,
      hBint, ENNReal.toReal_ofReal (tsum_nonneg fun n ↦ integral_nonneg (hAp n))]

/-- Every tail of summable nonnegative integrable majorants is integrable,
and its integral is the corresponding tail of the integrals. -/
theorem nonneg_summable_integral_majorant_tails (A : ℕ → Ω → ℝ)
    (hAm : ∀ n, Measurable (A n)) (hAi : ∀ n, Integrable (A n) μ)
    (hAp : ∀ n ω, 0 ≤ A n ω) (hAs : Summable fun n ↦ ∫ ω, A n ω ∂μ) :
    (∀ k, Integrable (fun ω ↦ ∑' n, A (n + k) ω) μ) ∧
      (∀ k, (∫ ω, ∑' n, A (n + k) ω ∂μ) = ∑' n, ∫ ω, A (n + k) ω ∂μ) ∧
      Tendsto (fun k ↦ ∫ ω, ∑' n, A (n + k) ω ∂μ) atTop (nhds 0) := by
  have htail (k : ℕ) := nonneg_summable_integral_majorants (fun n ↦ A (n + k))
    (fun n ↦ hAm (n + k)) (fun n ↦ hAi (n + k)) (fun n ↦ hAp (n + k))
    ((summable_nat_add_iff k).mpr hAs)
  refine ⟨fun k ↦ (htail k).2.1, fun k ↦ (htail k).2.2, ?_⟩
  simpa only [(htail _).2.2] using tendsto_sum_nat_add (fun n ↦ ∫ ω, A n ω ∂μ)

end ArakelovGeometry
