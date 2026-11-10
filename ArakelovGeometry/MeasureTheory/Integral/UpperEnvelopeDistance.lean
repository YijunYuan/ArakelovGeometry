/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.MeasureTheory.Integral.Envelope
import ArakelovGeometry.MeasureTheory.Integral.UpperEnvelope

/-!
# Upper-integral calculus for the distance of norm families

The functions need not be measurable. These are the nonnegative upper-integral
producers used in Chen–Moriwaki, Remark 4.1.20 and Appendix A.4.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace ArakelovGeometry

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}

/-- Upper integrals are unchanged by almost-everywhere equality. -/
theorem upperEnvelopeIntegral_congr (hfg : f =ᵐ[μ] g) :
    upperEnvelopeIntegral f μ = upperEnvelopeIntegral g μ :=
  le_antisymm (upperEnvelopeIntegral_mono hfg.le)
    (upperEnvelopeIntegral_mono hfg.symm.le)

/-- A nonnegative function has nonnegative upper integral, without measurability. -/
theorem upperEnvelopeIntegral_nonneg (hf : 0 ≤ᵐ[μ] f) :
    0 ≤ upperEnvelopeIntegral f μ := by
  apply le_sInf
  rintro _ ⟨A, _, hfA, rfl⟩
  exact EReal.coe_nonneg.mpr (integral_nonneg_of_ae (hf.trans hfA))

/-- Upper integrals of nonnegative functions are subadditive, including infinite values. -/
theorem upperEnvelopeIntegral_add_le (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[μ] g) :
    upperEnvelopeIntegral (f + g) μ ≤
      upperEnvelopeIntegral f μ + upperEnvelopeIntegral g μ := by
  have hfb : upperEnvelopeIntegral f μ ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (upperEnvelopeIntegral_nonneg hf))
  have hgb : upperEnvelopeIntegral g μ ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (upperEnvelopeIntegral_nonneg hg))
  apply EReal.le_add_of_forall_gt (.inl hfb) (.inr hgb)
  intro a ha b hb
  obtain ⟨_, ⟨A, hA, hfA, rfl⟩, hAa⟩ := sInf_lt_iff.mp ha
  obtain ⟨_, ⟨B, hB, hgB, rfl⟩, hBb⟩ := sInf_lt_iff.mp hb
  have h : upperEnvelopeIntegral (f + g) μ ≤ (∫ ω, (A + B) ω ∂μ : ℝ) :=
    sInf_le ⟨A + B, hA.add hB,
      (hfA.and hgB).mono (fun _ h ↦ add_le_add h.1 h.2), rfl⟩
  simp only [Pi.add_apply, integral_add hA hB, EReal.coe_add] at h
  exact h.trans (add_le_add hAa.le hBb.le)

/-- Every strict real upper bound for the upper integral admits an actual
nonnegative measurable integrable majorant below that bound. -/
theorem exists_nonneg_measurable_upper_envelope_lt (hf : 0 ≤ᵐ[μ] f)
    {r : ℝ} (hr : upperEnvelopeIntegral f μ < r) :
    ∃ A : Ω → ℝ, Measurable A ∧ Integrable A μ ∧ (∀ ω, 0 ≤ A ω) ∧
      f ≤ᵐ[μ] A ∧ ∫ ω, A ω ∂μ < r := by
  obtain ⟨_, ⟨A, hA, hfA, rfl⟩, hAr⟩ := sInf_lt_iff.mp hr
  obtain ⟨B, hBm, hB, hfB, hBA⟩ := measurable_upper_envelope hA hfA
  have hBpos : 0 ≤ᵐ[μ] B := hf.trans hfB
  have heq : (fun ω ↦ max (B ω) 0) =ᵐ[μ] B :=
    hBpos.mono fun _ h ↦ max_eq_left h
  refine ⟨fun ω ↦ max (B ω) 0, hBm.max measurable_const,
    hB.congr heq.symm, fun _ ↦ le_max_right _ _,
    hfB.trans (Eventually.of_forall fun _ ↦ le_max_left _ _), ?_⟩
  rw [integral_congr_ae heq, hBA]
  exact EReal.coe_lt_coe_iff.mp hAr

/-- The upper integral of an arbitrary nonnegative function vanishes exactly
when that function vanishes almost everywhere. -/
theorem upperEnvelopeIntegral_eq_zero_iff (hf : 0 ≤ᵐ[μ] f) :
    upperEnvelopeIntegral f μ = 0 ↔ f =ᵐ[μ] 0 := by
  constructor
  · intro hzero
    have hex (n : ℕ) : ∃ A : Ω → ℝ, Measurable A ∧ Integrable A μ ∧
        (∀ ω, 0 ≤ A ω) ∧ f ≤ᵐ[μ] A ∧ ∫ ω, A ω ∂μ < (1 / 2 : ℝ) ^ n := by
      apply exists_nonneg_measurable_upper_envelope_lt hf
      rw [hzero]
      exact EReal.coe_pos.mpr (pow_pos (by norm_num) _)
    choose A hAm hAi hAp hfA hAlt using hex
    let B : Ω → ℝ≥0∞ := fun ω ↦ ⨅ n : ℕ, ENNReal.ofReal (A n ω)
    have hBm : Measurable B := Measurable.iInf fun n ↦ (hAm n).ennreal_ofReal
    have hBbound (n : ℕ) : ∫⁻ ω, B ω ∂μ ≤ ENNReal.ofReal (1 / 2 : ℝ) ^ n := by
      calc
        ∫⁻ ω, B ω ∂μ ≤ ∫⁻ ω, ENNReal.ofReal (A n ω) ∂μ :=
          lintegral_mono fun ω ↦ iInf_le _ n
        _ = ENNReal.ofReal (∫ ω, A n ω ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal (hAi n)
            (Eventually.of_forall (hAp n))).symm
        _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := ENNReal.ofReal_le_ofReal (hAlt n).le
        _ = _ := ENNReal.ofReal_pow (by norm_num) n
    have hBzero : ∫⁻ ω, B ω ∂μ = 0 := by
      apply le_antisymm _ zero_le
      exact ge_of_tendsto'
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)) hBbound
    have hBa := (lintegral_eq_zero_iff hBm).mp hBzero
    filter_upwards [hf, ae_all_iff.mpr hfA, hBa] with ω hω hAω hBω
    have hle : ENNReal.ofReal (f ω) ≤ B ω :=
      le_iInf fun n ↦ ENNReal.ofReal_le_ofReal (hAω n)
    rw [show B ω = 0 from hBω] at hle
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp (le_antisymm hle zero_le)) hω
  · intro heq
    rw [upperEnvelopeIntegral_congr heq,
      upperEnvelopeIntegral_eq_integral (integrable_zero Ω ℝ μ)]
    simp

end ArakelovGeometry
