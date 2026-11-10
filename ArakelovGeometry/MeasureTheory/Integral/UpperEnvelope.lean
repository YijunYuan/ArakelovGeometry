/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.MeasureTheory.Integral.Envelope

/-!
# Calculus of integrable-envelope integrals

The extended upper integral is the infimum of integrals of real integrable
majorants. It agrees exactly with the existing real-function envelope integral.
Translation by an integrable function is valid even at infinite values.
-/

@[expose] public section

open MeasureTheory Filter

namespace ArakelovGeometry

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The upper-envelope integral for an extended-real function. The envelopes
remain genuine real integrable functions; an empty family has infimum `⊤`. -/
noncomputable def upperERealEnvelopeIntegral (f : Ω → EReal) (μ : Measure Ω) : EReal :=
  sInf {r | ∃ A : Ω → ℝ, Integrable A μ ∧
    (∀ᵐ ω ∂μ, f ω ≤ (A ω : EReal)) ∧ r = (∫ ω, A ω ∂μ : ℝ)}

/-- On real-valued functions this is the previously defined upper integral. -/
theorem upperERealEnvelopeIntegral_coe (f : Ω → ℝ) :
    upperERealEnvelopeIntegral (fun ω ↦ (f ω : EReal)) μ = upperEnvelopeIntegral f μ := by
  simp only [upperERealEnvelopeIntegral, upperEnvelopeIntegral, EReal.coe_le_coe_iff,
    Filter.EventuallyLE]

/-- Almost-everywhere order implies order of extended upper integrals. -/
theorem upperERealEnvelopeIntegral_mono {f g : Ω → EReal} (hfg : f ≤ᵐ[μ] g) :
    upperERealEnvelopeIntegral f μ ≤ upperERealEnvelopeIntegral g μ := by
  apply sInf_le_sInf
  rintro r ⟨A, hA, hgA, hr⟩
  exact ⟨A, hA, hfg.trans hgA, hr⟩

/-- One actual integrable upper envelope excludes the value `⊤`. -/
theorem upperERealEnvelopeIntegral_lt_top {f : Ω → EReal} {A : Ω → ℝ}
    (hA : Integrable A μ) (hfA : ∀ᵐ ω ∂μ, f ω ≤ (A ω : EReal)) :
    upperERealEnvelopeIntegral f μ < ⊤ := by
  have h : upperERealEnvelopeIntegral f μ ≤ (∫ ω, A ω ∂μ : ℝ) :=
    sInf_le ⟨A, hA, hfA, rfl⟩
  exact h.trans_lt (EReal.coe_lt_top _)

/-- Adding an integrable real function translates the extended upper integral.
Both infinite values are included; no measurability of the bounded function is assumed. -/
theorem upperERealEnvelopeIntegral_add_integrable (f : Ω → EReal)
    {a : Ω → ℝ} (ha : Integrable a μ) :
    upperERealEnvelopeIntegral (fun ω ↦ f ω + (a ω : EReal)) μ =
      upperERealEnvelopeIntegral f μ + (∫ ω, a ω ∂μ : ℝ) := by
  apply le_antisymm
  · apply (EReal.sub_le_iff_le_add
      (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).mp
    apply le_sInf
    rintro r ⟨A, hA, hfA, rfl⟩
    apply (EReal.sub_le_iff_le_add
      (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).mpr
    have h : upperERealEnvelopeIntegral (fun ω ↦ f ω + (a ω : EReal)) μ ≤
        (∫ ω, (A + a) ω ∂μ : ℝ) := by
      apply sInf_le
      refine ⟨A + a, hA.add ha, ?_, rfl⟩
      filter_upwards [hfA] with ω hω
      simp only [Pi.add_apply, EReal.coe_add]
      exact add_le_add hω le_rfl
    simpa only [Pi.add_apply, integral_add hA ha, EReal.coe_add] using h
  · apply le_sInf
    rintro r ⟨B, hB, hfB, rfl⟩
    have hf : ∀ᵐ ω ∂μ, f ω ≤ ((B - a) ω : EReal) := by
      filter_upwards [hfB] with ω hω
      rw [Pi.sub_apply, EReal.coe_sub]
      exact (EReal.le_sub_iff_add_le
        (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).mpr hω
    have h : upperERealEnvelopeIntegral f μ ≤ (∫ ω, (B - a) ω ∂μ : ℝ) :=
      sInf_le ⟨B - a, hB.sub ha, hf, rfl⟩
    have h' := add_le_add h (le_refl ((∫ ω, a ω ∂μ : ℝ) : EReal))
    simpa only [Pi.sub_apply, integral_sub hB ha, EReal.coe_sub, EReal.sub_add_cancel] using h'

/-- Translation for the original real upper-envelope integral. -/
theorem upperEnvelopeIntegral_add_integrable (f : Ω → ℝ)
    {a : Ω → ℝ} (ha : Integrable a μ) :
    upperEnvelopeIntegral (f + a) μ = upperEnvelopeIntegral f μ + (∫ ω, a ω ∂μ : ℝ) := by
  simpa only [← EReal.coe_add, ← Pi.add_apply, upperERealEnvelopeIntegral_coe] using
    upperERealEnvelopeIntegral_add_integrable (fun ω ↦ (f ω : EReal)) ha

/-- Upper integrals of real functions preserve almost-everywhere order. -/
theorem upperEnvelopeIntegral_mono {f g : Ω → ℝ} (hfg : f ≤ᵐ[μ] g) :
    upperEnvelopeIntegral f μ ≤ upperEnvelopeIntegral g μ := by
  rw [← upperERealEnvelopeIntegral_coe, ← upperERealEnvelopeIntegral_coe]
  exact upperERealEnvelopeIntegral_mono (hfg.mono fun _ h ↦ EReal.coe_le_coe_iff.mpr h)

/-- Lower integrals of real functions preserve almost-everywhere order. -/
theorem lowerEnvelopeIntegral_mono {f g : Ω → ℝ} (hfg : f ≤ᵐ[μ] g) :
    lowerEnvelopeIntegral f μ ≤ lowerEnvelopeIntegral g μ := by
  apply sSup_le_sSup
  rintro r ⟨B, hB, hBf, hr⟩
  exact ⟨B, hB, hBf.trans hfg, hr⟩

/-- Negation exchanges the two envelope integrals, including infinite values. -/
theorem lowerEnvelopeIntegral_eq_neg_upper (f : Ω → ℝ) :
    lowerEnvelopeIntegral f μ = -upperEnvelopeIntegral (-f) μ := by
  apply le_antisymm
  · apply sSup_le
    rintro r ⟨B, hB, hBf, rfl⟩
    apply EReal.le_neg.mpr
    have h : upperEnvelopeIntegral (-f) μ ≤ (∫ ω, (-B) ω ∂μ : ℝ) :=
      sInf_le ⟨-B, hB.neg, hBf.mono fun _ h ↦ neg_le_neg h, rfl⟩
    simpa only [Pi.neg_apply, integral_neg, EReal.coe_neg] using h
  · apply EReal.neg_le.mpr
    apply le_sInf
    rintro r ⟨A, hA, hfA, rfl⟩
    have hf : -A ≤ᵐ[μ] f := by
      filter_upwards [hfA] with ω hω
      exact neg_le.mp hω
    have h : (∫ ω, (-A) ω ∂μ : ℝ) ≤ lowerEnvelopeIntegral f μ :=
      le_sSup ⟨-A, hA.neg, hf, rfl⟩
    apply EReal.neg_le.mpr
    simpa only [Pi.neg_apply, integral_neg, EReal.coe_neg] using h

/-- Translation for lower integrals follows from the same actual envelope bijection. -/
theorem lowerEnvelopeIntegral_add_integrable (f : Ω → ℝ)
    {a : Ω → ℝ} (ha : Integrable a μ) :
    lowerEnvelopeIntegral (f + a) μ = lowerEnvelopeIntegral f μ + (∫ ω, a ω ∂μ : ℝ) := by
  rw [lowerEnvelopeIntegral_eq_neg_upper, neg_add,
    upperEnvelopeIntegral_add_integrable _ ha.neg, lowerEnvelopeIntegral_eq_neg_upper]
  rw [EReal.neg_add (.inr (EReal.coe_ne_top _)) (.inr (EReal.coe_ne_bot _))]
  simp only [Pi.neg_apply, integral_neg, EReal.coe_neg, sub_eq_add_neg, neg_neg]

/-- A nonnegative function has nonnegative lower-envelope integral. -/
theorem lowerEnvelopeIntegral_nonneg {f : Ω → ℝ} (hf : 0 ≤ᵐ[μ] f) :
    0 ≤ lowerEnvelopeIntegral f μ := by
  have h : (∫ ω, (0 : Ω → ℝ) ω ∂μ : ℝ) ≤ lowerEnvelopeIntegral f μ :=
    le_sSup ⟨0, integrable_zero _ _ _, hf, rfl⟩
  simpa only [Pi.zero_apply, integral_zero, EReal.coe_zero] using h

/-- Lower-envelope integrals are superadditive. Empty envelope sets and infinite
suprema are handled by the extended-real order argument. -/
theorem lowerEnvelopeIntegral_add_le (f g : Ω → ℝ) :
    lowerEnvelopeIntegral f μ + lowerEnvelopeIntegral g μ ≤ lowerEnvelopeIntegral (f + g) μ := by
  apply EReal.add_le_of_forall_lt
  intro a ha b hb
  obtain ⟨ra, ⟨A, hA, hAf, rfl⟩, hra⟩ := lt_sSup_iff.mp ha
  obtain ⟨rb, ⟨B, hB, hBg, rfl⟩, hrb⟩ := lt_sSup_iff.mp hb
  have h : (∫ ω, (A + B) ω ∂μ : ℝ) ≤ lowerEnvelopeIntegral (f + g) μ := by
    apply le_sSup
    refine ⟨A + B, hA.add hB, ?_, rfl⟩
    filter_upwards [hAf, hBg] with ω ha hb
    exact add_le_add ha hb
  exact (add_le_add hra.le hrb.le).trans (by
    simpa only [Pi.add_apply, integral_add hA hB, EReal.coe_add] using h)

/-- Finite sums of lower integrals are bounded by the lower integral of the sum.
This includes the empty sum without any finite-measure assumption. -/
theorem sum_lowerEnvelopeIntegral_le {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) :
    ∑ i ∈ s, lowerEnvelopeIntegral (f i) μ ≤
      lowerEnvelopeIntegral (fun ω ↦ ∑ i ∈ s, f i ω) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact lowerEnvelopeIntegral_nonneg (Eventually.of_forall fun _ ↦ le_rfl)
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (add_le_add le_rfl ih).trans (lowerEnvelopeIntegral_add_le _ _)

private noncomputable def erealMulPosOrderIso (c : ℝ) (hc : 0 < c) : EReal ≃o EReal where
  toFun x := (c : EReal) * x
  invFun x := (c⁻¹ : ℝ) * x
  left_inv x := by
    simp only [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hc.ne', EReal.coe_one, one_mul]
  right_inv x := by
    simp only [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hc.ne', EReal.coe_one, one_mul]
  map_rel_iff' := by
    intro x y
    change (c : EReal) * x ≤ (c : EReal) * y ↔ x ≤ y
    constructor
    · intro h
      have h' := mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.mpr (inv_pos.mpr hc).le)
      simpa only [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hc.ne',
        EReal.coe_one, one_mul] using h'
    · exact fun h ↦ mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.mpr hc.le)

private theorem upperEnvelopeIntegral_const_mul_le (f : Ω → ℝ) {c : ℝ} (hc : 0 < c) :
    upperEnvelopeIntegral (fun ω ↦ c * f ω) μ ≤ (c : EReal) * upperEnvelopeIntegral f μ := by
  change upperEnvelopeIntegral _ μ ≤ erealMulPosOrderIso c hc (sInf _)
  rw [OrderIso.map_sInf]
  apply le_iInf
  intro r
  apply le_iInf
  rintro ⟨A, hA, hfA, rfl⟩
  change upperEnvelopeIntegral (fun ω ↦ c * f ω) μ ≤ (c : EReal) * (∫ ω, A ω ∂μ : ℝ)
  have h : upperEnvelopeIntegral (fun ω ↦ c * f ω) μ ≤
      (∫ ω, c * A ω ∂μ : ℝ) :=
    sInf_le ⟨fun ω ↦ c * A ω, hA.const_mul c,
      hfA.mono fun _ h ↦ mul_le_mul_of_nonneg_left h hc.le, rfl⟩
  simpa only [integral_const_mul, EReal.coe_mul] using h

/-- Positive scalar homogeneity of the upper-envelope integral, also at infinite values. -/
theorem upperEnvelopeIntegral_const_mul (f : Ω → ℝ) {c : ℝ} (hc : 0 < c) :
    upperEnvelopeIntegral (fun ω ↦ c * f ω) μ = (c : EReal) * upperEnvelopeIntegral f μ := by
  apply le_antisymm (upperEnvelopeIntegral_const_mul_le f hc)
  have h := upperEnvelopeIntegral_const_mul_le (μ := μ) (fun ω ↦ c * f ω) (inv_pos.mpr hc)
  simp only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at h
  have h' := mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.mpr hc.le)
  simpa only [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hc.ne',
    EReal.coe_one, one_mul] using h'

/-- Positive scalar homogeneity of the lower-envelope integral. -/
theorem lowerEnvelopeIntegral_const_mul (f : Ω → ℝ) {c : ℝ} (hc : 0 < c) :
    lowerEnvelopeIntegral (fun ω ↦ c * f ω) μ = (c : EReal) * lowerEnvelopeIntegral f μ := by
  rw [lowerEnvelopeIntegral_eq_neg_upper, lowerEnvelopeIntegral_eq_neg_upper]
  have he : -(fun ω ↦ c * f ω) = fun ω ↦ c * (-f) ω := by
    funext ω
    simp only [Pi.neg_apply, mul_neg]
  rw [he, upperEnvelopeIntegral_const_mul _ hc, mul_neg]

end ArakelovGeometry
