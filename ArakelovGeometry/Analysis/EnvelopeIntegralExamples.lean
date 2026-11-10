/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.EnvelopeIntegral

/-!
# Envelope integrals on an infinite atom

The source integral is an infimum over real integrable majorants. On a
singleton of infinite mass, the only such functions vanish, so its value on
the real constant `-1`, or on the extended constant `⊥`, is zero. This records
why no identification with ordinary extended integration is asserted.
-/

@[expose] public section

open MeasureTheory Filter

namespace ArakelovGeometry

/-- The only integrable real function on an infinite-mass singleton is zero. -/
theorem integrable_infiniteAtom_eq_zero (f : Unit → ℝ)
    (hf : Integrable f ((⊤ : ENNReal) • Measure.dirac ())) : f = 0 := by
  have he : f = fun _ ↦ f () := by
    funext x
    cases x
    rfl
  rw [he] at hf
  rcases integrable_const_iff.mp hf with hz | hfin
  · funext x
    cases x
    exact hz
  · let := hfin
    have h := measure_lt_top ((⊤ : ENNReal) • Measure.dirac ()) Set.univ
    simp at h

/-- The source's real upper integral is zero on the constant `-1` over an infinite atom. -/
theorem upperEnvelopeIntegral_neg_one_infiniteAtom :
    upperEnvelopeIntegral (fun _ : Unit ↦ (-1 : ℝ))
      ((⊤ : ENNReal) • Measure.dirac ()) = 0 := by
  apply le_antisymm
  · have h : upperEnvelopeIntegral (fun _ : Unit ↦ (-1 : ℝ))
        ((⊤ : ENNReal) • Measure.dirac ()) ≤
        (∫ _ : Unit, (0 : ℝ) ∂((⊤ : ENNReal) • Measure.dirac ()) : ℝ) :=
      sInf_le ⟨0, integrable_zero _ _ _, Eventually.of_forall fun _ ↦ by norm_num, rfl⟩
    simpa only [integral_zero, EReal.coe_zero] using h
  · apply le_sInf
    rintro r ⟨A, hA, _, rfl⟩
    rw [integrable_infiniteAtom_eq_zero A hA]
    simp only [Pi.zero_apply, integral_zero, EReal.coe_zero, le_refl]

/-- The explicit extended-envelope convention has the same value on `⊥` over that atom. -/
theorem upperERealEnvelopeIntegral_bot_infiniteAtom :
    upperERealEnvelopeIntegral (fun _ : Unit ↦ (⊥ : EReal))
      ((⊤ : ENNReal) • Measure.dirac ()) = 0 := by
  apply le_antisymm
  · have h : upperERealEnvelopeIntegral (fun _ : Unit ↦ (⊥ : EReal))
        ((⊤ : ENNReal) • Measure.dirac ()) ≤
        (∫ _ : Unit, (0 : ℝ) ∂((⊤ : ENNReal) • Measure.dirac ()) : ℝ) :=
      sInf_le ⟨0, integrable_zero _ _ _, Eventually.of_forall fun _ ↦ bot_le, rfl⟩
    simpa only [integral_zero, EReal.coe_zero] using h
  · apply le_sInf
    rintro r ⟨A, hA, _, rfl⟩
    rw [integrable_infiniteAtom_eq_zero A hA]
    simp only [Pi.zero_apply, integral_zero, EReal.coe_zero, le_refl]

end ArakelovGeometry
