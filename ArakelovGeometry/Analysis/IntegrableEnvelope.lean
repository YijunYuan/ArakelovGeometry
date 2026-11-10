/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.EReal.Basic

/-!
# Integrable envelopes of arbitrary real functions

Upper and lower integrable envelopes use almost-everywhere inequalities and do
not impose measurability on the bounded function. These are the envelope
conditions in Chen–Moriwaki, Definition 4.1.1 and Appendix A.4.
-/

open MeasureTheory Filter

namespace ArakelovGeometry

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}

/-- An integrable almost-everywhere majorant, without measurability of `f`. -/
def HasIntegrableUpperBound (f : Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∃ A : Ω → ℝ, Integrable A μ ∧ f ≤ᵐ[μ] A

/-- An integrable almost-everywhere minorant, without measurability of `f`. -/
def HasIntegrableLowerBound (f : Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∃ B : Ω → ℝ, Integrable B μ ∧ B ≤ᵐ[μ] f

/-- Two-sided domination by integrable functions. -/
def HasIntegrableBounds (f : Ω → ℝ) (μ : Measure Ω) : Prop :=
  HasIntegrableUpperBound f μ ∧ HasIntegrableLowerBound f μ

theorem HasIntegrableUpperBound.mono (hg : HasIntegrableUpperBound g μ)
    (hfg : f ≤ᵐ[μ] g) : HasIntegrableUpperBound f μ := by
  obtain ⟨A, hA, hgA⟩ := hg
  exact ⟨A, hA, hfg.trans hgA⟩

theorem HasIntegrableLowerBound.mono (hf : HasIntegrableLowerBound f μ)
    (hfg : f ≤ᵐ[μ] g) : HasIntegrableLowerBound g μ := by
  obtain ⟨B, hB, hBf⟩ := hf
  exact ⟨B, hB, hBf.trans hfg⟩

theorem HasIntegrableUpperBound.congr (hf : HasIntegrableUpperBound f μ)
    (hfg : f =ᵐ[μ] g) : HasIntegrableUpperBound g μ :=
  hf.mono (hfg.symm.le)

theorem HasIntegrableLowerBound.congr (hf : HasIntegrableLowerBound f μ)
    (hfg : f =ᵐ[μ] g) : HasIntegrableLowerBound g μ :=
  hf.mono hfg.le

theorem HasIntegrableUpperBound.neg (hf : HasIntegrableUpperBound f μ) :
    HasIntegrableLowerBound (fun ω ↦ -f ω) μ := by
  obtain ⟨A, hA, hfA⟩ := hf
  exact ⟨-A, hA.neg, hfA.mono fun _ h ↦ neg_le_neg h⟩

theorem HasIntegrableLowerBound.neg (hf : HasIntegrableLowerBound f μ) :
    HasIntegrableUpperBound (fun ω ↦ -f ω) μ := by
  obtain ⟨B, hB, hBf⟩ := hf
  exact ⟨-B, hB.neg, hBf.mono fun _ h ↦ neg_le_neg h⟩

theorem HasIntegrableUpperBound.add (hf : HasIntegrableUpperBound f μ)
    (hg : HasIntegrableUpperBound g μ) : HasIntegrableUpperBound (f + g) μ := by
  obtain ⟨A, hA, hfA⟩ := hf
  obtain ⟨B, hB, hgB⟩ := hg
  exact ⟨A + B, hA.add hB, hfA.and hgB |>.mono fun _ h ↦ add_le_add h.1 h.2⟩

theorem HasIntegrableLowerBound.add (hf : HasIntegrableLowerBound f μ)
    (hg : HasIntegrableLowerBound g μ) : HasIntegrableLowerBound (f + g) μ := by
  obtain ⟨A, hA, hAf⟩ := hf
  obtain ⟨B, hB, hBg⟩ := hg
  exact ⟨A + B, hA.add hB, hAf.and hBg |>.mono fun _ h ↦ add_le_add h.1 h.2⟩

/-- Two integrable envelopes are equivalent to a nonnegative integrable absolute bound. -/
theorem hasIntegrableBounds_iff_abs_le : HasIntegrableBounds f μ ↔
    ∃ C : Ω → ℝ, Integrable C μ ∧ (∀ ω, 0 ≤ C ω) ∧
      ∀ᵐ ω ∂μ, |f ω| ≤ C ω := by
  constructor
  · rintro ⟨⟨A, hA, hfA⟩, ⟨B, hB, hBf⟩⟩
    refine ⟨fun ω ↦ |A ω| + |B ω|, hA.abs.add hB.abs, fun ω ↦ by positivity, ?_⟩
    filter_upwards [hfA, hBf] with ω h₁ h₂
    apply abs_le.mpr
    constructor
    · have := neg_abs_le (B ω)
      have := abs_nonneg (A ω)
      linarith
    · have := le_abs_self (A ω)
      have := abs_nonneg (B ω)
      linarith
  · rintro ⟨C, hC, _, hfC⟩
    exact ⟨⟨C, hC, hfC.mono fun _ h ↦ (le_abs_self _).trans h⟩,
      ⟨-C, hC.neg, hfC.mono fun _ h ↦ (neg_le_neg h).trans (neg_abs_le _)⟩⟩

/-- A measurable function with integrable envelopes is integrable. -/
theorem HasIntegrableBounds.integrable (hf : HasIntegrableBounds f μ)
    (hm : AEStronglyMeasurable f μ) : Integrable f μ := by
  obtain ⟨C, hC, hCpos, hbound⟩ := hasIntegrableBounds_iff_abs_le.mp hf
  apply hC.mono' hm
  simpa only [Real.norm_eq_abs] using hbound

theorem integrable_hasIntegrableBounds (hf : Integrable f μ) :
    HasIntegrableBounds f μ :=
  ⟨⟨f, hf, Eventually.of_forall fun _ ↦ le_rfl⟩,
    ⟨f, hf, Eventually.of_forall fun _ ↦ le_rfl⟩⟩

/-- The upper integral defined by integrable majorants, with value `⊤` if none exists. -/
noncomputable def upperEnvelopeIntegral (f : Ω → ℝ) (μ : Measure Ω) : EReal :=
  sInf {r | ∃ A : Ω → ℝ, Integrable A μ ∧ f ≤ᵐ[μ] A ∧ r = (∫ ω, A ω ∂μ : ℝ)}

/-- The lower integral defined by integrable minorants, with value `⊥` if none exists. -/
noncomputable def lowerEnvelopeIntegral (f : Ω → ℝ) (μ : Measure Ω) : EReal :=
  sSup {r | ∃ B : Ω → ℝ, Integrable B μ ∧ B ≤ᵐ[μ] f ∧ r = (∫ ω, B ω ∂μ : ℝ)}

theorem hasIntegrableUpperBound_iff_upperEnvelopeIntegral_lt_top :
    HasIntegrableUpperBound f μ ↔ upperEnvelopeIntegral f μ < ⊤ := by
  constructor
  · rintro ⟨A, hA, hfA⟩
    have hle : upperEnvelopeIntegral f μ ≤ (∫ ω, A ω ∂μ : ℝ) :=
      sInf_le ⟨A, hA, hfA, rfl⟩
    exact hle.trans_lt (EReal.coe_lt_top _)
  · intro h
    by_contra hn
    have he : {r : EReal | ∃ A : Ω → ℝ,
        Integrable A μ ∧ f ≤ᵐ[μ] A ∧ r = (∫ ω, A ω ∂μ : ℝ)} = ∅ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨A, hA, hfA, _⟩
      exact hn ⟨A, hA, hfA⟩
    simp [upperEnvelopeIntegral, he] at h

theorem hasIntegrableLowerBound_iff_bot_lt_lowerEnvelopeIntegral :
    HasIntegrableLowerBound f μ ↔ ⊥ < lowerEnvelopeIntegral f μ := by
  constructor
  · rintro ⟨B, hB, hBf⟩
    exact (EReal.bot_lt_coe _).trans_le (le_sSup ⟨B, hB, hBf, rfl⟩)
  · intro h
    by_contra hn
    have he : {r : EReal | ∃ B : Ω → ℝ,
        Integrable B μ ∧ B ≤ᵐ[μ] f ∧ r = (∫ ω, B ω ∂μ : ℝ)} = ∅ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨B, hB, hBf, _⟩
      exact hn ⟨B, hB, hBf⟩
    simp [lowerEnvelopeIntegral, he] at h

/-- An upper envelope can be chosen measurable without changing its integral. -/
theorem measurable_upper_envelope {A : Ω → ℝ} (hA : Integrable A μ)
    (hfA : f ≤ᵐ[μ] A) : ∃ B : Ω → ℝ, Measurable B ∧ Integrable B μ ∧
      f ≤ᵐ[μ] B ∧ ∫ ω, B ω ∂μ = ∫ ω, A ω ∂μ := by
  let h := hA.aestronglyMeasurable
  refine ⟨h.mk A, h.stronglyMeasurable_mk.measurable, hA.congr h.ae_eq_mk,
    hfA.trans h.ae_eq_mk.le, ?_⟩
  exact integral_congr_ae h.ae_eq_mk.symm

/-- A lower envelope can be chosen measurable without changing its integral. -/
theorem measurable_lower_envelope {B : Ω → ℝ} (hB : Integrable B μ)
    (hBf : B ≤ᵐ[μ] f) : ∃ A : Ω → ℝ, Measurable A ∧ Integrable A μ ∧
      A ≤ᵐ[μ] f ∧ ∫ ω, A ω ∂μ = ∫ ω, B ω ∂μ := by
  let h := hB.aestronglyMeasurable
  refine ⟨h.mk B, h.stronglyMeasurable_mk.measurable, hB.congr h.ae_eq_mk,
    h.ae_eq_mk.symm.le.trans hBf, ?_⟩
  exact integral_congr_ae h.ae_eq_mk.symm

theorem HasIntegrableUpperBound.max (hf : HasIntegrableUpperBound f μ)
    (hg : HasIntegrableUpperBound g μ) :
    HasIntegrableUpperBound (fun ω ↦ max (f ω) (g ω)) μ := by
  obtain ⟨A, hA, hfA⟩ := hf
  obtain ⟨B, hB, hgB⟩ := hg
  refine ⟨fun ω ↦ |A ω| + |B ω|, hA.abs.add hB.abs, ?_⟩
  filter_upwards [hfA, hgB] with ω h₁ h₂
  apply max_le
  · exact h₁.trans ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _)))
  · exact h₂.trans ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _)))

theorem HasIntegrableBounds.add (hf : HasIntegrableBounds f μ)
    (hg : HasIntegrableBounds g μ) : HasIntegrableBounds (f + g) μ :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

theorem HasIntegrableBounds.neg (hf : HasIntegrableBounds f μ) :
    HasIntegrableBounds (fun ω ↦ -f ω) μ := ⟨hf.2.neg, hf.1.neg⟩

theorem HasIntegrableBounds.abs (hf : HasIntegrableBounds f μ) :
    HasIntegrableBounds (fun ω ↦ |f ω|) μ := by
  obtain ⟨C, hC, _, hbound⟩ := hasIntegrableBounds_iff_abs_le.mp hf
  exact ⟨⟨C, hC, hbound⟩, ⟨0, integrable_zero _ _ _,
    Eventually.of_forall fun _ ↦ abs_nonneg _⟩⟩

theorem HasIntegrableBounds.max (hf : HasIntegrableBounds f μ)
    (hg : HasIntegrableBounds g μ) : HasIntegrableBounds (fun ω ↦ max (f ω) (g ω)) μ :=
  ⟨hf.1.max hg.1, hf.2.mono (Eventually.of_forall fun _ ↦ le_max_left _ _)⟩

/-- Domination transfers through an almost-everywhere absolute-value bound. -/
theorem HasIntegrableBounds.of_abs_le (hg : HasIntegrableBounds g μ)
    (hfg : (fun ω ↦ |f ω|) ≤ᵐ[μ] g) : HasIntegrableBounds f μ := by
  obtain ⟨C, hC, hCpos, hbound⟩ := hasIntegrableBounds_iff_abs_le.mp hg
  apply hasIntegrableBounds_iff_abs_le.mpr
  refine ⟨C, hC, hCpos, ?_⟩
  filter_upwards [hfg, hbound] with ω h₁ h₂
  exact h₁.trans ((le_abs_self _).trans h₂)

theorem HasIntegrableBounds.congr (hf : HasIntegrableBounds f μ) (hfg : f =ᵐ[μ] g) :
    HasIntegrableBounds g μ := ⟨hf.1.congr hfg, hf.2.congr hfg⟩

/-- A finite sum of upper-dominated functions is upper dominated. -/
theorem hasIntegrableUpperBound_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → Ω → ℝ) (h : ∀ i ∈ s, HasIntegrableUpperBound (f i) μ) :
    HasIntegrableUpperBound (fun ω ↦ ∑ i ∈ s, f i ω) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun _ ↦ 0, integrable_zero Ω ℝ μ, ?_⟩
    exact Eventually.of_forall fun _ ↦ by simp
  | @insert i s hi ih =>
    have hs := ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
    convert (h i (Finset.mem_insert_self _ _)).add hs using 1
    ext ω
    simp [Finset.sum_insert hi]

/-- A finite sum of dominated functions is dominated. -/
theorem hasIntegrableBounds_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → Ω → ℝ) (h : ∀ i ∈ s, HasIntegrableBounds (f i) μ) :
    HasIntegrableBounds (fun ω ↦ ∑ i ∈ s, f i ω) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    constructor <;> refine ⟨fun _ ↦ 0, integrable_zero Ω ℝ μ, ?_⟩ <;>
      exact Eventually.of_forall fun _ ↦ by simp
  | @insert i s hi ih =>
    have hs := ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
    convert (h i (Finset.mem_insert_self _ _)).add hs using 1
    ext ω
    simp [Finset.sum_insert hi]

/-- A nonempty finite maximum of upper-dominated functions is upper dominated. -/
theorem hasIntegrableUpperBound_finset_sup' {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (f : ι → Ω → ℝ)
    (h : ∀ i ∈ s, HasIntegrableUpperBound (f i) μ) :
    HasIntegrableUpperBound (fun ω ↦ s.sup' hs (fun i ↦ f i ω)) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hs).elim
  | @insert i s hi ih =>
    by_cases hn : s.Nonempty
    · have ht := ih hn (fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sup'_insert hn] using
        (h i (Finset.mem_insert_self _ _)).max ht
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst s
      simpa using h i (Finset.mem_insert_self _ _)

/-- A nonempty finite maximum of dominated functions is dominated. -/
theorem hasIntegrableBounds_finset_sup' {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (f : ι → Ω → ℝ)
    (h : ∀ i ∈ s, HasIntegrableBounds (f i) μ) :
    HasIntegrableBounds (fun ω ↦ s.sup' hs (fun i ↦ f i ω)) μ := by
  refine ⟨hasIntegrableUpperBound_finset_sup' s hs f (fun i hi ↦ (h i hi).1), ?_⟩
  obtain ⟨i, hi⟩ := hs
  exact (h i hi).2.mono (Eventually.of_forall fun ω ↦ Finset.le_sup' (fun j ↦ f j ω) hi)

/-- On an integrable function the upper-envelope integral is the ordinary integral. -/
theorem upperEnvelopeIntegral_eq_integral (hf : Integrable f μ) :
    upperEnvelopeIntegral f μ = (∫ ω, f ω ∂μ : ℝ) := by
  apply le_antisymm
  · exact sInf_le ⟨f, hf, Eventually.of_forall fun _ ↦ le_rfl, rfl⟩
  · apply le_sInf
    rintro _ ⟨A, hA, hfA, rfl⟩
    exact_mod_cast integral_mono_ae hf hA hfA

/-- On an integrable function the lower-envelope integral is the ordinary integral. -/
theorem lowerEnvelopeIntegral_eq_integral (hf : Integrable f μ) :
    lowerEnvelopeIntegral f μ = (∫ ω, f ω ∂μ : ℝ) := by
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨B, hB, hBf, rfl⟩
    exact_mod_cast integral_mono_ae hB hf hBf
  · exact le_sSup ⟨f, hf, Eventually.of_forall fun _ ↦ le_rfl, rfl⟩

end ArakelovGeometry
