/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Minima.Basic
public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic
public import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Normalization.Hermitian

import ArakelovGeometry.AdelicVectorBundle.Minima.Basis
import ArakelovGeometry.AdelicVectorBundle.Slope.Rescaling
import Mathlib.Algebra.Order.Star.Real

/-! # Pointwise completed-norm comparison of actual minima and maximal slopes -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldMinimumSlopeComparison

open AdelicStructure

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- Integrating the given bound on actual completed vectors gives the original vector-degree
shift; no vector-degree comparison is assumed. -/
theorem vectorDegree_sub_integral_le
    (P : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K))
    (Q : NormFamily (normalizedNumberFieldAdelicStructure K) P) [hQ : Q.IsAdelic]
    (b : (normalizedNumberFieldAdelicStructure K).Ω → ℝ)
    (hb : Integrable b (normalizedNumberFieldAdelicStructure K).v)
    (h : ∀ ω z, Q.norm ω z ≤ Real.exp (b ω) * P.toNormFamily.norm ω z)
    (s : {x : P // x ≠ 0}) :
    P.vectorDegree s - (∫ ω, b ω ∂(normalizedNumberFieldAdelicStructure K).v) ≤
      Q.toAdelicVectorBundle.vectorDegree s := by
  have hp := P.integrable_logNorm s.val
  have hq := Q.toAdelicVectorBundle.integrable_logNorm s.val
  have hl (ω : (normalizedNumberFieldAdelicStructure K).Ω) :
      Q.logNorm s.val ω ≤ b ω + P.toNormFamily.logNorm s.val ω := by
    have he := Real.log_le_log (Q.norm_rational_pos ω s.property)
      (h ω (1 ⊗ₜ[K] s.val))
    rwa [Real.log_mul (Real.exp_ne_zero _) (P.toNormFamily.norm_rational_pos ω s.property).ne',
      Real.log_exp] at he
  have hi := integral_mono hq (hb.add hp) hl
  simp only [Pi.add_apply] at hi
  rw [integral_add hb hp] at hi
  simp only [AdelicVectorBundle.vectorDegree, NormFamily.vectorDegree_eq_neg_integral]
  linarith

/-- Actual independent threshold families give the same finite translation of every
ordinary logarithmic minimum, including zero and above-rank indices. -/
theorem logarithmicMinimum_sub_integral_le
    (P : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K))
    (Q : NormFamily (normalizedNumberFieldAdelicStructure K) P) [hQ : Q.IsAdelic]
    (b : (normalizedNumberFieldAdelicStructure K).Ω → ℝ)
    (hb : Integrable b (normalizedNumberFieldAdelicStructure K).v)
    (h : ∀ ω z, Q.norm ω z ≤ Real.exp (b ω) * P.toNormFamily.norm ω z)
    (i : ℕ) :
    P.logarithmicMinimum i -
      ((∫ ω, b ω ∂(normalizedNumberFieldAdelicStructure K).v : ℝ) : EReal) ≤
        Q.toAdelicVectorBundle.logarithmicMinimum i := by
  apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mpr
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  obtain ⟨s, hli, hs⟩ := (P.le_finrank_degreeThresholdSpan_iff i t).mp ht
  have hlower : ((t - ∫ ω, b ω ∂(normalizedNumberFieldAdelicStructure K).v : ℝ) : EReal) ≤
      Q.toAdelicVectorBundle.logarithmicMinimum i := by
    apply Q.toAdelicVectorBundle.coe_le_logarithmicMinimum_of_linearIndependent s hli
    intro j
    have hd := vectorDegree_sub_integral_le P (Q.toAdelicVectorBundle) b hb h (s j)
    linarith [hs j]
  rw [EReal.coe_sub] at hlower
  exact (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mp hlower

/-- Two literal pointwise completed-norm inequalities give the source two-sided ordinary
minimum comparison. Every natural index retains its existing extended endpoint. -/
theorem logarithmicMinimum_comparison
    (P : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K))
    (Q : NormFamily (normalizedNumberFieldAdelicStructure K) P) [hQ : Q.IsAdelic]
    (a b : (normalizedNumberFieldAdelicStructure K).Ω → ℝ)
    (ha : Integrable a (normalizedNumberFieldAdelicStructure K).v)
    (hb : Integrable b (normalizedNumberFieldAdelicStructure K).v)
    (hlower : ∀ ω z, Real.exp (a ω) * P.toNormFamily.norm ω z ≤ Q.norm ω z)
    (hupper : ∀ ω z, Q.norm ω z ≤ Real.exp (b ω) * P.toNormFamily.norm ω z)
    (i : ℕ) :
    P.logarithmicMinimum i -
        ((∫ ω, b ω ∂(normalizedNumberFieldAdelicStructure K).v : ℝ) : EReal) ≤
      Q.toAdelicVectorBundle.logarithmicMinimum i ∧
    Q.toAdelicVectorBundle.logarithmicMinimum i ≤ P.logarithmicMinimum i -
      ((∫ ω, a ω ∂(normalizedNumberFieldAdelicStructure K).v : ℝ) : EReal) := by
  refine ⟨logarithmicMinimum_sub_integral_le P (Q.toAdelicVectorBundle) b hb hupper i, ?_⟩
  have hreverse (ω : (normalizedNumberFieldAdelicStructure K).Ω) (z) :
      P.toNormFamily.norm ω z ≤ Real.exp (-a ω) * Q.norm ω z := by
    calc
      _ = Real.exp (-a ω) * (Real.exp (a ω) * P.toNormFamily.norm ω z) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlower ω z) (Real.exp_pos _).le
  have h := logarithmicMinimum_sub_integral_le (Q.toAdelicVectorBundle) P (-a) ha.neg hreverse i
  simp only [Pi.neg_apply] at h
  rw [integral_neg] at h
  have he := (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mp h
  simpa only [EReal.coe_neg, sub_eq_add_neg] using he

/-- Enlarging every actual completed norm decreases the actual maximal slope. The proof
uses determinant-degree monotonicity on every genuine completed restriction. -/
theorem maximalSlope_antitone_norm
    (P : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K))
    (Q : NormFamily (normalizedNumberFieldAdelicStructure K) P) [hQ : Q.IsAdelic]
    (h : P.toNormFamily ≤ Q) :
    Q.toAdelicVectorBundle.maximalSlope ≤
      P.maximalSlope := by
  apply Q.toAdelicVectorBundle.maximalSlope_le
  intro F hF
  have hrestrict :
      (P.restrictOfMeasurableBase F).toNormFamily ≤
        (Q.toAdelicVectorBundle.restrictOfMeasurableBase F).toNormFamily := by
    intro ω z
    exact h ω (F.subtype.baseChange _ z)
  have hd := AdelicVectorBundle.degree_antitone
    (P.restrictOfMeasurableBase F)
    (Q.toAdelicVectorBundle.restrictOfMeasurableBase F).toNormFamily
    (hW := (Q.toAdelicVectorBundle.restrictOfMeasurableBase F).toIsAdelic) hrestrict
  have hs :
      (Q.toAdelicVectorBundle.restrictOfMeasurableBase F).slope
          ≤
        (P.restrictOfMeasurableBase F).slope
          :=
    div_le_div_of_nonneg_right hd (Nat.cast_pos.mpr hF).le
  exact (EReal.coe_le_coe hs).trans (P.slope_restrict_le_maximalSlope F hF
   )

/-- Actual exponential rescaling and norm antitonicity give the maximal-slope shift from
an upper completed-norm bound, including the zero-space convention. -/
theorem maximalSlope_sub_integral_le
    (P : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K))
    (Q : NormFamily (normalizedNumberFieldAdelicStructure K) P) [hQ : Q.IsAdelic]
    (b : (normalizedNumberFieldAdelicStructure K).Ω → ℝ)
    (hb : Integrable b (normalizedNumberFieldAdelicStructure K).v)
    (h : ∀ ω z, Q.norm ω z ≤ Real.exp (b ω) * P.toNormFamily.norm ω z) :
    P.maximalSlope -
      ((∫ ω, b ω ∂(normalizedNumberFieldAdelicStructure K).v : ℝ) : EReal) ≤
        Q.toAdelicVectorBundle.maximalSlope := by
  have he := maximalSlope_antitone_norm Q.toAdelicVectorBundle
    (P.scaleExp b Measurable.of_discrete hb).toNormFamily
    (hQ := (P.scaleExp b Measurable.of_discrete hb).toIsAdelic)
    (by intro ω z; exact h ω z)
  rwa [P.maximalSlope_scaleExp b Measurable.of_discrete hb
   ] at he

/-- The source two-sided actual maximal-slope comparison, derived from the completed-norm
inequalities and the integrable exponents alone. -/
theorem maximalSlope_comparison
    (P : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K))
    (Q : NormFamily (normalizedNumberFieldAdelicStructure K) P) [hQ : Q.IsAdelic]
    (a b : (normalizedNumberFieldAdelicStructure K).Ω → ℝ)
    (ha : Integrable a (normalizedNumberFieldAdelicStructure K).v)
    (hb : Integrable b (normalizedNumberFieldAdelicStructure K).v)
    (hlower : ∀ ω z, Real.exp (a ω) * P.toNormFamily.norm ω z ≤ Q.norm ω z)
    (hupper : ∀ ω z, Q.norm ω z ≤ Real.exp (b ω) * P.toNormFamily.norm ω z) :
    P.maximalSlope -
        ((∫ ω, b ω ∂(normalizedNumberFieldAdelicStructure K).v : ℝ) : EReal) ≤
      Q.toAdelicVectorBundle.maximalSlope ∧
    Q.toAdelicVectorBundle.maximalSlope ≤
      P.maximalSlope -
        ((∫ ω, a ω ∂(normalizedNumberFieldAdelicStructure K).v : ℝ) : EReal) := by
  refine ⟨maximalSlope_sub_integral_le P (Q.toAdelicVectorBundle) b hb hupper, ?_⟩
  have he := maximalSlope_antitone_norm (P.scaleExp a Measurable.of_discrete ha) Q
    (by intro ω z; exact hlower ω z)
  rwa [P.maximalSlope_scaleExp a Measurable.of_discrete ha
   ] at he

/-- The actual integrable completed-fibre distance bounds all ordinary minima and the
actual maximal slope by the given real integral bound. -/
theorem minima_and_maximalSlope_of_integral_localDist_le
    (P : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K))
    (Q : NormFamily (normalizedNumberFieldAdelicStructure K) P) [hQ : Q.IsAdelic]
    (hδ : Integrable (P.toNormFamily.localDist Q)
      (normalizedNumberFieldAdelicStructure K).v)
    {ε : ℝ} (hε : (∫ ω, P.toNormFamily.localDist Q ω
      ∂(normalizedNumberFieldAdelicStructure K).v) ≤ ε) :
    (∀ i : ℕ, P.logarithmicMinimum i - (ε : EReal) ≤ Q.toAdelicVectorBundle.logarithmicMinimum i ∧
      Q.toAdelicVectorBundle.logarithmicMinimum i ≤ P.logarithmicMinimum i + (ε : EReal)) ∧
    P.maximalSlope -
        (ε : EReal) ≤
      Q.toAdelicVectorBundle.maximalSlope ∧
    Q.toAdelicVectorBundle.maximalSlope ≤
      P.maximalSlope +
        (ε : EReal) := by
  let δ := P.toNormFamily.localDist Q
  have hnorm (ω : (normalizedNumberFieldAdelicStructure K).Ω) (z) :
      Real.exp (-δ ω) * P.toNormFamily.norm ω z ≤ Q.norm ω z ∧
        Q.norm ω z ≤ Real.exp (δ ω) * P.toNormFamily.norm ω z :=
    ((P.toNormFamily.localDist_le_iff Q ω
      (P.toNormFamily.localDist_nonneg Q ω)).mp le_rfl) z
  have hm := logarithmicMinimum_comparison P (Q.toAdelicVectorBundle) (-δ) δ hδ.neg hδ
    (fun ω z => (hnorm ω z).1) (fun ω z => (hnorm ω z).2)
  have hs := maximalSlope_comparison P (Q.toAdelicVectorBundle) (-δ) δ hδ.neg hδ
    (fun ω z => (hnorm ω z).1) (fun ω z => (hnorm ω z).2)
  simp only [Pi.neg_apply, integral_neg, EReal.coe_neg, sub_eq_add_neg, neg_neg] at hm hs
  refine ⟨fun i => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact (EReal.sub_le_sub le_rfl (EReal.coe_le_coe hε)).trans (hm i).1
  · exact (hm i).2.trans (add_le_add le_rfl (EReal.coe_le_coe hε))
  · exact (EReal.sub_le_sub le_rfl (EReal.coe_le_coe hε)).trans hs.1
  · exact hs.2.trans (add_le_add le_rfl (EReal.coe_le_coe hε))

end ArakelovGeometry.NumberFieldMinimumSlopeComparison
