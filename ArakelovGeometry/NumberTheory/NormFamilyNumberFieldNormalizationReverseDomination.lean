/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldNormalizationDual
public import ArakelovGeometry.NumberTheory.NormalizedNumberFieldIntegralComparison

/-!
# Reflection of actual number-field norm domination

Integrable normalized envelopes pull back through the actual positive exponent.
For every fixed old ultrametric family, actual normalization preserves and
reflects upper, lower and full domination, without recovering the trivial norm.
-/

@[expose] public section

open MeasureTheory NumberField
open scoped ENNReal

noncomputable section

namespace ArakelovGeometry.AdelicStructure

variable {K : Type*} [Field K] [NumberField K]

/-- A normalized real envelope pulls back through the genuine positive norm
exponent; assign zero at the old zero-mass trivial class. -/
def numberFieldNormalizationPullback
    (f : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K} → ℝ)
    (ω : AbsoluteValue.Place K) : ℝ := by
  classical
  exact if hω : ω = AbsoluteValue.trivialPlace K then 0 else
    (numberFieldNormalizationExponent ⟨ω, hω⟩)⁻¹ * f ⟨ω, hω⟩

/-- The actual exponent cancels the pullback at every nontrivial class. -/
theorem normalizationExponent_mul_pullback
    (f : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K} → ℝ)
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) :
    numberFieldNormalizationExponent ω * numberFieldNormalizationPullback f ω.val = f ω := by
  classical
  simp only [numberFieldNormalizationPullback, dite_eq_right ω.property]
  rw [← mul_assoc, mul_inv_cancel₀ (numberFieldNormalizationExponent_pos ω).ne', one_mul]

/-- Every genuine normalized integrable envelope has an old integrable pullback. -/
theorem integrable_numberFieldNormalizationPullback
    (f : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K} → ℝ)
    (hf : Integrable f (normalizedNumberFieldAdelicStructure K).v) :
    Integrable (numberFieldNormalizationPullback f) (numberFieldAdelicStructure K).v := by
  apply (integrable_numberFieldNormalizationExponent_mul_iff
    (numberFieldNormalizationPullback f)).mp
  exact hf.congr (Filter.Eventually.of_forall
    (fun ω => (normalizationExponent_mul_pullback f ω).symm))

/-- Actual normalized almost-everywhere assertions hold at every nontrivial class. -/
theorem forall_nontrivial_of_normalizedNumberField_ae
    (p : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K} → Prop)
    (hp : ∀ᵐ ω ∂(normalizedNumberFieldAdelicStructure K).v, p ω)
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) : p ω := by
  apply (ae_iff_of_countable.mp hp) ω
  intro hzero
  have h := normalizationExponent_mul_singleton_toReal ω
  erw [hzero, ENNReal.toReal_zero, mul_zero] at h
  exact (placeWeight_toReal_pos_of_nontrivial ω).ne' h.symm

/-- An assertion true at all nontrivial classes is true almost everywhere on the old curve. -/
theorem numberField_ae_of_forall_nontrivial
    (p : AbsoluteValue.Place K → Prop)
    (hp : ∀ ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}, p ω.val) :
    ∀ᵐ ω ∂(numberFieldAdelicStructure K).v, p ω := by
  let oldMeasurable : MeasurableSpace (AbsoluteValue.Place K) := ⊤
  apply ae_iff_of_countable.mpr
  intro ω hω
  have hnontrivial : ω ≠ AbsoluteValue.trivialPlace K := by
    intro heq
    subst ω
    apply hω
    change (Measure.sum fun τ : AbsoluteValue.Place K =>
      placeWeight τ • Measure.dirac τ) {AbsoluteValue.trivialPlace K} = 0
    rw [Measure.sum_smul_dirac_singleton, placeWeight_trivialPlace]
  exact hp ⟨ω, hnontrivial⟩

end ArakelovGeometry.AdelicStructure

namespace ArakelovGeometry.NormFamily

open AdelicStructure

variable {K : Type*} [Field K] [NumberField K]
  {E : Type*} [AddCommGroup E] [Module K E]

/-- Upper domination of the actual normalization reflects to the fixed old family. -/
theorem IsUpperDominated.of_numberFieldNormalize
    {ξ : NormFamily (numberFieldAdelicStructure K) E} {hξ : ξ.IsUltrametric}
    (hupper : (ξ.numberFieldNormalize hξ).IsUpperDominated) : ξ.IsUpperDominated := by
  intro x hx
  obtain ⟨A, hAi, hA⟩ := hupper x hx
  refine ⟨numberFieldNormalizationPullback A, integrable_numberFieldNormalizationPullback A hAi, ?_⟩
  apply numberField_ae_of_forall_nontrivial
  intro ω
  have hb := forall_nontrivial_of_normalizedNumberField_ae _ hA ω
  have hlog := ξ.numberFieldNormalize_logNorm hξ x ω
  have hback := normalizationExponent_mul_pullback A ω
  exact (mul_le_mul_iff_right₀ (numberFieldNormalizationExponent_pos ω)).mp
    ((hlog.symm.trans_le hb).trans_eq hback.symm)

/-- Lower domination of the actual normalization reflects to the fixed old family. -/
theorem IsLowerDominated.of_numberFieldNormalize
    {ξ : NormFamily (numberFieldAdelicStructure K) E} {hξ : ξ.IsUltrametric}
    (hlower : (ξ.numberFieldNormalize hξ).IsLowerDominated) : ξ.IsLowerDominated := by
  intro x hx
  obtain ⟨A, hAi, hA⟩ := hlower x hx
  refine ⟨numberFieldNormalizationPullback A, integrable_numberFieldNormalizationPullback A hAi, ?_⟩
  apply numberField_ae_of_forall_nontrivial
  intro ω
  have hb := forall_nontrivial_of_normalizedNumberField_ae _ hA ω
  have hlog := ξ.numberFieldNormalize_logNorm hξ x ω
  have hback := normalizationExponent_mul_pullback A ω
  exact (mul_le_mul_iff_right₀ (numberFieldNormalizationExponent_pos ω)).mp
    (hback.trans_le (hb.trans_eq hlog))

/-- Actual upper domination is unchanged for every fixed old ultrametric family. -/
theorem numberFieldNormalize_isUpperDominated_iff
    (ξ : NormFamily (numberFieldAdelicStructure K) E) (hξ : ξ.IsUltrametric) :
    (ξ.numberFieldNormalize hξ).IsUpperDominated ↔ ξ.IsUpperDominated :=
  ⟨IsUpperDominated.of_numberFieldNormalize,
    fun h => h.numberFieldNormalize hξ⟩

/-- Actual lower domination is unchanged for every fixed old ultrametric family. -/
theorem numberFieldNormalize_isLowerDominated_iff
    (ξ : NormFamily (numberFieldAdelicStructure K) E) (hξ : ξ.IsUltrametric) :
    (ξ.numberFieldNormalize hξ).IsLowerDominated ↔ ξ.IsLowerDominated :=
  ⟨IsLowerDominated.of_numberFieldNormalize,
    fun h => h.numberFieldNormalize hξ⟩

variable [FiniteDimensional K E]

/-- Full domination is preserved and reflected using the actual completed dual
normalization equality, independently of the discarded zero-mass trivial norm. -/
theorem numberFieldNormalize_isDominated_iff
    (ξ : NormFamily (numberFieldAdelicStructure K) E) (hξ : ξ.IsUltrametric) :
    (ξ.numberFieldNormalize hξ).IsDominated ↔ ξ.IsDominated := by
  constructor
  · intro h
    refine ⟨h.1.of_numberFieldNormalize, ?_⟩
    have hdual := h.2
    erw [ξ.numberFieldNormalize_dual hξ] at hdual
    exact hdual.of_numberFieldNormalize
  · intro h
    exact h.numberFieldNormalize hξ

end ArakelovGeometry.NormFamily
