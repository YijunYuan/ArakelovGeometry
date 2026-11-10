/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldNormalizationDomination
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Exact integrals under actual number-field normalization

Completion-degree masses cancel the actual positive norm powers. Extended
nonnegative integrals and integrable real logarithmic norms are preserved.
-/

open MeasureTheory NumberField
open scoped ENNReal

noncomputable section

namespace ArakelovGeometry.AdelicStructure

variable {K : Type*} [Field K] [NumberField K]

/-- Actual atom cancellation also holds for extended nonnegative weights. -/
theorem normalizationExponent_mul_singleton
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) :
    ENNReal.ofReal (numberFieldNormalizationExponent ω) *
      (normalizedNumberFieldAdelicStructure K).v {ω} = placeWeight ω.val := by
  have hfinite : (normalizedNumberFieldAdelicStructure K).v {ω} ≠ ⊤ := by
    rw [normalizedNumberFieldAdelicStructure_v_singleton]
    exact ENNReal.natCast_ne_top _
  calc
    _ = ENNReal.ofReal (numberFieldNormalizationExponent ω *
        ((normalizedNumberFieldAdelicStructure K).v {ω}).toReal) := by
      rw [ENNReal.ofReal_mul (numberFieldNormalizationExponent_pos ω).le,
        ENNReal.ofReal_toReal hfinite]
    _ = ENNReal.ofReal (placeWeight ω.val).toReal :=
      congrArg ENNReal.ofReal (normalizationExponent_mul_singleton_toReal ω)
    _ = placeWeight ω.val := ENNReal.ofReal_toReal (placeWeight_ne_top _)

/-- Extended nonnegative integrals are preserved, including an infinite value
at the omitted zero-mass trivial class. -/
theorem lintegral_numberFieldNormalizationExponent_mul
    (f : AbsoluteValue.Place K → ℝ≥0∞) :
    (∫⁻ ω : (normalizedNumberFieldAdelicStructure K).Ω,
      ENNReal.ofReal (numberFieldNormalizationExponent ω) * f ω.val
      ∂(normalizedNumberFieldAdelicStructure K).v) =
      ∫⁻ ω, f ω ∂(numberFieldAdelicStructure K).v := by
  let oldMeasurable : MeasurableSpace (AbsoluteValue.Place K) := ⊤
  let normalizedCountable : Countable (normalizedNumberFieldAdelicStructure K).Ω :=
    inferInstanceAs (Countable {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
  let normalizedSingleton : MeasurableSingletonClass
      (normalizedNumberFieldAdelicStructure K).Ω :=
    inferInstanceAs
      (MeasurableSingletonClass {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
  let μ := (normalizedNumberFieldAdelicStructure K).v
  change (∫⁻ ω, ENNReal.ofReal (numberFieldNormalizationExponent ω) * f ω.val ∂μ) = _
  rw [lintegral_countable']
  have hold : (∫⁻ ω, f ω ∂(numberFieldAdelicStructure K).v) =
      ∑' ω : AbsoluteValue.Place K, f ω * placeWeight ω := by
    change (∫⁻ ω, f ω ∂Measure.sum fun ω => placeWeight ω • Measure.dirac ω) = _
    erw [lintegral_sum_measure]
    apply tsum_congr
    intro ω
    erw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul, mul_comm]
  rw [hold]
  calc
    _ = ∑' ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K},
        f ω.val * placeWeight ω.val := by
      apply tsum_congr
      intro ω
      change (ENNReal.ofReal (numberFieldNormalizationExponent ω) * f ω.val) *
        (normalizedNumberFieldAdelicStructure K).v {ω} = _
      erw [mul_right_comm, normalizationExponent_mul_singleton, mul_comm]
    _ = _ := by
      exact tsum_subtype_eq_of_support_subset
        (f := fun ω : AbsoluteValue.Place K => f ω * placeWeight ω)
        (s := {ω | ω ≠ AbsoluteValue.trivialPlace K}) (by
          intro ω hω heq
          subst ω
          exact hω (by simp only [placeWeight_trivialPlace, mul_zero]))

/-- Exact preservation of the extended norm integral, with no integrability premise. -/
theorem lintegral_enorm_numberFieldNormalizationExponent_mul
    (f : AbsoluteValue.Place K → ℝ) :
    (∫⁻ ω : (normalizedNumberFieldAdelicStructure K).Ω,
      ‖numberFieldNormalizationExponent ω * f ω.val‖ₑ
      ∂(normalizedNumberFieldAdelicStructure K).v) =
      ∫⁻ ω, ‖f ω‖ₑ ∂(numberFieldAdelicStructure K).v := by
  calc
    _ = ∫⁻ ω : (normalizedNumberFieldAdelicStructure K).Ω,
        ENNReal.ofReal (numberFieldNormalizationExponent ω) * ‖f ω.val‖ₑ
        ∂(normalizedNumberFieldAdelicStructure K).v := by
      apply lintegral_congr
      intro ω
      change ‖numberFieldNormalizationExponent ω • f ω.val‖ₑ = _
      erw [enorm_smul, Real.enorm_eq_ofReal_abs,
        abs_of_pos (numberFieldNormalizationExponent_pos ω)]
    _ = _ := lintegral_numberFieldNormalizationExponent_mul (fun ω => ‖f ω‖ₑ)

/-- Integrability is equivalent after deleting the old zero-mass trivial point
and applying the actual norm exponent. -/
theorem integrable_numberFieldNormalizationExponent_mul_iff
    (f : AbsoluteValue.Place K → ℝ) :
    Integrable (fun ω : (normalizedNumberFieldAdelicStructure K).Ω =>
      numberFieldNormalizationExponent ω * f ω.val) (normalizedNumberFieldAdelicStructure K).v ↔
      Integrable f (numberFieldAdelicStructure K).v := by
  let oldMeasurable : MeasurableSpace (AbsoluteValue.Place K) := ⊤
  let oldDiscrete : DiscreteMeasurableSpace (numberFieldAdelicStructure K).Ω :=
    inferInstanceAs (DiscreteMeasurableSpace (AbsoluteValue.Place K))
  let normalizedDiscrete : DiscreteMeasurableSpace (normalizedNumberFieldAdelicStructure K).Ω :=
    inferInstanceAs
      (DiscreteMeasurableSpace {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
  have hold : AEStronglyMeasurable f (numberFieldAdelicStructure K).v :=
    Measurable.of_discrete.aestronglyMeasurable
  have hnew : AEStronglyMeasurable
      (fun ω : (normalizedNumberFieldAdelicStructure K).Ω =>
        numberFieldNormalizationExponent ω * f ω.val) (normalizedNumberFieldAdelicStructure K).v :=
    Measurable.of_discrete.aestronglyMeasurable
  have heq := lintegral_enorm_numberFieldNormalizationExponent_mul f
  constructor
  · intro h
    refine ⟨hold, ?_⟩
    erw [hasFiniteIntegral_iff_enorm]
    erw [← heq]
    exact (hasFiniteIntegral_iff_enorm.mp h.2)
  · intro h
    refine ⟨hnew, ?_⟩
    erw [hasFiniteIntegral_iff_enorm, heq]
    exact (hasFiniteIntegral_iff_enorm.mp h.2)

/-- The signed integral of every integrable real function is preserved. -/
theorem integral_numberFieldNormalizationExponent_mul
    (f : AbsoluteValue.Place K → ℝ) (hf : Integrable f (numberFieldAdelicStructure K).v) :
    (∫ ω : (normalizedNumberFieldAdelicStructure K).Ω,
      numberFieldNormalizationExponent ω * f ω.val
      ∂(normalizedNumberFieldAdelicStructure K).v) =
      ∫ ω, f ω ∂(numberFieldAdelicStructure K).v := by
  let oldMeasurable : MeasurableSpace (AbsoluteValue.Place K) := ⊤
  let normalizedCountable : Countable (normalizedNumberFieldAdelicStructure K).Ω :=
    inferInstanceAs (Countable {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
  let normalizedSingleton : MeasurableSingletonClass
      (normalizedNumberFieldAdelicStructure K).Ω :=
    inferInstanceAs
      (MeasurableSingletonClass {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
  have hnew := (integrable_numberFieldNormalizationExponent_mul_iff f).mpr hf
  let μ := (normalizedNumberFieldAdelicStructure K).v
  have hold : (∫ ω, f ω ∂(numberFieldAdelicStructure K).v) =
      ∑' ω : AbsoluteValue.Place K, (placeWeight ω).toReal * f ω := by
    change (∫ ω, f ω ∂Measure.sum fun ω => placeWeight ω • Measure.dirac ω) = _
    simpa only [id_eq, smul_eq_mul] using
      (integral_sum_dirac (x := id) (c := placeWeight) (f := f) placeWeight_ne_top)
  rw [hold]
  calc
    _ = ∑' ω : (normalizedNumberFieldAdelicStructure K).Ω,
        (μ {ω}).toReal * (numberFieldNormalizationExponent ω * f ω.val) := by
      simpa only [Measure.real, smul_eq_mul] using integral_countable hnew
    _ = ∑' ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K},
        (placeWeight ω.val).toReal * f ω.val := by
      apply tsum_congr
      intro ω
      change ((normalizedNumberFieldAdelicStructure K).v {ω}).toReal *
        (numberFieldNormalizationExponent ω * f ω.val) = _
      calc
        _ = (numberFieldNormalizationExponent ω *
            ((normalizedNumberFieldAdelicStructure K).v {ω}).toReal) * f ω.val := by ring
        _ = _ := congrArg (fun r : ℝ => r * f ω.val)
          (normalizationExponent_mul_singleton_toReal ω)
    _ = _ := tsum_subtype_eq_of_support_subset
      (f := fun ω : AbsoluteValue.Place K => (placeWeight ω).toReal * f ω)
      (s := {ω | ω ≠ AbsoluteValue.trivialPlace K}) (by
        intro ω hω heq
        subst ω
        exact hω (by simp only [placeWeight_trivialPlace, ENNReal.toReal_zero, zero_mul]))

/-- The absolute real integral is preserved whenever the old real function is integrable. -/
theorem integral_abs_numberFieldNormalizationExponent_mul
    (f : AbsoluteValue.Place K → ℝ) (hf : Integrable f (numberFieldAdelicStructure K).v) :
    (∫ ω : (normalizedNumberFieldAdelicStructure K).Ω,
      |numberFieldNormalizationExponent ω * f ω.val|
      ∂(normalizedNumberFieldAdelicStructure K).v) =
      ∫ ω, |f ω| ∂(numberFieldAdelicStructure K).v := by
  have heq (ω : (normalizedNumberFieldAdelicStructure K).Ω) :
      |numberFieldNormalizationExponent ω * f ω.val| =
        numberFieldNormalizationExponent ω * |f ω.val| := by
    erw [abs_mul, abs_of_pos (numberFieldNormalizationExponent_pos ω)]
  simpa only [heq] using
    integral_numberFieldNormalizationExponent_mul (fun ω => |f ω|) hf.abs

end ArakelovGeometry.AdelicStructure

namespace ArakelovGeometry.NormFamily

open AdelicStructure

variable {K : Type*} [Field K] [NumberField K]
  {E : Type*} [AddCommGroup E] [Module K E]

/-- Actual normalized rational logarithmic norm integrals agree with the old ones. -/
theorem numberFieldNormalize_integral_logNorm
    (ξ : NormFamily (numberFieldAdelicStructure K) E) (hξ : ξ.IsUltrametric) (x : E)
    (hx : Integrable (ξ.logNorm x) (numberFieldAdelicStructure K).v) :
    (∫ ω, (ξ.numberFieldNormalize hξ).logNorm x ω
      ∂(normalizedNumberFieldAdelicStructure K).v) =
      ∫ ω, ξ.logNorm x ω ∂(numberFieldAdelicStructure K).v := by
  exact (integral_congr_ae (Filter.Eventually.of_forall
    (fun ω => ξ.numberFieldNormalize_logNorm hξ x ω))).trans
      (integral_numberFieldNormalizationExponent_mul (ξ.logNorm x) hx)

/-- Actual normalized absolute logarithmic norm integrals agree with the old ones. -/
theorem numberFieldNormalize_integral_abs_logNorm
    (ξ : NormFamily (numberFieldAdelicStructure K) E) (hξ : ξ.IsUltrametric) (x : E)
    (hx : Integrable (ξ.logNorm x) (numberFieldAdelicStructure K).v) :
    (∫ ω, |(ξ.numberFieldNormalize hξ).logNorm x ω|
      ∂(normalizedNumberFieldAdelicStructure K).v) =
      ∫ ω, |ξ.logNorm x ω| ∂(numberFieldAdelicStructure K).v := by
  exact (integral_congr_ae (Filter.Eventually.of_forall
    (fun ω => congrArg abs (ξ.numberFieldNormalize_logNorm hξ x ω)))).trans
      (integral_abs_numberFieldNormalizationExponent_mul (ξ.logNorm x) hx)

end ArakelovGeometry.NormFamily
