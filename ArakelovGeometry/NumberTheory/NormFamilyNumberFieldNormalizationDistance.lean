/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldNormalizationDual
import ArakelovGeometry.NumberTheory.NormalizedNumberFieldIntegralComparison
import ArakelovGeometry.AdelicVectorBundle.Comparison

/-!
# Local distance under actual number-field normalization

The actual completed tensor transport scales every local logarithmic distance
by the positive normalization exponent. The degree-weighted atomic measure
then preserves integrability and the global distance integral.
-/

open MeasureTheory NumberField
open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

open AdelicStructure

variable {K : Type*} [Field K] [NumberField K]
  {E : Type*} [AddCommGroup E] [Module K E]

variable (ξ η : NormFamily (numberFieldAdelicStructure K) E)
  (hξ : ξ.IsUltrametric) (hη : η.IsUltrametric)

/-- Logarithmic norms transport on the whole actual completed fibre, including zero. -/
theorem numberFieldNormalize_log_norm_map
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (y : (placeRep ω.val).Completion ⊗[K] E) :
    Real.log ((ξ.numberFieldNormalize hξ).norm ω (normalizedNormFamilyTensorEquiv ω y)) =
      numberFieldNormalizationExponent ω * Real.log (ξ.norm ω.val y) := by
  by_cases hy : y = 0
  · simp only [hy, map_zero]
    erw [(ξ.numberFieldNormalize hξ).norm_zero ω, ξ.norm_zero ω.val]
    simp only [Real.log_zero, mul_zero]
  · erw [numberFieldNormalize_norm_map, Real.log_rpow (ξ.norm_pos ω.val hy)]

/-- Every completed logarithmic discrepancy scales by the positive actual exponent. -/
theorem numberFieldNormalize_log_discrepancy_map
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (y : (placeRep ω.val).Completion ⊗[K] E) :
    |Real.log ((ξ.numberFieldNormalize hξ).norm ω (normalizedNormFamilyTensorEquiv ω y)) -
      Real.log ((η.numberFieldNormalize hη).norm ω (normalizedNormFamilyTensorEquiv ω y))| =
      numberFieldNormalizationExponent ω *
        |Real.log (ξ.norm ω.val y) - Real.log (η.norm ω.val y)| := by
  erw [numberFieldNormalize_log_norm_map, numberFieldNormalize_log_norm_map,
    ← mul_sub, abs_mul, abs_of_pos (numberFieldNormalizationExponent_pos ω)]

variable [FiniteDimensional K E]

/-- The actual supremum distance scales by the normalization exponent. -/
theorem numberFieldNormalize_localDist
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) :
    (ξ.numberFieldNormalize hξ).localDist (η.numberFieldNormalize hη) ω =
      numberFieldNormalizationExponent ω * ξ.localDist η ω.val := by
  let θ := numberFieldNormalizationExponent ω
  have hθ : 0 < θ := numberFieldNormalizationExponent_pos ω
  apply le_antisymm
  · apply localDist_le
    intro z
    obtain ⟨y, rfl⟩ := (normalizedNormFamilyTensorEquiv ω).surjective z
    erw [numberFieldNormalize_log_discrepancy_map]
    exact mul_le_mul_of_nonneg_left (ξ.log_norm_sub_le_localDist η ω.val y) hθ.le
  · have hbound : ξ.localDist η ω.val ≤
        (ξ.numberFieldNormalize hξ).localDist (η.numberFieldNormalize hη) ω / θ := by
      apply localDist_le
      intro y
      apply (le_div_iff₀ hθ).mpr
      have hd := (ξ.numberFieldNormalize hξ).log_norm_sub_le_localDist
        (η.numberFieldNormalize hη) ω (normalizedNormFamilyTensorEquiv ω y)
      erw [numberFieldNormalize_log_discrepancy_map] at hd
      simpa only [θ, mul_comm] using hd
    have hm := mul_le_mul_of_nonneg_left hbound hθ.le
    simpa only [mul_div_cancel₀ _ hθ.ne'] using hm

/-- Actual local distance integrability is reflected as well as preserved. -/
theorem numberFieldNormalize_localDist_integrable_iff :
    Integrable ((ξ.numberFieldNormalize hξ).localDist (η.numberFieldNormalize hη))
      (normalizedNumberFieldAdelicStructure K).v ↔
      Integrable (ξ.localDist η) (numberFieldAdelicStructure K).v := by
  have heq : (ξ.numberFieldNormalize hξ).localDist (η.numberFieldNormalize hη) =
      fun ω => numberFieldNormalizationExponent ω * ξ.localDist η ω.val := by
    funext ω
    exact ξ.numberFieldNormalize_localDist η hξ hη ω
  rw [heq]
  exact integrable_numberFieldNormalizationExponent_mul_iff (ξ.localDist η)

/-- Integrable global distance is preserved by the actual degree-weighted curve. -/
theorem numberFieldNormalize_integral_localDist
    (h : Integrable (ξ.localDist η) (numberFieldAdelicStructure K).v) :
    (∫ ω, (ξ.numberFieldNormalize hξ).localDist (η.numberFieldNormalize hη) ω
      ∂(normalizedNumberFieldAdelicStructure K).v) =
      ∫ ω, ξ.localDist η ω ∂(numberFieldAdelicStructure K).v := by
  have heq : (ξ.numberFieldNormalize hξ).localDist (η.numberFieldNormalize hη) =
      fun ω => numberFieldNormalizationExponent ω * ξ.localDist η ω.val := by
    funext ω
    exact ξ.numberFieldNormalize_localDist η hξ hη ω
  rw [heq]
  exact integral_numberFieldNormalizationExponent_mul (ξ.localDist η) h

/-- Extended nonnegative distance integrals agree even when they are infinite. -/
theorem numberFieldNormalize_lintegral_localDist :
    (∫⁻ ω, ENNReal.ofReal
      ((ξ.numberFieldNormalize hξ).localDist (η.numberFieldNormalize hη) ω)
      ∂(normalizedNumberFieldAdelicStructure K).v) =
      ∫⁻ ω, ENNReal.ofReal (ξ.localDist η ω) ∂(numberFieldAdelicStructure K).v := by
  calc
    _ = ∫⁻ ω : (normalizedNumberFieldAdelicStructure K).Ω,
        ENNReal.ofReal (numberFieldNormalizationExponent ω) *
          ENNReal.ofReal (ξ.localDist η ω.val)
        ∂(normalizedNumberFieldAdelicStructure K).v := by
      apply lintegral_congr
      intro ω
      erw [numberFieldNormalize_localDist,
        ENNReal.ofReal_mul (numberFieldNormalizationExponent_pos ω).le]
    _ = _ := lintegral_numberFieldNormalizationExponent_mul
      (fun ω => ENNReal.ofReal (ξ.localDist η ω))

end ArakelovGeometry.NormFamily
