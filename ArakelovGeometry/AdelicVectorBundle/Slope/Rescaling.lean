/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Rescaling
public import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.Basic

import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Extremal slopes under actual exponential rescaling

Source Lemma 4.3.36 follows from the rank-weighted determinant shift on every
actual subspace. The quotient infimum commutes with rescaling, giving the
same shift for the minimal slope. Finite translation preserves both infinite
zero-space conventions, and the numerical slopes depend only on the exponent's
almost-everywhere class.
-/

@[expose] public section

open MeasureTheory

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S) (φ : S.Ω → ℝ) (hm : Measurable φ) (hi : Integrable φ S.v)
  [hS : S.HasMeasurableBase]

/-- The actual quotient bundle commutes with exponential rescaling, using
the equality of the defining infima of completed lift norms. -/
theorem quotient_scaleExp (U : Submodule K V) :
    (V.scaleExp φ hm hi).quotientOfMeasurableBase U =
      (V.quotientOfMeasurableBase U).scaleExp φ hm hi := by
  apply AdelicVectorBundle.ext
    (hξ := ((V.scaleExp φ hm hi).quotientOfMeasurableBase U).toIsAdelic)
    (hη := ((V.quotientOfMeasurableBase U).scaleExp φ hm hi).toIsAdelic)
  exact V.toNormFamily.scale_quotient (fun ω ↦ Real.exp (φ ω))
    (fun _ ↦ Real.exp_pos _) U

variable [S.IsProper]
  [hN : S.IsArchimedeanNormalized]

/-- Positive-rank mean slopes shift by the integral of the exponent.
The rank guard excludes the zero bundle's mean convention. -/
theorem slope_scaleExp (hE : 0 < Module.finrank K V) :
    (V.scaleExp φ hm hi).slope = V.slope - ∫ ω, φ ω ∂S.v := by
  have he : (Module.finrank K V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hE)
  unfold slope
  rw [V.degree_scaleExp φ hm hi]
  field_simp

/-- Every nonzero actual subspace has the same slope shift. -/
theorem slope_restrict_scaleExp (U : Submodule K V) (hU : 0 < Module.finrank K U) :
    ((V.scaleExp φ hm hi).restrictOfMeasurableBase U).slope =
      (V.restrictOfMeasurableBase U).slope - ∫ ω, φ ω ∂S.v := by
  rw [V.restrict_scaleExp φ hm hi U]
  exact slope_scaleExp _ φ hm hi hU

/-- Source Lemma 4.3.36(1), including the negative-infinite rank-zero convention. -/
theorem maximalSlope_scaleExp :
    (V.scaleExp φ hm hi).maximalSlope =
      V.maximalSlope - (∫ ω, φ ω ∂S.v : ℝ) := by
  apply le_antisymm
  · apply (V.scaleExp φ hm hi).maximalSlope_le
    intro U hU
    rw [V.slope_restrict_scaleExp φ hm hi U hU, EReal.coe_sub]
    exact EReal.sub_le_sub (V.slope_restrict_le_maximalSlope U hU) le_rfl
  · apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))).mpr
    apply V.maximalSlope_le
    intro U hU
    have h := (V.scaleExp φ hm hi).slope_restrict_le_maximalSlope U hU
    rw [V.slope_restrict_scaleExp φ hm hi U hU, EReal.coe_sub] at h
    exact (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))).mp h

/-- Actual quotient norms commute with rescaling, so the quotient-infimum
definition gives the same finite translation of the minimal slope in every rank. -/
theorem minimalSlope_scaleExp :
    (V.scaleExp φ hm hi).minimalSlope =
      V.minimalSlope - (∫ ω, φ ω ∂S.v : ℝ) := by
  apply le_antisymm
  · apply (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))).mpr
    apply V.le_minimalSlope
    intro U hU
    have h := (V.scaleExp φ hm hi).minimalSlope_le_maximalSlope_quotient U hU
    rw [V.quotient_scaleExp φ hm hi U, maximalSlope_scaleExp] at h
    exact (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))).mp h
  · apply (V.scaleExp φ hm hi).le_minimalSlope
    intro U hU
    rw [V.quotient_scaleExp φ hm hi U, maximalSlope_scaleExp]
    exact EReal.sub_le_sub (V.minimalSlope_le_maximalSlope_quotient U hU) le_rfl

/-- Combining the actual extremal-slope shift with source Lemma 4.3.36(2)
detects exactly when an exponential rescaling has vanishing positive degree. -/
theorem positiveDegree_scaleExp_eq_zero_iff :
    (V.scaleExp φ hm hi).positiveDegree = 0 ↔
      V.maximalSlope ≤ (∫ ω, φ ω ∂S.v : ℝ) := by
  rw [(V.scaleExp φ hm hi).positiveDegree_eq_zero_iff_maximalSlope_nonpos,
    V.maximalSlope_scaleExp φ hm hi]
  simpa only [zero_add] using
    (EReal.sub_le_iff_le_add (a := V.maximalSlope)
      (b := (∫ ω, φ ω ∂S.v : ℝ)) (c := 0)
      (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)))

/-- Changing the measurable integrable exponent on a null set preserves the
actual rescaled maximal slope. -/
theorem maximalSlope_scaleExp_eq_of_aeEq (ψ : S.Ω → ℝ)
    (hmψ : Measurable ψ) (hiψ : Integrable ψ S.v) (hφψ : φ =ᵐ[S.v] ψ) :
    (V.scaleExp φ hm hi).maximalSlope =
      (V.scaleExp ψ hmψ hiψ).maximalSlope := by
  rw [V.maximalSlope_scaleExp φ hm hi, V.maximalSlope_scaleExp ψ hmψ hiψ,
    integral_congr_ae hφψ]

/-- The quotient-infimum minimal slope also depends only on the integrable
exponent's almost-everywhere class. -/
theorem minimalSlope_scaleExp_eq_of_aeEq (ψ : S.Ω → ℝ)
    (hmψ : Measurable ψ) (hiψ : Integrable ψ S.v) (hφψ : φ =ᵐ[S.v] ψ) :
    (V.scaleExp φ hm hi).minimalSlope =
      (V.scaleExp ψ hmψ hiψ).minimalSlope := by
  rw [V.minimalSlope_scaleExp φ hm hi, V.minimalSlope_scaleExp ψ hmψ hiψ,
    integral_congr_ae hφψ]

end

end ArakelovGeometry.AdelicVectorBundle
