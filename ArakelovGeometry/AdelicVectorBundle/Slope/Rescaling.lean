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

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S E) (φ : S.Ω → ℝ) (hm : Measurable φ) (hi : Integrable φ S.v)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)

/-- The actual quotient bundle commutes with exponential rescaling, using
the equality of the defining infima of completed lift norms. -/
theorem quotient_scaleExp (U : Submodule K E) :
    (V.scaleExp φ hm hi).quotientOfMeasurableBase U hS =
      (V.quotientOfMeasurableBase U hS).scaleExp φ hm hi := by
  apply AdelicVectorBundle.ext
  exact V.toNormFamily.scale_quotient (fun ω ↦ Real.exp (φ ω))
    (fun _ ↦ Real.exp_pos _) U

variable [S.IsProper]
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)

/-- Positive-rank mean slopes shift by the integral of the exponent.
The rank guard excludes the zero bundle's mean convention. -/
theorem slope_scaleExp (hE : 0 < Module.finrank K E) :
    (V.scaleExp φ hm hi).slope hS hN = V.slope hS hN - ∫ ω, φ ω ∂S.v := by
  have he : (Module.finrank K E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hE)
  unfold slope
  rw [V.degree_scaleExp φ hm hi hS hN]
  field_simp

/-- Every nonzero actual subspace has the same slope shift. -/
theorem slope_restrict_scaleExp (U : Submodule K E) (hU : 0 < Module.finrank K U) :
    ((V.scaleExp φ hm hi).restrictOfMeasurableBase U hS).slope hS hN =
      (V.restrictOfMeasurableBase U hS).slope hS hN - ∫ ω, φ ω ∂S.v := by
  rw [V.restrict_scaleExp φ hm hi hS U]
  exact slope_scaleExp _ φ hm hi hS hN hU

/-- Source Lemma 4.3.36(1), including the negative-infinite rank-zero convention. -/
theorem maximalSlope_scaleExp :
    (V.scaleExp φ hm hi).maximalSlope hS hN =
      V.maximalSlope hS hN - (∫ ω, φ ω ∂S.v : ℝ) := by
  apply le_antisymm
  · apply (V.scaleExp φ hm hi).maximalSlope_le hS hN
    intro U hU
    rw [V.slope_restrict_scaleExp φ hm hi hS hN U hU, EReal.coe_sub]
    exact EReal.sub_le_sub (V.slope_restrict_le_maximalSlope U hU hS hN) le_rfl
  · apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))).mpr
    apply V.maximalSlope_le hS hN
    intro U hU
    have h := (V.scaleExp φ hm hi).slope_restrict_le_maximalSlope U hU hS hN
    rw [V.slope_restrict_scaleExp φ hm hi hS hN U hU, EReal.coe_sub] at h
    exact (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))).mp h

/-- Actual quotient norms commute with rescaling, so the quotient-infimum
definition gives the same finite translation of the minimal slope in every rank. -/
theorem minimalSlope_scaleExp :
    (V.scaleExp φ hm hi).minimalSlope hS hN =
      V.minimalSlope hS hN - (∫ ω, φ ω ∂S.v : ℝ) := by
  apply le_antisymm
  · apply (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))).mpr
    apply V.le_minimalSlope hS hN
    intro U hU
    have h := (V.scaleExp φ hm hi).minimalSlope_le_maximalSlope_quotient U hU hS hN
    rw [V.quotient_scaleExp φ hm hi hS U, maximalSlope_scaleExp] at h
    exact (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))).mp h
  · apply (V.scaleExp φ hm hi).le_minimalSlope hS hN
    intro U hU
    rw [V.quotient_scaleExp φ hm hi hS U, maximalSlope_scaleExp]
    exact EReal.sub_le_sub (V.minimalSlope_le_maximalSlope_quotient U hU hS hN) le_rfl

/-- Combining the actual extremal-slope shift with source Lemma 4.3.36(2)
detects exactly when an exponential rescaling has vanishing positive degree. -/
theorem positiveDegree_scaleExp_eq_zero_iff :
    (V.scaleExp φ hm hi).positiveDegree hS hN = 0 ↔
      V.maximalSlope hS hN ≤ (∫ ω, φ ω ∂S.v : ℝ) := by
  rw [(V.scaleExp φ hm hi).positiveDegree_eq_zero_iff_maximalSlope_nonpos hS hN,
    V.maximalSlope_scaleExp φ hm hi hS hN]
  simpa only [zero_add] using
    (EReal.sub_le_iff_le_add (a := V.maximalSlope hS hN)
      (b := (∫ ω, φ ω ∂S.v : ℝ)) (c := 0)
      (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)))

/-- Changing the measurable integrable exponent on a null set preserves the
actual rescaled maximal slope. -/
theorem maximalSlope_scaleExp_eq_of_aeEq (ψ : S.Ω → ℝ)
    (hmψ : Measurable ψ) (hiψ : Integrable ψ S.v) (hφψ : φ =ᵐ[S.v] ψ) :
    (V.scaleExp φ hm hi).maximalSlope hS hN =
      (V.scaleExp ψ hmψ hiψ).maximalSlope hS hN := by
  rw [V.maximalSlope_scaleExp φ hm hi hS hN, V.maximalSlope_scaleExp ψ hmψ hiψ hS hN,
    integral_congr_ae hφψ]

/-- The quotient-infimum minimal slope also depends only on the integrable
exponent's almost-everywhere class. -/
theorem minimalSlope_scaleExp_eq_of_aeEq (ψ : S.Ω → ℝ)
    (hmψ : Measurable ψ) (hiψ : Integrable ψ S.v) (hφψ : φ =ᵐ[S.v] ψ) :
    (V.scaleExp φ hm hi).minimalSlope hS hN =
      (V.scaleExp ψ hmψ hiψ).minimalSlope hS hN := by
  rw [V.minimalSlope_scaleExp φ hm hi hS hN, V.minimalSlope_scaleExp ψ hmψ hiψ hS hN,
    integral_congr_ae hφψ]

end

end ArakelovGeometry.AdelicVectorBundle
