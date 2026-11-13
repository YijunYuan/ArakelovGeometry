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
# Positive degree under integrable rescaling

Every bound consumes the exact degree shift on all actual restrictions.
Finite real positive degrees are produced before subtraction is used.
-/

@[expose] public section

open MeasureTheory

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

private theorem abs_rank_mul_le (U : Submodule K E) (t : ℝ) :
    |(Module.finrank K U : ℝ) * t| ≤ (Module.finrank K E : ℝ) * |t| := by
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr U.finrank_le) (abs_nonneg t)

/-- The upper positive-degree shift is bounded by ambient rank times the
absolute integral, uniformly over all actual subspaces. -/
theorem positiveDegree_scaleExp_le (V : AdelicVectorBundle S) (φ : S.Ω → ℝ)
    (hm : Measurable φ) (hi : Integrable φ S.v)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (V.scaleExp φ hm hi).positiveDegree ≤ V.positiveDegree +
      (((Module.finrank K V : ℝ) * |∫ ω, φ ω ∂S.v| : ℝ) : EReal) := by
  obtain ⟨c, hc⟩ := V.exists_positiveDegree_eq_coe
  rw [hc, ← EReal.coe_add]
  apply positiveDegree_le _
  intro U
  apply EReal.coe_le_coe_iff.mpr
  have hb := V.degree_restrict_le_positiveDegree U
  rw [hc] at hb
  have hb' := EReal.coe_le_coe_iff.mp hb
  have he := V.degree_restrict_scaleExp φ hm hi U
  have hneg := (neg_le_abs ((Module.finrank K U : ℝ) * (∫ ω, φ ω ∂S.v))).trans
    (abs_rank_mul_le U (∫ ω, φ ω ∂S.v))
  linarith

/-- The reverse bound also comes directly from each actual restricted shift,
without assuming that a supremum is attained. -/
theorem positiveDegree_le_scaleExp_add (V : AdelicVectorBundle S) (φ : S.Ω → ℝ)
    (hm : Measurable φ) (hi : Integrable φ S.v)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    V.positiveDegree ≤ (V.scaleExp φ hm hi).positiveDegree +
      (((Module.finrank K V : ℝ) * |∫ ω, φ ω ∂S.v| : ℝ) : EReal) := by
  obtain ⟨c, hc⟩ := (V.scaleExp φ hm hi).exists_positiveDegree_eq_coe
  rw [hc, ← EReal.coe_add]
  apply V.positiveDegree_le
  intro U
  apply EReal.coe_le_coe_iff.mpr
  have hb := (V.scaleExp φ hm hi).degree_restrict_le_positiveDegree U
  rw [hc] at hb
  have hb' := EReal.coe_le_coe_iff.mp hb
  have he := V.degree_restrict_scaleExp φ hm hi U
  have hpos := (le_abs_self ((Module.finrank K U : ℝ) * (∫ ω, φ ω ∂S.v))).trans
    (abs_rank_mul_le U (∫ ω, φ ω ∂S.v))
  linarith

/-- Source's lower rescaling estimate, after both positive degrees have
proved finite real representatives. -/
theorem positiveDegree_sub_le_scaleExp (V : AdelicVectorBundle S) (φ : S.Ω → ℝ)
    (hm : Measurable φ) (hi : Integrable φ S.v)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    V.positiveDegree -
      (((Module.finrank K V : ℝ) * |∫ ω, φ ω ∂S.v| : ℝ) : EReal) ≤
        (V.scaleExp φ hm hi).positiveDegree := by
  obtain ⟨c, hc⟩ := V.exists_positiveDegree_eq_coe
  obtain ⟨d, hd⟩ := (V.scaleExp φ hm hi).exists_positiveDegree_eq_coe
  have h := V.positiveDegree_le_scaleExp_add φ hm hi
  rw [hc, hd, ← EReal.coe_add] at h
  rw [hc, hd, ← EReal.coe_sub]
  apply EReal.coe_le_coe_iff.mpr
  have h' := EReal.coe_le_coe_iff.mp h
  linarith

/-- A nonnegative integral decreases every degree under `exp φ`, hence its
positive degree. The exponent need not be pointwise nonnegative. -/
theorem positiveDegree_scaleExp_le_of_integral_nonneg (V : AdelicVectorBundle S)
    (φ : S.Ω → ℝ) (hm : Measurable φ) (hi : Integrable φ S.v)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (ht : 0 ≤ ∫ ω, φ ω ∂S.v) :
    (V.scaleExp φ hm hi).positiveDegree ≤ V.positiveDegree := by
  apply positiveDegree_le _
  intro U
  have he := V.degree_restrict_scaleExp φ hm hi U
  have hb : ((V.scaleExp φ hm hi).restrictOfMeasurableBase U).degree ≤
      (V.restrictOfMeasurableBase U).degree := by
    rw [he]
    exact sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) ht)
  exact (EReal.coe_le_coe_iff.mpr hb).trans (V.degree_restrict_le_positiveDegree U)

/-- A nonpositive integral increases every actual restricted degree. -/
theorem positiveDegree_le_scaleExp_of_integral_nonpos (V : AdelicVectorBundle S)
    (φ : S.Ω → ℝ) (hm : Measurable φ) (hi : Integrable φ S.v)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (ht : (∫ ω, φ ω ∂S.v) ≤ 0) :
    V.positiveDegree ≤ (V.scaleExp φ hm hi).positiveDegree := by
  apply V.positiveDegree_le
  intro U
  have he := V.degree_restrict_scaleExp φ hm hi U
  have hb : (V.restrictOfMeasurableBase U).degree ≤
      ((V.scaleExp φ hm hi).restrictOfMeasurableBase U).degree := by
    rw [he]
    have hmul := mul_nonpos_of_nonneg_of_nonpos
      (Nat.cast_nonneg (Module.finrank K U) : (0 : ℝ) ≤ Module.finrank K U) ht
    linarith
  exact (EReal.coe_le_coe_iff.mpr hb).trans
    ((V.scaleExp φ hm hi).degree_restrict_le_positiveDegree U)

/-- An integral-zero rescaling preserves positive degree even though the
individual completed norm fibres can change. -/
theorem positiveDegree_scaleExp_eq_of_integral_eq_zero (V : AdelicVectorBundle S)
    (φ : S.Ω → ℝ) (hm : Measurable φ) (hi : Integrable φ S.v)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (ht : (∫ ω, φ ω ∂S.v) = 0) :
    (V.scaleExp φ hm hi).positiveDegree = V.positiveDegree :=
  le_antisymm (V.positiveDegree_scaleExp_le_of_integral_nonneg φ hm hi ht.ge)
    (V.positiveDegree_le_scaleExp_of_integral_nonpos φ hm hi ht.le)

/-- The numerical positive degree is independent of the choice of measurable
integrable representative of an almost-everywhere class. -/
theorem positiveDegree_scaleExp_eq_of_ae_eq (V : AdelicVectorBundle S)
    (φ ψ : S.Ω → ℝ) (hmφ : Measurable φ) (hiφ : Integrable φ S.v)
    (hmψ : Measurable ψ) (hiψ : Integrable ψ S.v)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (he : φ =ᵐ[S.v] ψ) :
    (V.scaleExp φ hmφ hiφ).positiveDegree =
      (V.scaleExp ψ hmψ hiψ).positiveDegree := by
  unfold positiveDegree
  apply iSup_congr
  intro U
  rw [V.degree_restrict_scaleExp φ hmφ hiφ U,
    V.degree_restrict_scaleExp ψ hmψ hiψ U, integral_congr_ae he]

end

end ArakelovGeometry.AdelicVectorBundle
