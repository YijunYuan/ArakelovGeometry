/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HermitianSemistability
public import ArakelovGeometry.AdelicVectorBundle.LineVectorDegree
public import ArakelovGeometry.NumberTheory.NumberFieldPureFirstMinimum

/-! # Explicit ordinary minimum bounds on the pure number-field subclass -/

@[expose] public section

noncomputable section
open NumberField

namespace ArakelovGeometry.NumberFieldPureMinkowskiLevels

variable (K : Type*) [Field K] [NumberField K]

/-- The actual integer discriminant has absolute value at least one. -/
theorem log_abs_discriminant_nonneg : 0 ≤ Real.log |(NumberField.discr K : ℝ)| := by
  have hd : (1 : ℤ) ≤ |NumberField.discr K| := by
    have := abs_pos.mpr (NumberField.discr_ne_zero K)
    omega
  exact Real.log_nonneg (by exact_mod_cast hd)

/-- For rank at least two, the discriminant error is absorbed into an explicit
multiple of the logarithmic rank. -/
theorem discriminant_error_le_log_rank {n : ℕ} (hn : 2 ≤ n) :
    Real.log |(NumberField.discr K : ℝ)| / 2 ≤
      (Real.log |(NumberField.discr K : ℝ)| / (2 * Real.log 2)) * Real.log (n : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hc : 0 ≤ Real.log |(NumberField.discr K : ℝ)| / (2 * Real.log 2) :=
    div_nonneg (log_abs_discriminant_nonneg K) (by positivity)
  have he : (Real.log |(NumberField.discr K : ℝ)| / (2 * Real.log 2)) *
      Real.log 2 = Real.log |(NumberField.discr K : ℝ)| / 2 := by
    field_simp
  simpa only [he] using mul_le_mul_of_nonneg_left hlog hc

theorem error_le_level_mul_log {n : ℕ} (hn : 2 ≤ n) (A : ℝ) :
    A * Real.log (n : ℝ) + Real.log |(NumberField.discr K : ℝ)| / 2 ≤
      (A + Real.log |(NumberField.discr K : ℝ)| / (2 * Real.log 2)) *
        Real.log (n : ℝ) := by
  calc
    _ ≤ A * Real.log (n : ℝ) +
        (Real.log |(NumberField.discr K : ℝ)| / (2 * Real.log 2)) * Real.log (n : ℝ) :=
      add_le_add le_rfl (discriminant_error_le_log_rank K hn)
    _ = _ := by ring

/-- Both explicit pure-subclass constants are nonnegative in the original place masses. -/
theorem levels_nonneg :
    0 ≤ (Module.finrank ℚ K : ℝ) / 2 +
      Real.log |(NumberField.discr K : ℝ)| / (2 * Real.log 2) ∧
    0 ≤ (Module.finrank ℚ K : ℝ) +
      Real.log |(NumberField.discr K : ℝ)| / (2 * Real.log 2) := by
  have hd := log_abs_discriminant_nonneg K
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor <;> positivity

open AdelicStructure
attribute [local instance] normalizedNumberFieldAdelicStructure_isProper

local instance pureLevelsDiscreteMeasurable :
    DiscreteMeasurableSpace (normalizedNumberFieldAdelicStructure K).Ω :=
  inferInstanceAs
    (DiscreteMeasurableSpace {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})

variable {K} {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Every actual number-field line has its ordinary first minimum and both extremal
slopes equal to its actual determinant degree, with no purity hypothesis. -/
theorem rank_one_invariants
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hr : Module.finrank K E = 1) :
    V.maximalLogarithmicMinimum =
        (V.degree (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions : EReal) ∧
      V.maximalSlope (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions =
        (V.degree (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions : EReal) ∧
      V.minimalSlope (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions =
        (V.degree (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions : EReal) := by
  let hS : DiscreteMeasurableSpace (normalizedNumberFieldAdelicStructure K).Ω ∨
      (normalizedNumberFieldAdelicStructure K).HasCommonCountableDenseSubfield :=
    Or.inl inferInstance
  let hN := normalizedNumberFieldArchimedeanCompletions (K := K)
  have hline : V.IsLine := hr
  have hp : 0 < Module.finrank K E := by omega
  have hsemi := V.isMeanSlopeSemistable_of_finrank_eq_one hS hN hr
  have hmax := (V.isMeanSlopeSemistable_iff_maximalSlope_eq_slope hS hN hp).mp hsemi
  have hmin := (V.isMeanSlopeSemistable_iff_minimalSlope_eq_slope_of_isHermitian
    hS hN (hline.isHermitian hN) hp).mp hsemi
  rw [V.slope_eq_degree_of_finrank_one hS hN hr] at hmax hmin
  refine ⟨?_, hmax, hmin⟩
  rw [V.maximalLogarithmicMinimum_eq_lineDegree hline, V.degree_eq_lineDegree hS hN hline]

/-- The explicit ordinary Minkowski bound on the pure Hermitian subclass.
This does not assert the unrestricted number-field Minkowski property. -/
theorem hermitian_maximalSlope_sub_level_mul_log_le_firstMinimum
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hV : V.toNormFamily.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (hpure : V.toNormFamily.IsPureAtFinitePlaces) :
    V.maximalSlope (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions -
      ((((Module.finrank ℚ K : ℝ) / 2 +
          Real.log |(NumberField.discr K : ℝ)| / (2 * Real.log 2)) *
        Real.log (Module.finrank K E : ℝ) : ℝ) : EReal) ≤
          V.maximalLogarithmicMinimum := by
  by_cases hz : Module.finrank K E = 0
  · simp only [hz, Nat.cast_zero, Real.log_zero, mul_zero, EReal.coe_zero, sub_zero]
    rw [V.maximalSlope_eq_bot_of_finrank_eq_zero (Or.inl inferInstance)
      normalizedNumberFieldArchimedeanCompletions hz]
    exact bot_le
  have hn : 0 < Module.finrank K E := Nat.pos_of_ne_zero hz
  by_cases hr : Module.finrank K E = 1
  · obtain ⟨hfirst, hmax, _⟩ := rank_one_invariants V hr
    simp only [hr, Nat.cast_one, Real.log_one, mul_zero, EReal.coe_zero, sub_zero]
    exact hmax.trans hfirst.symm |>.le
  · have htwo : 2 ≤ Module.finrank K E := by omega
    have h := NumberFieldHermitianFirstMinimum.maximalSlope_sub_error_le_firstMinimum
      V hV hpure hn
    have hc := error_le_level_mul_log K htwo ((Module.finrank ℚ K : ℝ) / 2)
    exact (EReal.sub_le_sub le_rfl (EReal.coe_le_coe hc)).trans h

/-- The explicit ordinary Minkowski bound on the pure subclass with arbitrary infinite
norms; finite-place ultrametricity remains separate from value-group purity. -/
theorem maximalSlope_sub_level_mul_log_le_firstMinimum
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hU : V.toNormFamily.IsUltrametric) (hpure : V.toNormFamily.IsPureAtFinitePlaces) :
    V.maximalSlope (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions -
      ((((Module.finrank ℚ K : ℝ) +
          Real.log |(NumberField.discr K : ℝ)| / (2 * Real.log 2)) *
        Real.log (Module.finrank K E : ℝ) : ℝ) : EReal) ≤
          V.maximalLogarithmicMinimum := by
  by_cases hz : Module.finrank K E = 0
  · simp only [hz, Nat.cast_zero, Real.log_zero, mul_zero, EReal.coe_zero, sub_zero]
    rw [V.maximalSlope_eq_bot_of_finrank_eq_zero (Or.inl inferInstance)
      normalizedNumberFieldArchimedeanCompletions hz]
    exact bot_le
  have hn : 0 < Module.finrank K E := Nat.pos_of_ne_zero hz
  by_cases hr : Module.finrank K E = 1
  · obtain ⟨hfirst, hmax, _⟩ := rank_one_invariants V hr
    simp only [hr, Nat.cast_one, Real.log_one, mul_zero, EReal.coe_zero, sub_zero]
    exact hmax.trans hfirst.symm |>.le
  · have htwo : 2 ≤ Module.finrank K E := by omega
    have h := NumberFieldPureFirstMinimum.maximalSlope_sub_error_le_firstMinimum
      V hU hpure hn
    have hc := error_le_level_mul_log K htwo (Module.finrank ℚ K : ℝ)
    exact (EReal.sub_le_sub le_rfl (EReal.coe_le_coe hc)).trans h

end ArakelovGeometry.NumberFieldPureMinkowskiLevels
