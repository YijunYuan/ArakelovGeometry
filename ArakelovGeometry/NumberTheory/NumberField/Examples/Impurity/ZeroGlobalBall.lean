/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Rescaling
public import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.Basic
public import ArakelovGeometry.NumberTheory.NumberField.Lattice.UnitBall.Global

import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
import ArakelovGeometry.NumberTheory.NumberField.Lattice.Coherence.Criteria

/-!
# A dominated actual number-field line with zero global integral ball

A positive integrable perturbation at every finite place preserves adelicity
and excludes every nonzero rational scalar from the literal global ball.
-/

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal
noncomputable section
namespace ArakelovGeometry.NumberFieldZeroGlobalBall

open AdelicStructure ActualPrimeIndexing

variable {K : Type*} [Field K] [NumberField K]

local instance : Encodable (normalizedNumberFieldAdelicStructure K).Ω :=
  Encodable.ofCountable _

/-- Positive geometric decay divided by a finite singleton mass plus one. -/
def exponent (ω : (normalizedNumberFieldAdelicStructure K).Ω) : ℝ := by
  classical
  exact if ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin then
    (1 / 2 : ℝ) ^ Encodable.encode ω /
      (((normalizedNumberFieldAdelicStructure K).v {ω}).toReal + 1)
  else 0

theorem exponent_nonneg (ω : (normalizedNumberFieldAdelicStructure K).Ω) :
    0 ≤ exponent ω := by
  unfold exponent
  split_ifs <;> positivity

theorem exponent_pos_of_finite (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) : 0 < exponent ω := by
  rw [exponent, ite_eq_left hω]
  positivity

theorem exponent_eq_zero_of_infinite (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωinf) : exponent ω = 0 := by
  have hn : ω ∉ (normalizedNumberFieldAdelicStructure K).Ωfin := hω
  rw [exponent, ite_eq_right hn]

theorem exponent_integrable :
    Integrable (exponent (K := K)) (normalizedNumberFieldAdelicStructure K).v := by
  let μ := (normalizedNumberFieldAdelicStructure K).v
  change Integrable (exponent (K := K)) μ
  rw [← Measure.sum_smul_dirac μ]
  apply integrable_sum_dirac (x := id)
  · intro ω
    change (normalizedNumberFieldAdelicStructure K).v {ω} ≠ ∞
    exact (lt_of_eq_of_lt
      (normalizedNumberFieldAdelicStructure_v_singleton ω) (by simp)).ne
  · apply Summable.of_nonneg_of_le
      (f := fun ω : (normalizedNumberFieldAdelicStructure K).Ω =>
        (1 / 2 : ℝ) ^ Encodable.encode ω)
    · intro ω
      positivity
    · intro ω
      simp only [id_eq]
      rw [Real.norm_eq_abs, abs_of_nonneg (exponent_nonneg ω)]
      unfold exponent
      split_ifs
      · rw [← mul_div_assoc]
        change (μ {ω}).toReal * (1 / 2 : ℝ) ^ Encodable.encode ω /
          ((μ {ω}).toReal + 1) ≤ (1 / 2 : ℝ) ^ Encodable.encode ω
        apply (div_le_iff₀ (by positivity)).mpr
        have hm : 0 ≤ (μ {ω}).toReal := ENNReal.toReal_nonneg
        have ht : 0 ≤ (1 / 2 : ℝ) ^ Encodable.encode ω := by positivity
        nlinarith
      · simp only [mul_zero]
        positivity
    · exact summable_geometric_two_encode

/-- The canonical scalar bundle rescaled by this produced integrable function. -/
abbrev bundle (K : Type*) [Field K] [NumberField K] :
    AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) :=
  (AdelicVectorBundle.scalarLine (normalizedNumberFieldAdelicStructure K)).scaleExp
    exponent (Measurable.of_discrete) exponent_integrable

theorem norm_rational (ω : (normalizedNumberFieldAdelicStructure K).Ω) (a : K) :
    (bundle K).norm ω (1 ⊗ₜ[K] a) =
      Real.exp (exponent ω) * (normalizedNumberFieldAdelicStructure K).ϕ ω a := by
  change ((AdelicVectorBundle.scalarLine
    (normalizedNumberFieldAdelicStructure K)).toNormFamily.scale
    (fun ω => Real.exp (exponent ω)) (fun _ => Real.exp_pos _)).norm ω (1 ⊗ₜ[K] a) = _
  rw [NormFamily.scale_norm, AdelicVectorBundle.scalarLine_norm_rational]

theorem isUltrametric : (bundle K).toNormFamily.IsUltrametric := by
  change ((AdelicVectorBundle.scalarLine
    (normalizedNumberFieldAdelicStructure K)).toNormFamily.scale
    (fun ω => Real.exp (exponent ω)) (fun _ => Real.exp_pos _)).IsUltrametric
  apply NormFamily.IsUltrametric.scale
  constructor
  intro ω hω x y
  have h := NormFamily.ofBasisMixed_isUltrametric
    (S := normalizedNumberFieldAdelicStructure K) (Module.Basis.singleton (Fin 1) K) ω hω x y
  simpa only [AdelicVectorBundle.scalarLine_toNormFamily,
    NormFamily.ofBasisMixed_norm_of_finite _ ω hω] using h

/-- Every nonzero scalar has an unchanged absolute value at some actual finite prime. -/
theorem exists_finite_norm_gt_one {a : K} (ha : a ≠ 0) :
    ∃ ω : (normalizedNumberFieldAdelicStructure K).Ω,
      ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin ∧
        1 < (bundle K).norm ω (1 ⊗ₜ[K] a) := by
  classical
  obtain ⟨p, hp⟩ := (FiniteValuation.finite_valuation_ne_one (R := 𝓞 K) ha).exists_notMem
  have hp1 : p.valuation K a = 1 := by simpa using hp
  have hv : (normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p) a = 1 := by
    apply Real.eq_one_of_pos_of_log_eq_zero ((normalizedPlaceValue _).pos ha)
    have hlog := normalizedPrime_log_value p ha
    rw [hp1, WithZero.log_one, Int.cast_zero, mul_zero] at hlog
    exact hlog
  refine ⟨normalizedPrimeParameter p, normalizedPrimeParameter_mem_fin p, ?_⟩
  rw [norm_rational, hv, mul_one]
  exact Real.one_lt_exp_iff.mpr (exponent_pos_of_finite _ (normalizedPrimeParameter_mem_fin p))

/-- The produced dominated line has the literal zero global ball. -/
theorem globalUnitBall_eq_singleton_zero :
    (bundle K).toNormFamily.globalUnitBall = {0} := by
  ext a
  constructor
  · intro ha
    by_contra ha0
    obtain ⟨ω, hω, hgt⟩ := exists_finite_norm_gt_one (a := a) ha0
    exact (not_lt_of_ge (ha ω hω)) hgt
  · rintro rfl ω _
    simp

theorem globalUnitBallModule_eq_bot :
    (bundle K).toNormFamily.globalUnitBallModule (hξ := isUltrametric) = ⊥ := by
  ext a
  change a ∈ (bundle K).toNormFamily.globalUnitBall ↔ a = 0
  rw [globalUnitBall_eq_singleton_zero]
  rfl

theorem not_coherent : ¬ (bundle K).toNormFamily.HasFiniteNormExceptions := by
  intro hc
  have h := (NormFamily.hasFiniteNormExceptions_iff_span_normalizedGlobalUnitBall_eq_top
    (bundle K).toNormFamily (hξ := isUltrametric)).mp hc
  change Submodule.span K (bundle K).toNormFamily.globalUnitBall = ⊤ at h
  rw [globalUnitBall_eq_singleton_zero, Submodule.span_singleton_eq_bot.mpr rfl] at h
  exact bot_ne_top h

end ArakelovGeometry.NumberFieldZeroGlobalBall
