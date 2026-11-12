/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Vector
public import ArakelovGeometry.MeasureTheory.Integral.UpperEnvelope
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

import ArakelovGeometry.AdelicVectorBundle.NormFamily.Rational
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Extended vector degrees for completed seminorm families

Source Remark 4.3.3 uses the genuine extended logarithm with `log 0 = ⊥`.
The raw extended degree is defined by the actual upper-envelope integral.
An integrable upper envelope for the logarithm places it in `(⊥, ⊤]`, the
source domain; this condition is proved to be invariant under nonzero scalars.
Measurability is proved from the source measurable evaluation hypothesis.

Appendix A.4.1 defines its envelope integral only for real-valued functions.
Here its same real-integrable-majorant formula is explicitly extended to the
extended logarithm. This specifies a convention left implicit in Remark 4.3.3.
It is not an identification with the ordinary extended Lebesgue integral on
arbitrary measures: even the source upper integral of the real constant `-1`
is zero on an infinite-mass singleton, where its ordinary integral is `⊥`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped TensorProduct

namespace ArakelovGeometry

universe u v w

variable {K : Type u} [Field K]

/-- A family of actual seminorms on the completed fibres; no separation is imposed. -/
abbrev SeminormFamily (S : AdelicStructure.{u, v} K) (E : Type w)
    [AddCommGroup E] [Module K E] :=
  ∀ ω : S.Ω, Seminorm (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E)

namespace SeminormFamily

variable {S : AdelicStructure.{u, v} K} {E : Type w} [AddCommGroup E] [Module K E]

/-- The extended logarithmic rational evaluation, with value `⊥` at zero. -/
noncomputable def logNorm (p : SeminormFamily S E) (x : E) (ω : S.Ω) : EReal :=
  ENNReal.log (ENNReal.ofReal (p ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x)))

/-- The raw extended vector degree. The integrable-upper-envelope theorem below
identifies its source domain by excluding `⊥`; no finite value is silently substituted. -/
noncomputable def vectorDegree (p : SeminormFamily S E) (x : E) : EReal :=
  -upperERealEnvelopeIntegral (p.logNorm x) S.v

/-- Rational homogeneity holds for seminorms without a nonvanishing-vector premise. -/
theorem norm_rational_smul (p : SeminormFamily S E) (ω : S.Ω) (a : K) (x : E) :
    p ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (a • x)) =
      S.ϕ ω a * p ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) := by
  have ht : algebraMap K (S.ϕ ω).Completion a •
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) =
        (1 : (S.ϕ ω).Completion) ⊗ₜ[K] (a • x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [← ht, map_smul_eq_mul, S.norm_algebraMap_eq_absValue]

/-- Extended logarithmic homogeneity remains valid when the seminorm vanishes. -/
theorem logNorm_smul (p : SeminormFamily S E) {a : K} (ha : a ≠ 0) (x : E) (ω : S.Ω) :
    p.logNorm (a • x) ω = (Real.log (S.ϕ ω a) : EReal) + p.logNorm x ω := by
  unfold logNorm
  rw [norm_rational_smul, ENNReal.ofReal_mul ((S.ϕ ω).nonneg a), ENNReal.log_mul_add,
    ENNReal.log_ofReal_of_pos ((S.ϕ ω).pos ha)]

/-- The zero-vector logarithm is genuinely negative infinity. -/
@[simp]
theorem logNorm_zero (p : SeminormFamily S E) (ω : S.Ω) : p.logNorm 0 ω = ⊥ := by
  simp only [logNorm, TensorProduct.tmul_zero, map_zero, ENNReal.ofReal_zero, ENNReal.log_zero]

/-- Measurable seminorm evaluations give measurable extended logarithms. -/
theorem measurable_logNorm (p : SeminormFamily S E) (x : E)
    (hm : Measurable (fun ω ↦ p ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x))) :
    Measurable (p.logNorm x) := hm.ennreal_ofReal.ennreal_log

/-- The extended logarithm is bounded by the unlogged nonnegative evaluation. -/
theorem logNorm_le_norm (p : SeminormFamily S E) (x : E) (ω : S.Ω) :
    p.logNorm x ω ≤ (p ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) : ℝ) := by
  by_cases h : p ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) = 0
  · simp only [logNorm, h, ENNReal.ofReal_zero, ENNReal.log_zero, bot_le]
  · rw [logNorm, ENNReal.log_ofReal_of_pos (lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm h))]
    exact EReal.coe_le_coe_iff.mpr (Real.log_le_self (apply_nonneg _ _))

/-- The source's upper domination of an unlogged evaluation is a sufficient condition
for an integrable upper envelope of its extended logarithm. -/
theorem exists_logNorm_upperBound_of_norm (p : SeminormFamily S E) (x : E)
    (h : HasIntegrableUpperBound (fun ω ↦ p ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x)) S.v) :
    ∃ A : S.Ω → ℝ, Integrable A S.v ∧ ∀ᵐ ω ∂S.v, p.logNorm x ω ≤ (A ω : EReal) := by
  obtain ⟨A, hA, hpA⟩ := h
  exact ⟨A, hA, hpA.mono fun ω hω ↦
    (p.logNorm_le_norm x ω).trans (EReal.coe_le_coe_iff.mpr hω)⟩

/-- On the source upper-envelope domain the degree belongs to `(⊥, ⊤]`. -/
theorem bot_lt_vectorDegree (p : SeminormFamily S E) (x : E)
    (h : ∃ A : S.Ω → ℝ, Integrable A S.v ∧
      ∀ᵐ ω ∂S.v, p.logNorm x ω ≤ (A ω : EReal)) :
    ⊥ < p.vectorDegree x := by
  obtain ⟨A, hA, hpA⟩ := h
  have ht := upperERealEnvelopeIntegral_lt_top hA hpA
  simpa only [EReal.neg_top, vectorDegree] using EReal.neg_lt_neg_iff.mpr ht

/-- Nonzero scalar multiplication preserves the actual logarithmic upper-envelope domain. -/
theorem exists_logNorm_upperBound_smul (p : SeminormFamily S E) {a : K} (ha : a ≠ 0) (x : E)
    (h : ∃ A : S.Ω → ℝ, Integrable A S.v ∧
      ∀ᵐ ω ∂S.v, p.logNorm x ω ≤ (A ω : EReal)) :
    ∃ B : S.Ω → ℝ, Integrable B S.v ∧
      ∀ᵐ ω ∂S.v, p.logNorm (a • x) ω ≤ (B ω : EReal) := by
  obtain ⟨A, hA, hpA⟩ := h
  refine ⟨fun ω ↦ Real.log (S.ϕ ω a) + A ω, (S.integrable_log a ha).add hA, ?_⟩
  filter_upwards [hpA] with ω hω
  rw [p.logNorm_smul ha, EReal.coe_add]
  exact add_le_add le_rfl hω

/-- The exact degree transformation law before the product formula. -/
theorem vectorDegree_smul (p : SeminormFamily S E) {a : K} (ha : a ≠ 0) (x : E) :
    p.vectorDegree (a • x) =
      -(upperERealEnvelopeIntegral (p.logNorm x) S.v + (∫ ω, Real.log (S.ϕ ω a) ∂S.v : ℝ)) := by
  unfold vectorDegree
  have he : p.logNorm (a • x) = fun ω ↦ p.logNorm x ω + (Real.log (S.ϕ ω a) : EReal) := by
    funext ω
    rw [p.logNorm_smul ha, add_comm]
  rw [he, upperERealEnvelopeIntegral_add_integrable _ (S.integrable_log a ha)]

/-- The product formula makes the extended degree invariant, including value `⊤`. -/
theorem vectorDegree_smul_of_proper [S.IsProper] (p : SeminormFamily S E)
    {a : K} (ha : a ≠ 0) (x : E) : p.vectorDegree (a • x) = p.vectorDegree x := by
  rw [vectorDegree_smul p ha, AdelicStructure.IsProper.product_formula a ha,
    EReal.coe_zero, add_zero]
  rfl

/-- With zero measure every envelope degree is zero, even for vanishing seminorms. -/
theorem vectorDegree_of_measure_eq_zero (p : SeminormFamily S E) (x : E) (hμ : S.v = 0) :
    p.vectorDegree x = 0 := by
  unfold vectorDegree
  rw [hμ]
  have hi : upperERealEnvelopeIntegral (p.logNorm x) 0 = 0 := by
    apply le_antisymm
    · have h : upperERealEnvelopeIntegral (p.logNorm x) 0 ≤ (∫ ω, (0 : ℝ) ∂(0 : Measure S.Ω)) :=
        sInf_le ⟨0, integrable_zero _ _ _, by simp, rfl⟩
      simpa only [integral_zero_measure, EReal.coe_zero] using h
    · apply le_sInf
      rintro r ⟨A, _, _, rfl⟩
      simp only [integral_zero_measure, EReal.coe_zero, le_refl]
  rw [hi, neg_zero]

/-- Under positive finite total measure, an almost-everywhere vanishing evaluation
has degree `⊤` under the actual envelope convention. -/
theorem vectorDegree_eq_top_of_norm_ae_zero [IsFiniteMeasure S.v]
    (p : SeminormFamily S E) (x : E) (hμ : 0 < S.v.real Set.univ)
    (hx : ∀ᵐ ω ∂S.v, p ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) = 0) :
    p.vectorDegree x = ⊤ := by
  have hi : upperERealEnvelopeIntegral (p.logNorm x) S.v = ⊥ := by
    apply le_antisymm _ bot_le
    apply EReal.le_of_forall_lt_iff_le.mp
    intro r _
    have h : upperERealEnvelopeIntegral (p.logNorm x) S.v ≤
        (∫ _ : S.Ω, r / S.v.real Set.univ ∂S.v : ℝ) := by
      apply sInf_le
      refine ⟨fun _ ↦ r / S.v.real Set.univ, integrable_const _, ?_, rfl⟩
      filter_upwards [hx] with ω hω
      simp only [logNorm, hω, ENNReal.ofReal_zero, ENNReal.log_zero, bot_le]
    simpa only [integral_const, smul_eq_mul, mul_div_cancel₀ _ hμ.ne'] using h
  rw [vectorDegree, hi, EReal.neg_bot]

end SeminormFamily

namespace NormFamily

variable {S : AdelicStructure.{u, v} K} {E : Type w}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

omit [FiniteDimensional K E] in
/-- On nonzero vectors of a norm family the extended logarithm is the finite real logarithm. -/
theorem seminorm_logNorm_eq (ξ : NormFamily S E) (s : {x : E // x ≠ 0}) (ω : S.Ω) :
    SeminormFamily.logNorm ξ.norm s.val ω = (ξ.logNorm s.val ω : EReal) :=
  ENNReal.log_ofReal_of_pos (ξ.norm_rational_pos ω s.property)

/-- The extended seminorm degree agrees with the actual L1 vector degree whenever
the norm family is dominated and measurable. -/
theorem seminorm_vectorDegree_eq (ξ : NormFamily S E) [hd : ξ.IsDominated] [hm : ξ.IsMeasurable]
    (s : {x : E // x ≠ 0}) :
    SeminormFamily.vectorDegree ξ.norm s.val = (ξ.vectorDegree s : EReal) := by
  unfold SeminormFamily.vectorDegree
  have he : SeminormFamily.logNorm ξ.norm s.val = fun ω ↦ (ξ.logNorm s.val ω : EReal) :=
    funext (ξ.seminorm_logNorm_eq s)
  rw [he]
  rw [upperERealEnvelopeIntegral_coe,
    upperEnvelopeIntegral_eq_integral (hd.integrable_logNorm hm _),
    vectorDegree_eq_neg_integral, EReal.coe_neg]

end NormFamily

end ArakelovGeometry
