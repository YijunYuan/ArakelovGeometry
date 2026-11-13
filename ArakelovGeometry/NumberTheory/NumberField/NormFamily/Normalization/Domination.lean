/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Basic
public import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Normalization.Basic

import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.PrimeIndexing

/-!
# Integrable envelopes under actual number-field normalization

Actual singleton weights cancel the local norm exponent. Transport integrable
upper and lower rational-vector envelopes without assuming norm domination.
-/

@[expose] public section

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped ENNReal TensorProduct NumberField

noncomputable section

namespace ArakelovGeometry.AdelicStructure

variable {K : Type*} [Field K] [NumberField K]

/-- The actual norm power at every nontrivial class, unchanged at infinite places. -/
def numberFieldNormalizationExponent
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) : ℝ := by
  classical
  exact if IsNonarchimedean (normalizedPlaceValue ω) then
    ((normalizedPlaceValue ω).localDegree ℚ : ℝ)⁻¹ else 1

/-- At every actual finite class the exponent is the inverse completed dimension. -/
theorem numberFieldNormalizationExponent_of_fin
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) :
    numberFieldNormalizationExponent ω = ((normalizedPlaceValue ω).localDegree ℚ : ℝ)⁻¹ := by
  change IsNonarchimedean (normalizedPlaceValue ω) at hω
  rw [numberFieldNormalizationExponent, ite_eq_left hω]

/-- At every actual infinite class the exponent is one. -/
theorem numberFieldNormalizationExponent_of_inf
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (hω : ω ∉ (normalizedNumberFieldAdelicStructure K).Ωfin) :
    numberFieldNormalizationExponent ω = 1 := by
  change ¬ IsNonarchimedean (normalizedPlaceValue ω) at hω
  rw [numberFieldNormalizationExponent, ite_eq_right hω]

/-- The true exponent is positive at every nontrivial class. -/
theorem numberFieldNormalizationExponent_pos
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) :
    0 < numberFieldNormalizationExponent ω := by
  by_cases hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin
  · exact (numberFieldNormalizationExponent_of_fin ω hω).symm ▸ normalizedFiniteExponent_pos ω hω
  · exact (numberFieldNormalizationExponent_of_inf ω hω).symm ▸ zero_lt_one

/-- Every nontrivial old ideal-norm curve atom has a positive real weight. -/
theorem placeWeight_toReal_pos_of_nontrivial
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) :
    0 < (placeWeight ω.val).toReal := by
  rcases place_trichotomy ω.val with ht | ⟨v, hv⟩ | ⟨w, hw⟩
  · exact False.elim (ω.property ht)
  · rw [hv, placeWeight_mk_finitePlace]
    norm_num
  · rw [hw, placeWeight_mk_infinitePlace, ENNReal.toReal_natCast]
    exact_mod_cast InfinitePlace.mult_pos (w := w)

/-- The actual completion-degree singleton mass cancels the true norm exponent. -/
theorem normalizationExponent_mul_singleton_toReal
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) :
    numberFieldNormalizationExponent ω *
      ((normalizedNumberFieldAdelicStructure K).v {ω}).toReal = (placeWeight ω.val).toReal := by
  by_cases hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin
  · obtain ⟨P, rfl⟩ := ActualPrimeIndexing.exists_normalizedPrimeParameter_eq ω hω
    have hd : (0 : ℝ) < ((normalizedPlaceValue
        (ActualPrimeIndexing.normalizedPrimeParameter P)).localDegree ℚ : ℝ) :=
      inv_pos.mp (normalizedFiniteExponent_pos _ hω)
    calc
      _ = ((normalizedPlaceValue (ActualPrimeIndexing.normalizedPrimeParameter P)).localDegree ℚ :
            ℝ)⁻¹ *
          ((normalizedPlaceValue (ActualPrimeIndexing.normalizedPrimeParameter P)).localDegree ℚ :
            ℝ) :=
        congrArg₂ (fun a b : ℝ => a * b)
          (numberFieldNormalizationExponent_of_fin _ hω)
          ((congrArg ENNReal.toReal (normalizedNumberFieldAdelicStructure_v_singleton _)).trans
            (ENNReal.toReal_natCast _))
      _ = 1 := inv_mul_cancel₀ hd.ne'
      _ = _ := by
        change 1 = (placeWeight (Quotient.mk' (FinitePlace.mk P).val)).toReal
        rw [placeWeight_mk_finitePlace]
        norm_num
  · rcases place_trichotomy ω.val with ht | ⟨v, hv⟩ | ⟨w, hw⟩
    · exact False.elim (ω.property ht)
    · have hb : IsNonarchimedean (placeRep ω.val) := by
        rw [hv, placeRep_mk_finitePlace]
        exact NumberField.finitePlace_isNonarchimedean v
      exact False.elim (hω
        ((NumberField.isNonarchimedean_congr (normalizedPlaceValue_isEquiv_placeRep ω)).mpr hb))
    · have he : ω = ⟨Quotient.mk' w.val, mk_infinitePlace_ne_trivialPlace w⟩ := Subtype.ext hw
      calc
        _ = ((normalizedNumberFieldAdelicStructure K).v {ω}).toReal := by
          rw [numberFieldNormalizationExponent_of_inf ω hω, one_mul]
        _ = (w.mult : ℝ) :=
          (congrArg (fun η => ((normalizedNumberFieldAdelicStructure K).v {η}).toReal) he).trans
            ((congrArg ENNReal.toReal
              (normalizedNumberFieldAdelicStructure_v_infinitePlace w)).trans
              (ENNReal.toReal_natCast _))
        _ = _ := by rw [hw, placeWeight_mk_infinitePlace, ENNReal.toReal_natCast]

/-- Every old integrable real envelope transports to an actual normalized integrable envelope. -/
theorem integrable_numberFieldNormalizationExponent_mul
    (f : (numberFieldAdelicStructure K).Ω → ℝ)
    (hf : Integrable f (numberFieldAdelicStructure K).v) :
    Integrable (fun ω : (normalizedNumberFieldAdelicStructure K).Ω =>
      numberFieldNormalizationExponent ω * f ω.val) (normalizedNumberFieldAdelicStructure K).v := by
  let oldMeasurable : MeasurableSpace (AbsoluteValue.Place K) := ⊤
  have hs : Summable (fun ω : AbsoluteValue.Place K =>
      (placeWeight ω).toReal * ‖f ω‖) :=
    (integrable_sum_dirac_iff (ι := AbsoluteValue.Place K)
      (X := AbsoluteValue.Place K) (E := ℝ) (x := id) (c := placeWeight)
      (f := f) placeWeight_ne_top).mp hf
  have hsub := hs.subtype (fun ω => ω ≠ AbsoluteValue.trivialPlace K)
  let μ := (normalizedNumberFieldAdelicStructure K).v
  change Integrable _ μ
  rw [← Measure.sum_smul_dirac μ]
  apply (integrable_sum_dirac_iff (x := id) (c := fun ω => μ {ω})
    (f := fun ω : (normalizedNumberFieldAdelicStructure K).Ω =>
      numberFieldNormalizationExponent ω * f ω.val) (fun ω => by
      change (normalizedNumberFieldAdelicStructure K).v {ω} ≠ ⊤
      intro htop
      exact ENNReal.natCast_ne_top _
        ((normalizedNumberFieldAdelicStructure_v_singleton ω).symm.trans htop))).mpr
  apply hsub.congr
  intro ω
  calc
    (placeWeight ω.val).toReal * ‖f ω.val‖ =
        (numberFieldNormalizationExponent ω * (μ {ω}).toReal) * ‖f ω.val‖ :=
      congrArg (fun r : ℝ => r * ‖f ω.val‖)
        (normalizationExponent_mul_singleton_toReal ω).symm
    _ = (μ {ω}).toReal * ‖numberFieldNormalizationExponent ω * f ω.val‖ := by
      erw [norm_mul, Real.norm_eq_abs (numberFieldNormalizationExponent ω),
        abs_of_pos (numberFieldNormalizationExponent_pos ω)]
      ring

/-- An old almost-everywhere statement holds at each actual nontrivial class. -/
theorem forall_nontrivial_of_numberField_ae
    (p : (numberFieldAdelicStructure K).Ω → Prop)
    (hp : ∀ᵐ ω ∂(numberFieldAdelicStructure K).v, p ω)
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) : p ω.val := by
  let oldCountable : Countable (numberFieldAdelicStructure K).Ω :=
    inferInstanceAs (Countable (AbsoluteValue.Place K))
  apply (ae_iff_of_countable.mp hp) ω.val
  let oldMeasurable : MeasurableSpace (AbsoluteValue.Place K) := ⊤
  change (Measure.sum fun τ : AbsoluteValue.Place K => placeWeight τ • Measure.dirac τ) {ω.val} ≠ 0
  rw [Measure.sum_smul_dirac_singleton]
  intro hzero
  have h := placeWeight_toReal_pos_of_nontrivial ω
  rw [hzero, ENNReal.toReal_zero] at h
  exact (lt_irrefl 0) h

end ArakelovGeometry.AdelicStructure

namespace ArakelovGeometry.NormFamily

open AdelicStructure

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [AddCommGroup E] [Module K E]

/-- The actual normalization scales every rational logarithmic norm, including at zero. -/
theorem numberFieldNormalize_logNorm
    (ξ : NormFamily (numberFieldAdelicStructure K) E) [hξ : ξ.IsUltrametricAtFinitePlaces] (x : E)
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) :
    (ξ.numberFieldNormalize).logNorm x ω =
      numberFieldNormalizationExponent ω * ξ.logNorm x ω.val := by
  by_cases hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin
  · have hd : (0 : ℝ) < ((normalizedPlaceValue ω).localDegree ℚ : ℝ) :=
      inv_pos.mp (normalizedFiniteExponent_pos ω hω)
    have h := ξ.numberFieldNormalize_weighted_log_norm_map_fin ω hω (1 ⊗ₜ[K] x)
    have ht := congrArg (fun z => ((normalizedPlaceValue ω).localDegree ℚ : ℝ) *
      Real.log ((ξ.numberFieldNormalize).norm ω z))
      (normalizedNormFamilyTensorEquiv_one_tmul ω x)
    have hw : ((normalizedPlaceValue ω).localDegree ℚ : ℝ) *
        (ξ.numberFieldNormalize).logNorm x ω = ξ.logNorm x ω.val := ht.symm.trans h
    calc
      _ = ((normalizedPlaceValue ω).localDegree ℚ : ℝ)⁻¹ *
          (((normalizedPlaceValue ω).localDegree ℚ : ℝ) *
            (ξ.numberFieldNormalize).logNorm x ω) := by
        erw [← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul]
      _ = ((normalizedPlaceValue ω).localDegree ℚ : ℝ)⁻¹ * ξ.logNorm x ω.val :=
        congrArg (fun r : ℝ => ((normalizedPlaceValue ω).localDegree ℚ : ℝ)⁻¹ * r) hw
      _ = _ := congrArg (fun r : ℝ => r * ξ.logNorm x ω.val)
        (numberFieldNormalizationExponent_of_fin ω hω).symm
  · calc
      _ = ξ.logNorm x ω.val :=
        congrArg Real.log (ξ.numberFieldNormalize_norm_tmul_inf ω hω x)
      _ = _ := by erw [numberFieldNormalizationExponent_of_inf ω hω, one_mul]

/-- Actual upper domination transports along the produced norm-family normalization. -/
theorem IsUpperDominated.numberFieldNormalize
    {ξ : NormFamily (numberFieldAdelicStructure K) E}
    (hupper : ξ.IsUpperDominated) (hξ : ξ.IsUltrametricAtFinitePlaces) :
    (ξ.numberFieldNormalize).IsUpperDominated := by
  constructor
  intro x hx
  obtain ⟨A, hA, hbound⟩ := hupper x hx
  refine ⟨fun ω => numberFieldNormalizationExponent ω * A ω.val,
    integrable_numberFieldNormalizationExponent_mul A hA, ?_⟩
  apply Eventually.of_forall
  intro ω
  exact (ξ.numberFieldNormalize_logNorm x ω).trans_le
    (mul_le_mul_of_nonneg_left
      (forall_nontrivial_of_numberField_ae _ hbound ω)
      (numberFieldNormalizationExponent_pos ω).le)

/-- Actual lower domination transports along the produced norm-family normalization. -/
theorem IsLowerDominated.numberFieldNormalize
    {ξ : NormFamily (numberFieldAdelicStructure K) E}
    (hlower : ξ.IsLowerDominated) (hξ : ξ.IsUltrametricAtFinitePlaces) :
    (ξ.numberFieldNormalize).IsLowerDominated := by
  constructor
  intro x hx
  obtain ⟨A, hA, hbound⟩ := hlower x hx
  refine ⟨fun ω => numberFieldNormalizationExponent ω * A ω.val,
    integrable_numberFieldNormalizationExponent_mul A hA, ?_⟩
  apply Eventually.of_forall
  intro ω
  exact (mul_le_mul_of_nonneg_left
      (forall_nontrivial_of_numberField_ae _ hbound ω)
      (numberFieldNormalizationExponent_pos ω).le).trans
    (ξ.numberFieldNormalize_logNorm x ω).symm.le

end ArakelovGeometry.NormFamily
