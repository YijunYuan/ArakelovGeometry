/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Rescaling
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
public import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.PrimeIndexing
public import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Normalization.Bundle
public import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Normalization.Domination
public import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Normalization.Hermitian
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum

import ArakelovGeometry.AdelicVectorBundle.Degree.LineVector
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Line
import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Normalization.Determinant

/-! # Rational examples of actual number-field normalization

An actual rational line rescaled at the prime two has determinant norm two and
Arakelov degree `-log 2` on both the original and normalized number-field curves.
The same completed-fibre transport is evaluated at arbitrary rank-two vectors
and at the rank-zero empty exterior wedge.
-/

@[expose] public section

open ArakelovGeometry ArakelovGeometry.NormFamily ArakelovGeometry.AdelicStructure
open ArakelovGeometry.AdelicVectorBundle ArakelovGeometry.ActualPrimeIndexing
open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField TensorProduct ENNReal

noncomputable section

namespace ArakelovGeometry.NumberFieldNormalizationExamples

abbrev OldS := numberFieldAdelicStructure ℚ
abbrev NewS := normalizedNumberFieldAdelicStructure ℚ
local instance oldPlaceMeasurable : MeasurableSpace (AbsoluteValue.Place ℚ) := ⊤
local instance oldPlaceDiscrete : DiscreteMeasurableSpace (AbsoluteValue.Place ℚ) :=
  ⟨fun _ => trivial⟩
local instance oldCurveDiscrete : DiscreteMeasurableSpace OldS.Ω :=
  inferInstanceAs (DiscreteMeasurableSpace (AbsoluteValue.Place ℚ))
local instance oldCurveSingleton : @MeasurableSingletonClass
    (AbsoluteValue.Place ℚ) OldS.A := ⟨fun _ => trivial⟩

def primeTwo : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨2, Nat.prime_two⟩
def ωTwo : {ω : AbsoluteValue.Place ℚ // ω ≠ AbsoluteValue.trivialPlace ℚ} :=
  normalizedPrimeParameter primeTwo
theorem ωTwo_fin : ωTwo ∈ NewS.Ωfin := normalizedPrimeParameter_mem_fin primeTwo

theorem old_prime_mass : OldS.v {ωTwo.val} = 1 := by
  change (Measure.sum fun ω => placeWeight ω • Measure.dirac ω) {ωTwo.val} = 1
  erw [Measure.sum_smul_dirac_singleton]
  exact placeWeight_mk_finitePlace (FinitePlace.mk primeTwo)

theorem rational_finite_exponent : numberFieldNormalizationExponent ωTwo = 1 := by
  have hp : (0 : ℝ) < ((normalizedPlaceValue ωTwo).localDegree ℚ : ℝ) :=
    inv_pos.mp (normalizedFiniteExponent_pos ωTwo ωTwo_fin)
  have hpn : 0 < (normalizedPlaceValue ωTwo).localDegree ℚ := by exact_mod_cast hp
  have hl := (normalizedPlaceValue ωTwo).finrank_completion_le ℚ
  change (normalizedPlaceValue ωTwo).localDegree ℚ ≤ Module.finrank ℚ ℚ at hl
  erw [Module.finrank_self] at hl
  have hd : (normalizedPlaceValue ωTwo).localDegree ℚ = 1 := by omega
  erw [numberFieldNormalizationExponent_of_fin ωTwo ωTwo_fin, hd]
  norm_num

def φ : AbsoluteValue.Place ℚ → ℝ := by
  classical
  exact ({ωTwo.val} : Set (AbsoluteValue.Place ℚ)).indicator (fun _ => Real.log 2)

theorem φ_measurable : Measurable φ := Measurable.of_discrete

theorem φ_integrable : Integrable φ OldS.v := by
  classical
  exact (integrableOn_const (μ := OldS.v) (C := Real.log 2)
    (s := {ωTwo.val}) (old_prime_mass ▸ ENNReal.one_ne_top)).integrable_indicator
      (measurableSet_singleton _)

theorem φ_integral : (∫ ω, φ ω ∂OldS.v) = Real.log 2 := by
  classical
  erw [φ, integral_indicator_const _ (measurableSet_singleton _)]
  simp only [Measure.real]
  erw [old_prime_mass, ENNReal.toReal_one, one_smul]

abbrev base : AdelicVectorBundle OldS := scalarLine OldS
abbrev bundle : AdelicVectorBundle OldS := base.scaleExp φ φ_measurable φ_integrable
theorem bundle_ultrametric : bundle.toNormFamily.IsUltrametricAtFinitePlaces :=
  bundle.toNormFamily.isUltrametricAtFinitePlaces_of_finrank_le_one (Module.finrank_self ℚ).le

abbrev normalizedBundle : AdelicVectorBundle NewS := bundle.numberFieldNormalize
    (hV := bundle_ultrametric)

theorem finite_original_norm_two : bundle.norm ωTwo.val (1 ⊗ₜ[ℚ] (1 : ℚ)) = 2 := by
  classical
  change (base.toNormFamily.scale (fun ω => Real.exp (φ ω))
    (fun _ => Real.exp_pos _)).norm ωTwo.val _ = 2
  erw [scale_norm]
  have hb : base.norm ωTwo.val (1 ⊗ₜ[ℚ] (1 : ℚ)) = 1 := by
    exact (scalarLine_norm_tmul_one OldS _ 1).trans norm_one
  erw [hb, mul_one]
  simp only [φ, Set.indicator_of_mem (Set.mem_singleton _)]
  exact Real.exp_log (by norm_num)

def detOne : ⋀[ℚ]^(Module.finrank ℚ ℚ) ℚ :=
  _root_.exteriorPower.ιMulti ℚ (Module.finrank ℚ ℚ) (fun _ => 1)

theorem finite_original_determinant_norm_two :
    bundle.toNormFamily.determinant.norm ωTwo.val (1 ⊗ₜ[ℚ] detOne) = 2 := by
  erw [detOne, determinant_norm_single_wedge _ (Module.finrank_self ℚ)]
  exact finite_original_norm_two

theorem finite_normalized_determinant_norm_two :
    normalizedBundle.toNormFamily.determinant.norm ωTwo (1 ⊗ₜ[ℚ] detOne) = 2 := by
  have H := bundle.toNormFamily.numberFieldNormalize_determinant_norm_map
    (hξ := bundle_ultrametric) ωTwo (1 ⊗ₜ[ℚ] detOne)
  erw [normalizedNormFamilyTensorEquiv_one_tmul,
    finite_original_determinant_norm_two, rational_finite_exponent,
    Real.rpow_one] at H
  exact H

theorem old_nontrivial_degree :
    bundle.degree (hS := ⟨(Or.inl (inferInstanceAs (DiscreteMeasurableSpace (AbsoluteValue.Place
        ℚ))))⟩)
      (hN := ⟨numberFieldArchimedeanCompletions⟩) = -Real.log 2 := by
  erw [bundle, degree_scaleExp]
  have hb : base.degree (hS := ⟨(Or.inl oldCurveDiscrete)⟩)
      (hN := ⟨numberFieldArchimedeanCompletions⟩) = 0 := by
    erw [base, degree_eq_lineDegree _ (hV := (scalarLine_isLine OldS)), lineDegree_scalarLine]
  erw [hb, φ_integral, Module.finrank_self]
  norm_num

theorem normalized_nontrivial_degree :
    normalizedBundle.degree
        (hS := ⟨(Or.inl (inferInstanceAs (DiscreteMeasurableSpace
          {ω : AbsoluteValue.Place ℚ // ω ≠ AbsoluteValue.trivialPlace ℚ})))⟩)
        = -Real.log 2 := by
  erw [normalizedBundle, bundle.numberFieldNormalize_degree (hV := bundle_ultrametric)]
  exact old_nontrivial_degree

theorem normalized_degree_negative :
    normalizedBundle.degree
        (hS := ⟨(Or.inl (inferInstanceAs (DiscreteMeasurableSpace
          {ω : AbsoluteValue.Place ℚ // ω ≠ AbsoluteValue.trivialPlace ℚ})))⟩)
        < 0 := by
  erw [normalized_nontrivial_degree]
  exact neg_neg_of_pos (Real.log_pos (by norm_num))

abbrev V₂ := Fin 2 → ℚ
def b₂ : Module.Basis (Fin 2) ℚ V₂ := Pi.basisFun ℚ (Fin 2)
def ξ₂ : NormFamily OldS V₂ := ofBasisMixed OldS V₂ b₂
theorem ξ₂_ultrametric
    : ξ₂.IsUltrametricAtFinitePlaces := ofBasisMixed_isUltrametricAtFinitePlaces b₂

theorem rank_two_completed_determinant
    (z : (placeRep ωTwo.val).Completion ⊗[ℚ] (⋀[ℚ]^(Module.finrank ℚ V₂) V₂)) :
    (ξ₂.numberFieldNormalize (hξ := ξ₂_ultrametric)).determinant.norm ωTwo
        (normalizedNormFamilyTensorEquiv ωTwo z) = ξ₂.determinant.norm ωTwo.val z := by
  erw [numberFieldNormalize_determinant_norm_map, rational_finite_exponent, Real.rpow_one]

theorem rank_two_zero_determinant :
    (ξ₂.numberFieldNormalize (hξ := ξ₂_ultrametric)).determinant.norm ωTwo
      (normalizedNormFamilyTensorEquiv ωTwo 0) = 0 := by
  erw [rank_two_completed_determinant, ξ₂.determinant.norm_zero]

def zeroBasis : Module.Basis Empty ℚ (Empty → ℚ) := Pi.basisFun ℚ Empty
def zeroOld : NormFamily OldS (Empty → ℚ) := ofBasisMixed OldS _ zeroBasis
theorem zero_ultrametric
    : zeroOld.IsUltrametricAtFinitePlaces := ofBasisMixed_isUltrametricAtFinitePlaces zeroBasis
abbrev zeroBundle : AdelicVectorBundle OldS where
  carrier := (Empty → ℚ)
  toNormFamily := zeroOld
  toIsAdelic := {
    isMeasurable := zeroOld.isMeasurable_of_subsingleton
    dual_isMeasurable := zeroOld.dual.isMeasurable_of_subsingleton
    isDominated := zeroOld.isDominated_of_subsingleton
  }

theorem rank_zero_determinant_empty_norm (a : (placeRep ωTwo.val).Completion) :
    (zeroOld.numberFieldNormalize (hξ := zero_ultrametric)).determinant.norm ωTwo
        (normalizedNormFamilyTensorEquiv ωTwo (a ⊗ₜ[ℚ]
          _root_.exteriorPower.ιMulti ℚ (Module.finrank ℚ (Empty → ℚ)) (fun _ => 0))) = ‖a‖ := by
  erw [numberFieldNormalize_determinant_norm_map, rational_finite_exponent,
    Real.rpow_one, zeroOld.determinant_norm_empty_tmul (by simp)]
  rfl

theorem rank_zero_normalized_degree :
    (zeroBundle.numberFieldNormalize (hV := zero_ultrametric)).degree
        (hS := ⟨(Or.inl (inferInstanceAs (DiscreteMeasurableSpace
          {ω : AbsoluteValue.Place ℚ // ω ≠ AbsoluteValue.trivialPlace ℚ})))⟩)
        = 0 :=
  zeroBundle.numberFieldNormalize_degree_eq_zero_of_finrank_eq_zero
      (hV := zero_ultrametric) (by simp)

end ArakelovGeometry.NumberFieldNormalizationExamples
