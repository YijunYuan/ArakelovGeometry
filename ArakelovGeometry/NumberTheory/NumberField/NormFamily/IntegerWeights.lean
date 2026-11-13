/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.ScalarLine
public import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.PrimeIndexing

import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.LocalDegree
import ArakelovGeometry.NumberTheory.NumberField.Lattice.Coherence.Criteria
import ArakelovGeometry.NumberTheory.NumberField.Local.ValuationModule.Criterion

/-!
# Actual integer-weighted scalar norms

The arbitrary integer family in Chen–Moriwaki Example 4.4.8 is implemented
on the actual completed scalar line, using the source-normalized curve.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NumberFieldIntegerWeights

open AdelicStructure AdelicStructure.NormalizedNumberFieldPlaces ActualPrimeIndexing

variable {K : Type*} [Field K] [NumberField K]

/-- The printed coefficient is the produced scale of the actual normalized value. -/
theorem primeLogScale_eq_log_base_div_ramificationIdx (P : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (hp : (parameterMeasurableEquivNontrivialPlace.symm
      (normalizedPrimeParameter P)).base = Sum.inl p) :
    normalizedPrimeLogScale P = Real.log (p.val : ℝ) / (P.asIdeal.ramificationIdx ℤ : ℝ) := by
  let hLiesOver : P.asIdeal.LiesOver (Ideal.span {(p.val : ℤ)}) :=
    normalizedPrimeParameter_liesOver_base P p hp
  have hpK : (p.val : K) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  have hν : ((P.valuation K (p.val : K)).log : ℝ) =
      -(P.asIdeal.ramificationIdx ℤ : ℝ) := by
    exact_mod_cast valuation_log_base_prime_eq_neg_ramificationIdx P p
  have hlog := normalizedPrime_log_value P hpK
  change Real.log (normalizedPlaceValue (normalizedPrimeParameter P) (p.val : K)) = _ at hlog
  rw [normalizedPlaceValue_apply_base_prime _ p hp, Real.log_inv, hν] at hlog
  have he : (P.asIdeal.ramificationIdx ℤ : ℝ) ≠ 0 := by
    exact_mod_cast (canonical_ramificationIdx_pos P).ne'
  apply (eq_div_iff he).mpr
  nlinarith

/-- Arbitrary integer weights specify finite-place exponents, with zero at infinity. -/
def weightExponent (b : (normalizedNumberFieldAdelicStructure K).Ωfin → ℤ)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω) : ℝ := by
  classical
  exact if hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin then
    -(b ⟨ω, hω⟩ : ℝ) * normalizedPlaceLogScale ω else 0

/-- The genuine positively rescaled actual completed scalar norm family. -/
def normFamily (b : (normalizedNumberFieldAdelicStructure K).Ωfin → ℤ) :
    NormFamily (normalizedNumberFieldAdelicStructure K) K :=
  (AdelicVectorBundle.scalarLine (normalizedNumberFieldAdelicStructure K)).toNormFamily.scale
    (fun ω => Real.exp (weightExponent b ω)) (fun _ => Real.exp_pos _)

variable (b : (normalizedNumberFieldAdelicStructure K).Ωfin → ℤ)

/-- Exact finite-place exponent at the actual parameter of a prime. -/
theorem weightExponent_prime (P : HeightOneSpectrum (𝓞 K)) :
    weightExponent b (normalizedPrimeParameter P) =
      -(b (normalizedPrimeEquivFinite P) : ℝ) * normalizedPrimeLogScale P := by
  classical
  rw [weightExponent, dite_eq_left (normalizedPrimeParameter_mem_fin P),
    normalizedPlaceLogScale_prime]
  rfl

/-- The exponent at infinity is zero. -/
theorem weightExponent_infinite (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωinf) : weightExponent b ω = 0 := by
  classical
  have hn : ω ∉ (normalizedNumberFieldAdelicStructure K).Ωfin := hω
  rw [weightExponent, dite_eq_right hn]

/-- The actual completed scalar formula, with no integrability hypothesis. -/
theorem norm_tmul_one (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (c : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion) :
    (normFamily b).norm ω (c ⊗ₜ[K] (1 : K)) = Real.exp (weightExponent b ω) * ‖c‖ := by
  rw [normFamily, NormFamily.scale_norm, AdelicVectorBundle.scalarLine_norm_tmul_one]

/-- The literal rational-vector formula. -/
theorem norm_rational (ω : (normalizedNumberFieldAdelicStructure K).Ω) (a : K) :
    (normFamily b).norm ω ((1 : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion)
      ⊗ₜ[K] a) = Real.exp (weightExponent b ω) *
        (normalizedNumberFieldAdelicStructure K).ϕ ω a := by
  rw [normFamily, NormFamily.scale_norm, AdelicVectorBundle.scalarLine_norm_rational]

/-- At infinity the actual standard completed scalar norm is retained. -/
theorem norm_tmul_one_of_infinite (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωinf)
    (c : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion) :
    (normFamily b).norm ω (c ⊗ₜ[K] (1 : K)) = ‖c‖ := by
  rw [norm_tmul_one, weightExponent_infinite b ω hω, Real.exp_zero, one_mul]

/-- The source's printed finite-place completed scalar formula. -/
theorem norm_tmul_one_of_prime_base (P : HeightOneSpectrum (𝓞 K)) (p : Nat.Primes)
    (hp : (parameterMeasurableEquivNontrivialPlace.symm
      (normalizedPrimeParameter P)).base = Sum.inl p)
    (c : ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter P)).Completion) :
    (normFamily b).norm (normalizedPrimeParameter P) (c ⊗ₜ[K] (1 : K)) =
      Real.exp (-(b (normalizedPrimeEquivFinite P) : ℝ) * Real.log (p.val : ℝ) /
        (P.asIdeal.ramificationIdx ℤ : ℝ)) * ‖c‖ := by
  rw [norm_tmul_one, weightExponent_prime, primeLogScale_eq_log_base_div_ramificationIdx P p hp,
    mul_div_assoc]

/-- Every actual finite completed norm is ultrametric. -/
theorem isUltrametricAtFinitePlaces : (normFamily b).IsUltrametricAtFinitePlaces := by
  apply NormFamily.IsUltrametricAtFinitePlaces.scale
  constructor
  intro ω hω x y
  have h := NormFamily.ofBasisMixed_isUltrametricAtFinitePlaces
    (S := normalizedNumberFieldAdelicStructure K) (Module.Basis.singleton (Fin 1) K) ω hω x y
  simpa only [AdelicVectorBundle.scalarLine_toNormFamily,
    NormFamily.ofBasisMixed_norm_of_finite _ ω hω] using h

/-- The log norm of the actual scalar generator at a finite prime. -/
theorem logNorm_one_prime (P : HeightOneSpectrum (𝓞 K)) :
    (normFamily b).logNorm 1 (normalizedPrimeParameter P) =
      -(b (normalizedPrimeEquivFinite P) : ℝ) * normalizedPrimeLogScale P := by
  rw [NormFamily.logNorm, norm_tmul_one, norm_one, mul_one, Real.log_exp, weightExponent_prime]

/-- Rounding the actual logarithmic generator norm recovers the arbitrary integer weight. -/
theorem roundedPrimeBound_eq (P : HeightOneSpectrum (𝓞 K)) :
    (normFamily b).roundedPrimeBound (1 : K) normalizedPrimeParameter normalizedPlaceLogScale P =
      b (normalizedPrimeEquivFinite P) := by
  rw [NormFamily.roundedPrimeBound, logNorm_one_prime, normalizedPlaceLogScale_prime]
  have hγ : normalizedPrimeLogScale P ≠ 0 := (normalizedPrimeLogScale_pos P).ne'
  rw [neg_mul, neg_div, mul_div_cancel_right₀ _ hγ]
  rw [← Int.cast_neg, Int.ceil_intCast, neg_neg]

/-- The literal completed finite global ball is the actual arbitrary-bound valuation module. -/
theorem globalUnitBallModule_eq_valuationModule :
    (normFamily b).globalUnitBallModule (hξ := (isUltrametricAtFinitePlaces b)) =
      FiniteValuation.valuationModule (K := K) (fun P => b (normalizedPrimeEquivFinite P)) := by
  have hc :=
    scalarGlobalUnitBallModule_eq_valuationModule (normFamily b) (hξ := (isUltrametricAtFinitePlaces
    b))
    (x := (1 : K)) one_ne_zero
  have hid : scalarGlobalUnitBallModule (normFamily b) (hξ :=
    (isUltrametricAtFinitePlaces b)) (1 : K) =
      (normFamily b).globalUnitBallModule (hξ := (isUltrametricAtFinitePlaces b)) := by
    ext a
    change a • (1 : K) ∈ (normFamily b).globalUnitBall ↔ a ∈ (normFamily b).globalUnitBall
    rw [smul_eq_mul, mul_one]
  rw [hid] at hc
  have hb : (normFamily b).roundedPrimeBound (1 : K)
      normalizedPrimeParameter normalizedPlaceLogScale =
      fun P => b (normalizedPrimeEquivFinite P) :=
    funext (roundedPrimeBound_eq b)
  exact hc.trans (congrArg (FiniteValuation.valuationModule (K := K)) hb)

/-- The source's exact finite-generation criterion for the literal weighted global ball. -/
theorem globalUnitBallModule_fg_iff :
    ((normFamily b).globalUnitBallModule (hξ := (isUltrametricAtFinitePlaces b))).FG ↔
      {ω | 0 < b ω}.Finite ∨ {ω | b ω < 0}.Infinite := by
  rw [globalUnitBallModule_eq_valuationModule]
  exact FiniteValuation.fg_normalizedFinitePlace_valuationModule_iff b

/-- Infinitely many negative weights give the actual zero global ball. -/
theorem globalUnitBallModule_eq_bot_of_infinite_negative (hneg : {ω | b ω < 0}.Infinite) :
    (normFamily b).globalUnitBallModule (hξ := (isUltrametricAtFinitePlaces b)) = ⊥ := by
  rw [globalUnitBallModule_eq_valuationModule]
  exact FiniteValuation.normalizedFinitePlace_valuationModule_eq_bot_of_infinite_negative b hneg

/-- Nonnegative weights put the original rational generator in the actual finite global ball. -/
theorem one_mem_globalUnitBall_of_nonnegative (hb : ∀ ω, 0 ≤ b ω) :
    (1 : K) ∈ (normFamily b).globalUnitBall := by
  change (1 : K) ∈ (normFamily b).globalUnitBallModule (hξ := (isUltrametricAtFinitePlaces b))
  rw [globalUnitBallModule_eq_valuationModule]
  intro P
  simpa only [map_one, ← WithZero.exp_zero, WithZero.exp_le_exp] using
    hb (normalizedPrimeEquivFinite P)

/-- The actual global span criterion proves coherence for every nonnegative weight family. -/
theorem hasFiniteNormExceptions_of_nonnegative (hb : ∀ ω, 0 ≤ b ω) :
    (normFamily b).HasFiniteNormExceptions := by
  apply NormFamily.hasFiniteNormExceptions_of_span_normalizedGlobalUnitBall_eq_top
    (normFamily b) (hξ := (isUltrametricAtFinitePlaces b))
  apply top_unique
  intro a _
  have h1 := Submodule.subset_span (R := K) (one_mem_globalUnitBall_of_nonnegative b hb)
  have ha := (Submodule.span K (normFamily b).globalUnitBall).smul_mem a h1
  simpa only [smul_eq_mul, mul_one] using ha

/-- The all-one source example has a global ball which is not finitely generated. -/
theorem allOne_globalUnitBallModule_not_fg :
    ¬ ((normFamily (K := K) (fun _ ↦ 1)).globalUnitBallModule (hξ := (isUltrametricAtFinitePlaces
      _))).FG := by
  let : Infinite (normalizedNumberFieldAdelicStructure K).Ωfin :=
    (normalizedPrimeEquivFinite (K := K)).infinite_iff.mp inferInstance
  rw [globalUnitBallModule_fg_iff]
  simp only [zero_lt_one, Set.ofPred_true, Int.reduceLT, Set.ofPred_false,
    Set.finite_empty, Set.Finite.not_infinite, or_false, Set.not_finite]
  exact Set.infinite_univ

/-- Lower domination contradicts the produced nonfinite actual rank-one global ball. -/
theorem allOne_not_lowerDominated :
    ¬ (normFamily (K := K) (fun _ => 1)).IsLowerDominated := by
  intro hdom
  exact allOne_globalUnitBallModule_not_fg
    (fg_globalUnitBallModule_rank_one (normFamily _) (hξ := (isUltrametricAtFinitePlaces _))
      (hdom := hdom))

/-- The all-one source example is not dominated. -/
theorem allOne_not_dominated : ¬ (normFamily (K := K) (fun _ => 1)).IsDominated := by
  intro hdom
  exact allOne_not_lowerDominated hdom.lower

end ArakelovGeometry.NumberFieldIntegerWeights
