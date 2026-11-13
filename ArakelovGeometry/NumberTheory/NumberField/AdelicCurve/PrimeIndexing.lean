/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.Basic
public import ArakelovGeometry.NumberTheory.NumberField.Lattice.UnitBall.Global
public import ArakelovGeometry.NumberTheory.NumberField.Local.ValuationModule.Rounded

import ArakelovGeometry.AdelicCurve.Equiv
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Rational
import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.ProductFormulaComparison

/-!
# Actual prime indexing for normalized scalar unit balls

The actual finite prime ideals exhaust the nonarchimedean locus of the
rationally normalized number-field curve. Positive-power equivalence, rather
than any assumed ramification or completion-degree formula, supplies local
logarithmic scales.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct NNReal WithZero

noncomputable section

namespace ArakelovGeometry.ActualPrimeIndexing

open AdelicStructure AdelicStructure.NormalizedNumberFieldPlaces

variable {K : Type*} [Field K] [NumberField K]

/-- The actual class of the actual finite absolute value of a nonzero integral prime. -/
def normalizedPrimeParameter (p : HeightOneSpectrum (𝓞 K)) :
    (normalizedNumberFieldAdelicStructure K).Ω :=
  ⟨Quotient.mk' (FinitePlace.mk p).val, mk_finitePlace_ne_trivialPlace _⟩

/-- Every actual prime parameter belongs to the actual normalized finite locus. -/
theorem normalizedPrimeParameter_mem_fin (p : HeightOneSpectrum (𝓞 K)) :
    normalizedPrimeParameter p ∈ (normalizedNumberFieldAdelicStructure K).Ωfin := by
  have he : (normalizedPlaceValue (normalizedPrimeParameter p)).IsEquiv
      (FinitePlace.mk p).val :=
    Quotient.eq'.mp (normalizedPlaceValue_class (normalizedPrimeParameter p))
  exact (NumberField.isNonarchimedean_congr he).mpr
    (NumberField.finitePlace_isNonarchimedean _)

/-- No two actual integral primes represent the same normalized place parameter. -/
theorem normalizedPrimeParameter_injective :
    Function.Injective (normalizedPrimeParameter (K := K)) := by
  intro p q hpq
  exact FinitePlace.mk_eq_iff.mp
    (NumberField.finitePlace_injective_place (congrArg Subtype.val hpq))

/-- Every actual normalized finite parameter comes from an actual integral prime. -/
theorem exists_normalizedPrimeParameter_eq
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) :
    ∃ p : HeightOneSpectrum (𝓞 K), normalizedPrimeParameter p = ω := by
  have hnt : (normalizedPlaceValue ω).IsNontrivial :=
    parameter_isNontrivial (parameterMeasurableEquivNontrivialPlace.symm ω)
  obtain ⟨v, hv⟩ := NumberField.exists_finitePlace_of_isNonarchimedean hnt hω
  refine ⟨v.maximalIdeal, Subtype.ext ?_⟩
  change Quotient.mk' (FinitePlace.mk v.maximalIdeal).val = ω.val
  rw [FinitePlace.mk_maximalIdeal]
  exact (Quotient.sound' hv).symm.trans (normalizedPlaceValue_class ω)

/-- Actual nonzero primes exhaust precisely the actual normalized nonarchimedean locus. -/
theorem normalizedPrimeParameter_range : Set.range (normalizedPrimeParameter (K := K)) =
    (normalizedNumberFieldAdelicStructure K).Ωfin := by
  ext ω
  constructor
  · rintro ⟨p, rfl⟩
    exact normalizedPrimeParameter_mem_fin p
  · exact exists_normalizedPrimeParameter_eq ω

/-- The produced bijection between actual integral primes and actual normalized finite places. -/
def normalizedPrimeEquivFinite : HeightOneSpectrum (𝓞 K) ≃
    (normalizedNumberFieldAdelicStructure K).Ωfin :=
  Equiv.ofBijective (fun p => ⟨normalizedPrimeParameter p, normalizedPrimeParameter_mem_fin p⟩)
    ⟨fun _ _ h => normalizedPrimeParameter_injective (congrArg Subtype.val h), by
      intro ω
      obtain ⟨p, hp⟩ := exists_normalizedPrimeParameter_eq ω.1 ω.2
      exact ⟨p, Subtype.ext hp⟩⟩

/-- The actual finite-place logarithm is its residue-cardinality logarithm times
the actual signed integer adic exponent. -/
theorem finitePlace_log_value (p : HeightOneSpectrum (𝓞 K)) {a : K} (ha : a ≠ 0) :
    Real.log ((FinitePlace.mk p) a) =
      Real.log (Ideal.absNorm p.asIdeal) * ((p.valuation K a).log : ℝ) := by
  have hv : p.valuation K a ≠ 0 := (p.valuation K).ne_zero_iff.mpr ha
  have heq : (FinitePlace.mk p) a =
      (WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero p)
        (p.valuation K a) : ℝ) := by
    rw [← FinitePlace.norm_embedding_eq, FinitePlace.maximalIdeal_mk,
      FinitePlace.norm_embedding']
  rw [heq, WithZeroMulInt.toNNReal_neg_apply _ hv, NNReal.coe_zpow, Real.log_zpow]
  push_cast
  ring

/-- Positive-power equivalence produces an actual positive logarithmic scale;
no ramification or completion-degree identity is an input. -/
theorem exists_positive_log_scale_of_equiv (p : HeightOneSpectrum (𝓞 K))
    (φ : AbsoluteValue K ℝ) (he : (FinitePlace.mk p).val.IsEquiv φ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ a : K, a ≠ 0 →
      Real.log (φ a) = γ * ((p.valuation K a).log : ℝ) := by
  obtain ⟨c, hc, hpower⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp he
  have hN : (1 : ℝ) < Ideal.absNorm p.asIdeal := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm p
  refine ⟨c * Real.log (Ideal.absNorm p.asIdeal), mul_pos hc (Real.log_pos hN), ?_⟩
  intro a ha
  calc
    Real.log (φ a) = Real.log ((FinitePlace.mk p) a ^ c) :=
      congrArg Real.log (congrFun hpower a).symm
    _ = c * Real.log ((FinitePlace.mk p) a) :=
      Real.log_rpow ((FinitePlace.mk p).val.pos ha) c
    _ = _ := by rw [finitePlace_log_value p ha]; ring

/-- The actual normalized absolute value has a positive scale at each actual prime. -/
def normalizedPrimeLogScale (p : HeightOneSpectrum (𝓞 K)) : ℝ :=
  (exists_positive_log_scale_of_equiv p (normalizedPlaceValue (normalizedPrimeParameter p))
    (Quotient.eq'.mp (normalizedPlaceValue_class (normalizedPrimeParameter p)).symm)).choose

/-- Positivity of the produced actual normalized prime scale. -/
theorem normalizedPrimeLogScale_pos (p : HeightOneSpectrum (𝓞 K)) :
    0 < normalizedPrimeLogScale p :=
  (exists_positive_log_scale_of_equiv p (normalizedPlaceValue (normalizedPrimeParameter p))
    (Quotient.eq'.mp (normalizedPlaceValue_class (normalizedPrimeParameter p)).symm)).choose_spec.1

/-- The normalized value has exactly the produced log-scale times actual signed adic order. -/
theorem normalizedPrime_log_value (p : HeightOneSpectrum (𝓞 K)) {a : K} (ha : a ≠ 0) :
    Real.log ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p) a) =
      normalizedPrimeLogScale p * ((p.valuation K a).log : ℝ) :=
  (exists_positive_log_scale_of_equiv p (normalizedPlaceValue (normalizedPrimeParameter p))
    (Quotient.eq'.mp (normalizedPlaceValue_class (normalizedPrimeParameter p)).symm)).choose_spec.2
      a ha

/-- Extend the produced prime scales to all actual normalized parameters. -/
def normalizedPlaceLogScale (ω : (normalizedNumberFieldAdelicStructure K).Ω) : ℝ := by
  classical
  exact if hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin then
    normalizedPrimeLogScale (normalizedPrimeEquivFinite.symm ⟨ω, hω⟩)
  else 1

/-- The extended scale agrees with the actual prime scale at its actual prime parameter. -/
theorem normalizedPlaceLogScale_prime (p : HeightOneSpectrum (𝓞 K)) :
    normalizedPlaceLogScale (normalizedPrimeParameter p) = normalizedPrimeLogScale p := by
  classical
  rw [normalizedPlaceLogScale, dite_eq_left (normalizedPrimeParameter_mem_fin p)]
  have hinv : normalizedPrimeEquivFinite.symm
      ⟨normalizedPrimeParameter p, normalizedPrimeParameter_mem_fin p⟩ = p :=
    normalizedPrimeEquivFinite.symm_apply_apply p
  exact congrArg normalizedPrimeLogScale hinv

/-- Every extended scale is positive, including outside the finite locus. -/
theorem normalizedPlaceLogScale_pos (ω : (normalizedNumberFieldAdelicStructure K).Ω) :
    0 < normalizedPlaceLogScale ω := by
  classical
  unfold normalizedPlaceLogScale
  split
  · exact normalizedPrimeLogScale_pos _
  · exact zero_lt_one

/-- Every actual normalized place atom is strictly positive: finite atoms have
positive actual completion degree and infinite atoms have positive multiplicity. -/
theorem normalized_singleton_pos (ω : (normalizedNumberFieldAdelicStructure K).Ω) :
    0 < (normalizedNumberFieldAdelicStructure K).v {ω} := by
  rcases place_trichotomy ω.val with ht | ⟨v, hv⟩ | ⟨w, hw⟩
  · exact False.elim (ω.property ht)
  · have hω : ω = ⟨Quotient.mk' v.val, mk_finitePlace_ne_trivialPlace v⟩ :=
      Subtype.ext hv
    rw [hω]
    have hm := normalizedNumberFieldAdelicStructure_v_singleton (K := K)
      ⟨Quotient.mk' v.val, mk_finitePlace_ne_trivialPlace v⟩
    have hpos : (0 : ENNReal) < ((normalizedPlaceValue
        ⟨Quotient.mk' v.val, mk_finitePlace_ne_trivialPlace v⟩).localDegree ℚ : ENNReal) := by
      exact_mod_cast normalizedPlaceValue_finitePlace_localDegree_pos v
    exact hm.symm ▸ hpos
  · have hω : ω = ⟨Quotient.mk' w.val, mk_infinitePlace_ne_trivialPlace w⟩ :=
      Subtype.ext hw
    rw [hω, normalizedNumberFieldAdelicStructure_v_infinitePlace]
    exact_mod_cast (InfinitePlace.mult_pos (w := w))

/-- The actual completion-degree mass times the produced prime log scale is
exactly the residue-cardinality logarithm. This uses the proved weighted-log formula. -/
theorem normalized_weighted_prime_log_scale (p : HeightOneSpectrum (𝓞 K)) :
    (normalizedNumberFieldAdelicStructure K).v.real {normalizedPrimeParameter p} *
      normalizedPlaceLogScale (normalizedPrimeParameter p) =
        Real.log (Ideal.absNorm p.asIdeal) := by
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer K
  have hπ0 : π ≠ 0 := (p.valuation K).ne_zero_iff.mp (by rw [hπ]; exact WithZero.exp_ne_zero)
  have hα := normalizedPrime_log_value p hπ0
  have hβ := finitePlace_log_value p hπ0
  rw [hπ, WithZero.log_exp] at hα hβ
  have hd := normalizedPlaceValue_weightedLog_finitePlace (FinitePlace.mk p) hπ0
  change ((normalizedPlaceValue (normalizedPrimeParameter p)).localDegree ℚ : ℝ) *
      Real.log ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p) π) =
        Real.log ((FinitePlace.mk p) π) at hd
  rw [hα, hβ] at hd
  change ((normalizedNumberFieldAdelicStructure K).v {normalizedPrimeParameter p}).toReal *
      normalizedPlaceLogScale (normalizedPrimeParameter p) = _
  have hm := normalizedNumberFieldAdelicStructure_v_singleton (K := K)
    (normalizedPrimeParameter p)
  have hr : ((normalizedNumberFieldAdelicStructure K).v
      {normalizedPrimeParameter p}).toReal =
        ((normalizedPlaceValue (normalizedPrimeParameter p)).localDegree ℚ : ℝ) := by
    exact (congrArg ENNReal.toReal hm).trans (ENNReal.toReal_natCast _)
  rw [hr, normalizedPlaceLogScale_prime]
  norm_num at hd
  nlinarith

/-- Actual normalized prime masses and scales have the uniform positive `log 2` gap. -/
theorem normalized_weighted_prime_log_gap (p : HeightOneSpectrum (𝓞 K)) :
    Real.log 2 ≤
      (normalizedNumberFieldAdelicStructure K).v.real {normalizedPrimeParameter p} *
        normalizedPlaceLogScale (normalizedPrimeParameter p) := by
  rw [normalized_weighted_prime_log_scale]
  apply Real.log_le_log (by norm_num : (0 : ℝ) < 2)
  have hN := HeightOneSpectrum.one_lt_absNorm p
  exact_mod_cast (show 2 ≤ Ideal.absNorm p.asIdeal by omega)

variable {E : Type*} [AddCommGroup E] [Module K E]

/-- The literal completed rational unit-ball scalar condition is exactly the
actual rounded integral-prime valuation condition. -/
theorem smul_mem_rationalUnitBall_iff_valuation_le
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) {x : E} (hx : x ≠ 0)
    (p : HeightOneSpectrum (𝓞 K)) (a : K) :
    a • x ∈ ξ.rationalUnitBall (normalizedPrimeParameter p) ↔
      p.valuation K a ≤ WithZero.exp
        (ξ.roundedPrimeBound x normalizedPrimeParameter normalizedPlaceLogScale p) := by
  by_cases ha : a = 0
  · subst a
    simp only [zero_smul, NormFamily.zero_mem_rationalUnitBall, map_zero, zero_le, iff_self]
  have hα : 0 < (normalizedNumberFieldAdelicStructure K).ϕ
      (normalizedPrimeParameter p) a := (normalizedPlaceValue _).pos ha
  have hν := ξ.norm_rational_pos (normalizedPrimeParameter p) hx
  have hγ := normalizedPrimeLogScale_pos p
  have hball : a • x ∈ ξ.rationalUnitBall (normalizedPrimeParameter p) ↔
      normalizedPrimeLogScale p * ((p.valuation K a).log : ℝ) +
        ξ.logNorm x (normalizedPrimeParameter p) ≤ 0 := by
    change ξ.norm _ (1 ⊗ₜ[K] (a • x)) ≤ 1 ↔ _
    rw [ξ.norm_rational_smul,
      ← Real.log_le_log_iff (mul_pos hα hν) zero_lt_one, Real.log_one,
      Real.log_mul (ne_of_gt hα) (ne_of_gt hν), normalizedPrime_log_value p ha]
    rfl
  have hv : p.valuation K a ≠ 0 := (p.valuation K).ne_zero_iff.mpr ha
  have hval : p.valuation K a ≤ WithZero.exp
        (ξ.roundedPrimeBound x normalizedPrimeParameter normalizedPlaceLogScale p) ↔
      (p.valuation K a).log ≤
        -⌈ξ.logNorm x (normalizedPrimeParameter p) / normalizedPrimeLogScale p⌉ := by
    rw [← WithZero.log_le_log hv WithZero.exp_ne_zero, WithZero.log_exp,
      NormFamily.roundedPrimeBound, normalizedPlaceLogScale_prime]
  rw [hball, hval, ← Int.floor_neg, Int.le_floor, ← neg_div, le_div_iff₀ hγ]
  constructor <;> intro h <;> nlinarith

/-- Exhaustive actual prime indexing identifies all literal global scalar
unit-ball conditions with membership in the actual valuation module. -/
theorem smul_mem_globalUnitBall_iff_mem_valuationModule
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) {x : E} (hx : x ≠ 0)
    (a : K) : a • x ∈ ξ.globalUnitBall ↔
      a ∈ FiniteValuation.valuationModule (K := K)
        (ξ.roundedPrimeBound x normalizedPrimeParameter normalizedPlaceLogScale) := by
  constructor
  · intro h p
    exact (smul_mem_rationalUnitBall_iff_valuation_le ξ hx p a).mp
      (h (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p))
  · intro h ω hω
    obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
    exact (smul_mem_rationalUnitBall_iff_valuation_le ξ hx p a).mpr (h p)

/-- The actual integral scalar coefficients of a vector in the literal global ball. -/
def scalarGlobalUnitBallModule (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [hξ : ξ.IsUltrametricAtFinitePlaces] (x : E) : Submodule (𝓞 K) K :=
  (ξ.globalUnitBallModule).comap
    ({
      toFun := fun a => a • x
      map_add' := fun a b => add_smul a b x
      map_smul' := fun r a => by
        change (algebraMap (𝓞 K) K r * a) • x =
          algebraMap (𝓞 K) K r • (a • x)
        exact mul_smul _ _ _ } : K →ₗ[𝓞 K] E)

/-- The actual coefficient comap is exactly the actual rounded valuation module. -/
theorem scalarGlobalUnitBallModule_eq_valuationModule
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) [hξ : ξ.IsUltrametricAtFinitePlaces]
    {x : E} (hx : x ≠ 0) : scalarGlobalUnitBallModule ξ x =
      FiniteValuation.valuationModule (K := K)
        (ξ.roundedPrimeBound x normalizedPrimeParameter normalizedPlaceLogScale) := by
  ext a
  exact smul_mem_globalUnitBall_iff_mem_valuationModule ξ hx a

/-- The actual scalar coefficient module is finitely generated under the explicit
positive weighted arithmetic gap, by the produced rounded valuation-module theorem. -/
theorem fg_scalarGlobalUnitBallModule_of_weighted_gap
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) [hξ : ξ.IsUltrametricAtFinitePlaces]
    [hdom : ξ.IsLowerDominated]
    [hμ : (normalizedNumberFieldAdelicStructure K).HasPositiveSingletons]
    {x : E} (hx : x ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ p : HeightOneSpectrum (𝓞 K), ε ≤
      (normalizedNumberFieldAdelicStructure K).v.real {normalizedPrimeParameter p} *
        normalizedPlaceLogScale (normalizedPrimeParameter p)) :
    (scalarGlobalUnitBallModule ξ x).FG := by
  rw [scalarGlobalUnitBallModule_eq_valuationModule ξ hx]
  exact hdom.fg_rounded_valuationModule hx normalizedPrimeParameter
    normalizedPrimeParameter_injective normalizedPlaceLogScale
    (fun p => normalizedPlaceLogScale_pos _) hε hgap

/-- For the actual normalized number-field curve, lower domination produces
finite generation of every nonzero vector's literal global scalar coefficient module. -/
theorem fg_scalarGlobalUnitBallModule
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) [hξ : ξ.IsUltrametricAtFinitePlaces]
    [hdom : ξ.IsLowerDominated] {x : E} (hx : x ≠ 0) :
    (scalarGlobalUnitBallModule ξ x).FG :=
  fg_scalarGlobalUnitBallModule_of_weighted_gap ξ (hμ := ⟨normalized_singleton_pos⟩) hx
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)) normalized_weighted_prime_log_gap

/-- The actual rank-one literal global integral unit ball is finitely generated
for every lower-dominated ultrametric norm family, including the zero-module case. -/
theorem fg_globalUnitBallModule_rank_one
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) K) [hξ : ξ.IsUltrametricAtFinitePlaces]
    [hdom : ξ.IsLowerDominated] : (ξ.globalUnitBallModule).FG := by
  have heq : scalarGlobalUnitBallModule ξ (1 : K) = ξ.globalUnitBallModule := by
    ext a
    change a • (1 : K) ∈ ξ.globalUnitBall ↔ a ∈ ξ.globalUnitBall
    rw [smul_eq_mul, mul_one]
  exact heq ▸ fg_scalarGlobalUnitBallModule ξ one_ne_zero

end ArakelovGeometry.ActualPrimeIndexing

end
