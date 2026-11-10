/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NumberFieldValuationTruncationChain
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldLineIndex

/-!
# Exact finite-support valuation ideals

The literal valuation module is the genuine product of actual prime fractional
ideals with the source negative exponents. Prime orders and localizations are
proved from the accepted actual fractional-ideal valuation producers.
-/

open NumberField IsDedekindDomain
open scoped NumberField WithZero Pointwise

noncomputable section

namespace ArakelovGeometry.FiniteValuation

open AdelicStructure ActualPrimeIndexing NumberFieldLineIndex

variable {K : Type*} [Field K] [NumberField K]

attribute [local instance 2000] Algebra.toModule

/-- All actual prime valuations detect membership in a genuine nonzero fractional ideal. -/
theorem fractionalIdeal_mem_iff_valuation_le
    (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hJ : J ≠ 0) (x : K) :
    x ∈ J ↔ ∀ p : HeightOneSpectrum (𝓞 K),
      p.valuation K x ≤ WithZero.exp (-FractionalIdeal.count K p J) := by
  constructor
  · intro hx p
    exact fractionalIdeal_member_valuation_le J hJ p hx
  · intro hx
    have hInv : J⁻¹ ≠ 0 := inv_ne_zero hJ
    have hmem : x ∈ (J⁻¹)⁻¹ := (FractionalIdeal.mem_inv_iff hInv).mpr (by
      intro y hy
      rw [FractionalIdeal.mem_one_iff]
      apply HeightOneSpectrum.mem_integers_of_valuation_le_one K
      intro p
      have hyle := fractionalIdeal_member_valuation_le J⁻¹ hInv p hy
      rw [FractionalIdeal.count_inv] at hyle
      calc
        p.valuation K (x * y) = p.valuation K x * p.valuation K y := map_mul _ _ _
        _ ≤ WithZero.exp (-FractionalIdeal.count K p J) *
            WithZero.exp (FractionalIdeal.count K p J) := mul_le_mul' (hx p) (by simpa using hyle)
        _ = 1 := by rw [← WithZero.exp_add]; simp)
    simpa only [inv_inv] using hmem

/-- The literal all-prime module of the negative actual fractional orders is the ideal itself. -/
theorem valuationModule_neg_count_eq_fractionalIdeal
    (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hJ : J ≠ 0) :
    valuationModule (K := K) (fun p => -FractionalIdeal.count K p J) =
      (J : Submodule (𝓞 K) K) := by
  ext x
  exact (fractionalIdeal_mem_iff_valuation_le J hJ x).symm

/-- The fractional ideal is built from the literal finite-support valuation module. -/
def finiteSupportValuationFractionalIdeal
    (b : HeightOneSpectrum (𝓞 K) → ℤ) (hb : {p | b p ≠ 0}.Finite) :
    FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
  ⟨valuationModule (K := K) b, FractionalIdeal.isFractional_of_fg
    (fg_valuationModule_of_finite_positive (hb.subset (fun _ hp => ne_of_gt hp)))⟩

@[simp]
theorem finiteSupportValuationFractionalIdeal_coe
    (b : HeightOneSpectrum (𝓞 K) → ℤ) (hb : {p | b p ≠ 0}.Finite) :
    (finiteSupportValuationFractionalIdeal b hb : Submodule (𝓞 K) K) =
      valuationModule (K := K) b := rfl

/-- The exact actual prime product has the source exponent minus the literal bound. -/
theorem finiteSupportValuationFractionalIdeal_eq_primeProduct
    (b : HeightOneSpectrum (𝓞 K) → ℤ) (hb : {p | b p ≠ 0}.Finite) :
    finiteSupportValuationFractionalIdeal b hb =
      ∏ᶠ p : HeightOneSpectrum (𝓞 K),
        (p.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-b p) := by
  let J := ∏ᶠ p : HeightOneSpectrum (𝓞 K),
    (p.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-b p)
  have hJ : J ≠ 0 := finprod_ne_zero (fun p =>
    zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr p.ne_bot))
  have hcof : ∀ᶠ p : HeightOneSpectrum (𝓞 K) in Filter.cofinite, -b p = 0 := by
    filter_upwards [show ∀ᶠ p in Filter.cofinite, b p = 0 from
      Filter.eventually_cofinite.mpr hb] with p hp
    simp [hp]
  have hc (p : HeightOneSpectrum (𝓞 K)) : FractionalIdeal.count K p J = -b p :=
    FractionalIdeal.count_finprod K p _ hcof
  ext x
  change (∀ p, p.valuation K x ≤ WithZero.exp (b p)) ↔ x ∈ J
  simpa only [hc, neg_neg] using (fractionalIdeal_mem_iff_valuation_le J hJ x).symm

/-- The same exact product is a finite product over the actual nonzero bounds. -/
theorem finiteSupportValuationFractionalIdeal_eq_finsetPrimeProduct
    (b : HeightOneSpectrum (𝓞 K) → ℤ) (hb : {p | b p ≠ 0}.Finite) :
    finiteSupportValuationFractionalIdeal b hb =
      ∏ p ∈ hb.toFinset,
        (p.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-b p) := by
  classical
  rw [finiteSupportValuationFractionalIdeal_eq_primeProduct]
  apply finprod_eq_finsetProd_of_mulSupport_subset
  intro p hp
  by_contra hnot
  have hb0 : b p = 0 := not_not.mp (fun h => hnot (hb.mem_toFinset.mpr h))
  exact hp (by simp [hb0])

theorem finiteSupportValuationFractionalIdeal_ne_zero
    (b : HeightOneSpectrum (𝓞 K) → ℤ) (hb : {p | b p ≠ 0}.Finite) :
    finiteSupportValuationFractionalIdeal b hb ≠ 0 := by
  rw [finiteSupportValuationFractionalIdeal_eq_primeProduct]
  exact finprod_ne_zero (fun p => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr p.ne_bot))

/-- Every actual prime order is exactly the negative source bound. -/
theorem finiteSupportValuationFractionalIdeal_count
    (b : HeightOneSpectrum (𝓞 K) → ℤ) (hb : {p | b p ≠ 0}.Finite)
    (p : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K p (finiteSupportValuationFractionalIdeal b hb) = -b p := by
  rw [finiteSupportValuationFractionalIdeal_eq_primeProduct]
  apply FractionalIdeal.count_finprod
  filter_upwards [show ∀ᶠ p in Filter.cofinite, b p = 0 from
    Filter.eventually_cofinite.mpr hb] with p hp
  simp [hp]

theorem finiteSupportValuationFractionalIdeal_invertible
    (b : HeightOneSpectrum (𝓞 K) → ℤ) (hb : {p | b p ≠ 0}.Finite) :
    Module.Invertible (𝓞 K) (finiteSupportValuationFractionalIdeal b hb : Submodule (𝓞 K) K) :=
  fractionalIdeal_module_invertible _ (finiteSupportValuationFractionalIdeal_ne_zero b hb)

/-- The actual literal finite-support module is finitely generated. -/
theorem finiteSupportValuationFractionalIdeal_fg
    (b : HeightOneSpectrum (𝓞 K) → ℤ) (hb : {p | b p ≠ 0}.Finite) :
    (finiteSupportValuationFractionalIdeal b hb : Submodule (𝓞 K) K).FG :=
  fg_valuationModule_of_finite_positive (hb.subset (fun _ hp => ne_of_gt hp))

/-- Every genuine finite nonzero fraction-field submodule has actual finitely supported bounds. -/
theorem exists_finiteSupport_valuationModule_eq_of_fg
    (M : Submodule (𝓞 K) K) (hM : M.FG) (hne : M ≠ ⊥) :
    ∃ (b : HeightOneSpectrum (𝓞 K) → ℤ) (hb : {p | b p ≠ 0}.Finite),
      (finiteSupportValuationFractionalIdeal b hb : Submodule (𝓞 K) K) = M ∧
        Module.Invertible (𝓞 K) M := by
  let J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    ⟨M, FractionalIdeal.isFractional_of_fg hM⟩
  have hJ : J ≠ 0 := fun h => hne (FractionalIdeal.coeToSubmodule_eq_bot.mpr h)
  let b := fun p => -FractionalIdeal.count K p J
  have hb : {p | b p ≠ 0}.Finite := by
    simpa only [b, neg_ne_zero] using
      Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors J)
  refine ⟨b, hb, ?_, fractionalIdeal_module_invertible J hJ⟩
  exact valuationModule_neg_count_eq_fractionalIdeal J hJ

/-- The actual normalized rational local coefficient ring is the literal prime-valuation ring. -/
theorem mem_normalizedPrimeLocalRing_iff_valuation_le_one
    (p : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ (normalizedNumberFieldAdelicStructure K).rationalLocalRing
      (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p) ↔
        p.valuation K x ≤ 1 := by
  have hp : ((normalizedNumberFieldAdelicStructure K).ϕ
      (normalizedPrimeParameter p)).IsEquiv (FinitePlace.mk p).val :=
    Quotient.eq'.mp (AdelicStructure.normalizedPlaceValue_class
      (normalizedPrimeParameter p))
  rw [(normalizedNumberFieldAdelicStructure K).rationalLocalRing_eq_finitePlaceInteger
    _ _ (FinitePlace.mk p) hp]
  simpa only [FinitePlace.maximalIdeal_mk] using
    Valuation.mem_integer_iff ((FinitePlace.mk p).maximalIdeal.valuation K) x

/-- The actual localization inside the fraction field is scalar extension of the literal ideal. -/
def normalizedPrimeLocalizedFractionalIdeal
    (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (p : HeightOneSpectrum (𝓞 K)) :
    Submodule ((normalizedNumberFieldAdelicStructure K).rationalLocalRing
      (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p)) K :=
  Submodule.span _ (J : Set K)

/-- Actual order attainment makes the literal localized module exactly the prime valuation ball. -/
theorem mem_normalizedPrimeLocalizedFractionalIdeal_iff
    (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hJ : J ≠ 0)
    (p : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ normalizedPrimeLocalizedFractionalIdeal J p ↔
      p.valuation K x ≤ WithZero.exp (-FractionalIdeal.count K p J) := by
  constructor
  · intro hx
    apply Submodule.span_induction
      (p := fun x _ => p.valuation K x ≤ WithZero.exp (-FractionalIdeal.count K p J))
      (fun y hy => fractionalIdeal_member_valuation_le J hJ p hy) (by simp)
      (fun y z _ _ hy hz => (p.valuation K).map_add _ _ |>.trans (max_le hy hz))
      (fun r y _ hy => ?_) hx
    rw [Algebra.smul_def, map_mul]
    have hr := (mem_normalizedPrimeLocalRing_iff_valuation_le_one p (r : K)).mp r.property
    exact (mul_le_mul' hr hy).trans_eq (one_mul _)
  · intro hx
    obtain ⟨a, ha, hane, hva⟩ := exists_fractionalIdeal_member_attaining_valuation J hJ p
    let r : (normalizedNumberFieldAdelicStructure K).rationalLocalRing
        (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p) :=
      ⟨x / a, (mem_normalizedPrimeLocalRing_iff_valuation_le_one p _).mpr (by
        rw [map_div₀, hva, div_le_one₀ WithZero.exp_pos]
        exact hx)⟩
    have hmem := (normalizedPrimeLocalizedFractionalIdeal J p).smul_mem r
      (Submodule.subset_span ha)
    change x / a * a ∈ normalizedPrimeLocalizedFractionalIdeal J p at hmem
    simpa only [div_mul_cancel₀ _ hane] using hmem

/-- The literal local span has the actual denominator-outside-the-prime criterion. -/
theorem mem_normalizedPrimeLocalizedFractionalIdeal_iff_exists_denominator
    (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hJ : J ≠ 0)
    (p : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ normalizedPrimeLocalizedFractionalIdeal J p ↔
      ∃ d : p.asIdeal.primeCompl, algebraMap (𝓞 K) K d * x ∈ J := by
  constructor
  · intro hx
    have hv := (mem_normalizedPrimeLocalizedFractionalIdeal_iff J hJ p x).mp hx
    obtain ⟨a, ha, hane, hva⟩ := exists_fractionalIdeal_member_attaining_valuation J hJ p
    let r : (normalizedNumberFieldAdelicStructure K).rationalLocalRing
        (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p) :=
      ⟨x / a, (mem_normalizedPrimeLocalRing_iff_valuation_le_one p _).mpr (by
        rw [map_div₀, hva, div_le_one₀ WithZero.exp_pos]
        exact hv)⟩
    have hp : ((normalizedNumberFieldAdelicStructure K).ϕ
        (normalizedPrimeParameter p)).IsEquiv (FinitePlace.mk p).val :=
      Quotient.eq'.mp (AdelicStructure.normalizedPlaceValue_class (normalizedPrimeParameter p))
    let S := normalizedNumberFieldAdelicStructure K
    obtain ⟨m, d, hrd⟩ :=
      S.exists_integral_denominator_outside_finitePlace _ _ (FinitePlace.mk p) hp r
    let d' : p.asIdeal.primeCompl :=
      ⟨d, by simpa only [FinitePlace.maximalIdeal_mk] using d.property⟩
    refine ⟨d', ?_⟩
    have heq : algebraMap (𝓞 K) K d' * x = algebraMap (𝓞 K) K m * a := by
      have h := congrArg (fun z : K => z * a) hrd
      change x / a * algebraMap (𝓞 K) K d * a = algebraMap (𝓞 K) K m * a at h
      simpa only [mul_right_comm (x / a), div_mul_cancel₀ _ hane, d', mul_comm x] using h
    rw [heq]
    exact J.val.smul_mem m ha
  · rintro ⟨d, hd⟩
    have hval := fractionalIdeal_member_valuation_le J hJ p hd
    have hdv : p.valuation K (algebraMap (𝓞 K) K d) = 1 := by
      rw [p.valuation_of_algebraMap]
      exact (p.intValuation_eq_one_iff_mem_primeCompl d).mpr d.property
    rw [map_mul, hdv, one_mul] at hval
    exact (mem_normalizedPrimeLocalizedFractionalIdeal_iff J hJ p x).mpr hval

/-- A genuine uniformizer power gives the literal principal local valuation ball
for every integer. -/
theorem mem_normalizedPrime_span_uniformizer_zpow_iff
    (p : HeightOneSpectrum (𝓞 K)) (π : K)
    (hπ : p.valuation K π = WithZero.exp (-1 : ℤ)) (n : ℤ) (x : K) :
    x ∈ Submodule.span ((normalizedNumberFieldAdelicStructure K).rationalLocalRing
      (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p)) {π ^ n} ↔
        p.valuation K x ≤ WithZero.exp (-n) := by
  have hπne : π ≠ 0 := (p.valuation K).ne_zero_iff.mp (hπ ▸ WithZero.exp_ne_zero)
  have hv : p.valuation K (π ^ n) = WithZero.exp (-n) := by
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
    simp
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, hr⟩
    rw [← hr, Algebra.smul_def, map_mul, hv]
    have hrv := (mem_normalizedPrimeLocalRing_iff_valuation_le_one p (r : K)).mp r.property
    exact (mul_le_mul' hrv le_rfl).trans_eq (one_mul _)
  · intro hx
    let r : (normalizedNumberFieldAdelicStructure K).rationalLocalRing
        (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p) :=
      ⟨x / π ^ n, (mem_normalizedPrimeLocalRing_iff_valuation_le_one p _).mpr (by
        rw [map_div₀, hv, div_le_one₀ WithZero.exp_pos]
        exact hx)⟩
    refine ⟨r, ?_⟩
    change x / π ^ n * π ^ n = x
    exact div_mul_cancel₀ _ (zpow_ne_zero _ hπne)

/-- Exact localization at the actual normalized prime, with its actual integer order. -/
theorem normalizedPrimeLocalizedFractionalIdeal_eq_span_uniformizer_zpow
    (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hJ : J ≠ 0)
    (p : HeightOneSpectrum (𝓞 K)) (π : K)
    (hπ : p.valuation K π = WithZero.exp (-1 : ℤ)) :
    normalizedPrimeLocalizedFractionalIdeal J p =
      Submodule.span ((normalizedNumberFieldAdelicStructure K).rationalLocalRing
        (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p))
        {π ^ FractionalIdeal.count K p J} := by
  ext x
  rw [mem_normalizedPrimeLocalizedFractionalIdeal_iff J hJ,
    mem_normalizedPrime_span_uniformizer_zpow_iff p π hπ]

/-- The exact source localization has exponent minus the original finite-support bound. -/
theorem normalizedPrimeLocalized_finiteSupportValuationFractionalIdeal_eq
    (b : HeightOneSpectrum (𝓞 K) → ℤ) (hb : {p | b p ≠ 0}.Finite)
    (p : HeightOneSpectrum (𝓞 K)) (π : K)
    (hπ : p.valuation K π = WithZero.exp (-1 : ℤ)) :
    normalizedPrimeLocalizedFractionalIdeal (finiteSupportValuationFractionalIdeal b hb) p =
      Submodule.span ((normalizedNumberFieldAdelicStructure K).rationalLocalRing
        (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p)) {π ^ (-b p)} := by
  rw [normalizedPrimeLocalizedFractionalIdeal_eq_span_uniformizer_zpow _
    (finiteSupportValuationFractionalIdeal_ne_zero b hb) p π hπ,
    finiteSupportValuationFractionalIdeal_count]

/-- Every actual localized nonzero fractional ideal is explicitly free of rank one. -/
def normalizedPrimeLocalizedFractionalIdealEquiv
    (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hJ : J ≠ 0)
    (p : HeightOneSpectrum (𝓞 K)) :
    (normalizedNumberFieldAdelicStructure K).rationalLocalRing
      (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p) ≃ₗ[
        (normalizedNumberFieldAdelicStructure K).rationalLocalRing
          (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p)]
      normalizedPrimeLocalizedFractionalIdeal J p := by
  let π := (p.valuation_exists_uniformizer K).choose
  have hπ : p.valuation K π = WithZero.exp (-1 : ℤ) :=
    (p.valuation_exists_uniformizer K).choose_spec
  have hπne : π ≠ 0 := (p.valuation K).ne_zero_iff.mp (hπ ▸ WithZero.exp_ne_zero)
  exact (LinearEquiv.toSpanNonzeroSingleton _ K (π ^ FractionalIdeal.count K p J)
    (zpow_ne_zero _ hπne)).trans (LinearEquiv.ofEq _ _
      (normalizedPrimeLocalizedFractionalIdeal_eq_span_uniformizer_zpow J hJ p π hπ).symm)

/-- Every literal actual normalized finite place has the source localization formula. -/
theorem exists_normalizedFinitePlace_valuationModule_localization
    (b : (normalizedNumberFieldAdelicStructure K).Ωfin → ℤ)
    (hb : {ω | b ω ≠ 0}.Finite)
    (ω : (normalizedNumberFieldAdelicStructure K).Ωfin) :
    ∃ π : K,
      (normalizedPrimeEquivFinite.symm ω).valuation K π = WithZero.exp (-1 : ℤ) ∧
      Submodule.span ((normalizedNumberFieldAdelicStructure K).rationalLocalRing ω.1 ω.2)
        (valuationModule (K := K) (fun p => b (normalizedPrimeEquivFinite p)) : Set K) =
      Submodule.span ((normalizedNumberFieldAdelicStructure K).rationalLocalRing ω.1 ω.2)
        {π ^ (-b ω)} := by
  obtain ⟨p, rfl⟩ := normalizedPrimeEquivFinite.surjective ω
  have hpull : {p | b (normalizedPrimeEquivFinite p) ≠ 0}.Finite :=
    hb.preimage (f := normalizedPrimeEquivFinite (K := K))
      normalizedPrimeEquivFinite.injective.injOn
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer K
  refine ⟨π, by simpa only [Equiv.symm_apply_apply] using hπ, ?_⟩
  exact normalizedPrimeLocalized_finiteSupportValuationFractionalIdeal_eq
    (fun p => b (normalizedPrimeEquivFinite p)) hpull p π hπ

end ArakelovGeometry.FiniteValuation
