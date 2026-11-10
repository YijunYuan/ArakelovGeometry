/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldLatticeGaugeDomination
public import ArakelovGeometry.NumberTheory.NumberFieldBoundedIndexElement
public import Mathlib.RingTheory.FractionalIdeal.Norm

/-!
# Actual prime factors and cyclic line indices

Arithmetic identities for the literal ideal quotient used in the
finite-place contribution of source Proposition 4.4.10.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors WithZero TensorProduct

noncomputable section

namespace ArakelovGeometry.NumberFieldLineIndex

open AdelicStructure ActualPrimeIndexing

variable {K : Type*} [Field K] [NumberField K]

/-- Factorization of an actual ideal gives its logarithmic norm, with
the sum taken over the actual height-one primes. -/
theorem ideal_log_absNorm_eq_tsum (I : (Ideal (𝓞 K))⁰) :
    Real.log (Ideal.absNorm (I : Ideal (𝓞 K))) =
      ∑' p : HeightOneSpectrum (𝓞 K), Real.log (Ideal.absNorm (p.maxPowDividing I)) := by
  classical
  have hI : (I : Ideal (𝓞 K)) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.property
  have hfinite : {p : HeightOneSpectrum (𝓞 K) |
      p.maxPowDividing (I : Ideal (𝓞 K)) ≠ 1}.Finite := Ideal.hasFiniteMulSupport hI
  let s := hfinite.toFinset
  have hp (p : HeightOneSpectrum (𝓞 K)) : p.maxPowDividing I ≠ 0 := by
    rw [p.maxPowDividing_eq_pow_multiset_count hI]
    exact pow_ne_zero _ p.ne_bot
  have hprod : ∏ p ∈ s, p.maxPowDividing I = (I : Ideal (𝓞 K)) := by
    exact (finprod_eq_finsetProd_of_mulSupport_subset (s := s)
      (fun p : HeightOneSpectrum (𝓞 K) => p.maxPowDividing (I : Ideal (𝓞 K)))
      (by intro p hp; exact hfinite.mem_toFinset.mpr hp)).symm.trans
        (Ideal.finprod_heightOneSpectrum_factorization hI)
  have hnorm : (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) =
      ∏ p ∈ s, (Ideal.absNorm (p.maxPowDividing I) : ℝ) := by
    calc
      _ = (Ideal.absNorm (∏ p ∈ s, p.maxPowDividing (I : Ideal (𝓞 K))) : ℝ) :=
        congrArg (fun J : Ideal (𝓞 K) => (Ideal.absNorm J : ℝ)) hprod.symm
      _ = _ := by rw [map_prod, Nat.cast_prod]
  rw [hnorm, Real.log_prod (fun p _ => by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr (hp p)))]
  exact (tsum_eq_sum (s := s) (fun p hps => by
    have hpf : p.maxPowDividing (I : Ideal (𝓞 K)) = 1 := by
      simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hps
    simp only [hpf, map_one, Nat.cast_one, Real.log_one])).symm

/-- Prime factorization of the cardinality of the literal cyclic ideal
quotient; the quotient cardinality is produced arithmetically. -/
theorem ideal_cyclicQuotient_log_card_eq_tsum (I J : (Ideal (𝓞 K))⁰)
    (x : (I : Ideal (𝓞 K)))
    (hprod : (I : Ideal (𝓞 K)) * J = Ideal.span {(x : 𝓞 K)}) :
    Real.log (Nat.card ((I : Ideal (𝓞 K)) ⧸ Submodule.span (𝓞 K) {x})) =
      ∑' p : HeightOneSpectrum (𝓞 K), Real.log (Ideal.absNorm (p.maxPowDividing J)) := by
  rw [NumberFieldBoundedIndex.ideal_cyclicQuotient_card_of_product K I J x hprod]
  exact ideal_log_absNorm_eq_tsum J

/-- Actual rationally normalized masses cancel the actual local
logarithmic scales in the prime factorization of a nonzero ideal. -/
theorem ideal_log_absNorm_eq_normalized_weighted_tsum (I : (Ideal (𝓞 K))⁰) :
    Real.log (Ideal.absNorm (I : Ideal (𝓞 K))) =
      ∑' p : HeightOneSpectrum (𝓞 K),
        (normalizedNumberFieldAdelicStructure K).v.real {normalizedPrimeParameter p} *
          normalizedPlaceLogScale (normalizedPrimeParameter p) *
            ((Associates.mk p.asIdeal).count (Associates.mk (I : Ideal (𝓞 K))).factors : ℝ) := by
  rw [ideal_log_absNorm_eq_tsum I]
  apply tsum_congr
  intro p
  rw [normalized_weighted_prime_log_scale]
  change Real.log (Ideal.absNorm (p.asIdeal ^
    (Associates.mk p.asIdeal).count (Associates.mk (I : Ideal (𝓞 K))).factors)) = _
  rw [map_pow, Nat.cast_pow, Real.log_pow]
  ring

/-- The actual completion-degree weighted prime orders recover the
literal cyclic quotient index produced by principalization. -/
theorem ideal_cyclicQuotient_log_card_eq_normalized_weighted_tsum
    (I J : (Ideal (𝓞 K))⁰) (x : (I : Ideal (𝓞 K)))
    (hprod : (I : Ideal (𝓞 K)) * J = Ideal.span {(x : 𝓞 K)}) :
    Real.log (Nat.card ((I : Ideal (𝓞 K)) ⧸ Submodule.span (𝓞 K) {x})) =
      ∑' p : HeightOneSpectrum (𝓞 K),
        (normalizedNumberFieldAdelicStructure K).v.real {normalizedPrimeParameter p} *
          normalizedPlaceLogScale (normalizedPrimeParameter p) *
            ((Associates.mk p.asIdeal).count (Associates.mk (J : Ideal (𝓞 K))).factors : ℝ) := by
  rw [NumberFieldBoundedIndex.ideal_cyclicQuotient_card_of_product K I J x hprod]
  exact ideal_log_absNorm_eq_normalized_weighted_tsum J

/-- The index of an actual element in any actual nonzero ideal is the
ratio of the principal ideal norm to the ambient ideal norm. -/
theorem ideal_cyclicQuotient_card_mul_absNorm (I : Ideal (𝓞 K)) (x : I) :
    Nat.card (I ⧸ Submodule.span (𝓞 K) {x}) * Ideal.absNorm I =
      Ideal.absNorm (Ideal.span {(x : 𝓞 K)}) := by
  rw [NumberFieldBoundedIndex.ideal_cyclicQuotient_card_eq_relIndex,
    Ideal.absNorm_eq_index, Ideal.absNorm_eq_index]
  exact AddSubgroup.relIndex_mul_index
    (show (Ideal.span {(x : 𝓞 K)}).toAddSubgroup ≤ I.toAddSubgroup from
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr x.property))

theorem ideal_cyclicQuotient_log_card (I : (Ideal (𝓞 K))⁰)
    (x : (I : Ideal (𝓞 K))) (hx : x ≠ 0) :
    Real.log (Nat.card ((I : Ideal (𝓞 K)) ⧸ Submodule.span (𝓞 K) {x})) =
      Real.log (Ideal.absNorm (Ideal.span {(x : 𝓞 K)})) -
        Real.log (Ideal.absNorm (I : Ideal (𝓞 K))) := by
  have hxR : (x : 𝓞 K) ≠ 0 := fun h => hx (Subtype.ext h)
  have hI : Ideal.absNorm (I : Ideal (𝓞 K)) ≠ 0 :=
    Ideal.absNorm_ne_zero_of_nonZeroDivisors I
  have hxN : Ideal.absNorm (Ideal.span {(x : 𝓞 K)}) ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr (by simpa using hxR)
  have hcard := ideal_cyclicQuotient_card_mul_absNorm (I : Ideal (𝓞 K)) x
  have hc : Nat.card ((I : Ideal (𝓞 K)) ⧸ Submodule.span (𝓞 K) {x}) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hcard
    exact hxN hcard.symm
  have hreal : (Nat.card ((I : Ideal (𝓞 K)) ⧸ Submodule.span (𝓞 K) {x}) : ℝ) *
      Ideal.absNorm (I : Ideal (𝓞 K)) = Ideal.absNorm (Ideal.span {(x : 𝓞 K)}) := by
    exact_mod_cast hcard
  have hlog := congrArg Real.log hreal
  rw [Real.log_mul (Nat.cast_ne_zero.mpr hc) (Nat.cast_ne_zero.mpr hI)] at hlog
  linarith

/-- Clearing a real denominator identifies the literal fractional-ideal
quotient index with the quotient of actual absolute ideal norms. -/
theorem fractionalIdeal_cyclicQuotient_log_card
    (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0)
    (x : J.val) (hx : x ≠ 0) :
    Real.log (Nat.card (J.val ⧸ Submodule.span (𝓞 K) {x})) =
      Real.log (FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) : ℝ) -
        Real.log (FractionalIdeal.absNorm J : ℝ) := by
  have hd : (J.den : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero _
  let e : J.val ≃ₗ[𝓞 K] J.num := FractionalIdeal.equivNum hd
  let I : (Ideal (𝓞 K))⁰ :=
    ⟨J.num, mem_nonZeroDivisors_of_ne_zero (FractionalIdeal.num_eq_zero_iff.not.mpr hJ)⟩
  have hy : e x ≠ 0 := by
    intro h
    apply hx
    exact e.injective (h.trans (map_zero e).symm)
  have hcard := NumberFieldBoundedIndex.cyclicQuotient_card_eq e x
  rw [hcard, ideal_cyclicQuotient_log_card I (e x) hy]
  have hxK : (x : K) ≠ 0 := fun h => hx (Subtype.ext h)
  have hNX : FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) ≠ 0 :=
    FractionalIdeal.absNorm_eq_zero_iff.not.mpr
      (FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hxK)
  have hND : Ideal.absNorm (Ideal.span {(J.den : 𝓞 K)}) ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr (by simp [hd])
  have hNI : Ideal.absNorm J.num ≠ 0 := Ideal.absNorm_ne_zero_of_nonZeroDivisors I
  have heq : algebraMap (𝓞 K) K (e x : 𝓞 K) =
      algebraMap (𝓞 K) K (J.den : 𝓞 K) * (x : K) := by
    exact FractionalIdeal.equivNum_apply hd x
  have hny : (Ideal.absNorm (Ideal.span {(e x : 𝓞 K)}) : ℚ) =
      Ideal.absNorm (Ideal.span {(J.den : 𝓞 K)}) *
        FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) := by
    rw [← FractionalIdeal.coeIdeal_absNorm (K := K),
      FractionalIdeal.coeIdeal_span_singleton, heq,
      map_mul, map_mul,
      ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_absNorm]
  have hnyR : (Ideal.absNorm (Ideal.span {(e x : 𝓞 K)}) : ℝ) =
      Ideal.absNorm (Ideal.span {(J.den : 𝓞 K)}) *
        (FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) : ℝ) := by
    exact_mod_cast hny
  have hnJ : (FractionalIdeal.absNorm J : ℝ) = (Ideal.absNorm J.num : ℝ) /
      Ideal.absNorm (Ideal.span {(J.den : 𝓞 K)}) := by
    rw [FractionalIdeal.absNorm_eq, Ideal.absNorm_span_singleton]
    push_cast
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hnyR, Real.log_mul (Nat.cast_ne_zero.mpr hND) (Rat.cast_ne_zero.mpr hNX),
    hnJ, Real.log_div (Nat.cast_ne_zero.mpr hNI) (Nat.cast_ne_zero.mpr hND)]
  dsimp only [I]
  ring

private theorem ideal_le_prime_pow_iff (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (p : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    I ≤ p.asIdeal ^ n ↔ n ≤ (Associates.mk p.asIdeal).count (Associates.mk I).factors := by
  classical
  rw [← Ideal.dvd_iff_le, ← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
  exact Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hI) p.associates_irreducible

/-- The actual prime order of a nonzero ideal is attained by an actual
element of that ideal, rather than merely supplying a bound. -/
theorem exists_ideal_member_attaining_valuation (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (p : HeightOneSpectrum (𝓞 K)) :
    ∃ a ∈ I, a ≠ 0 ∧ p.valuation K (algebraMap (𝓞 K) K a) =
      WithZero.exp (-((Associates.mk p.asIdeal).count (Associates.mk I).factors : ℤ)) := by
  classical
  let n := (Associates.mk p.asIdeal).count (Associates.mk I).factors
  have hle : I ≤ p.asIdeal ^ n := (ideal_le_prime_pow_iff I hI p n).mpr le_rfl
  have hnot : ¬ I ≤ p.asIdeal ^ (n + 1) := by
    rw [ideal_le_prime_pow_iff I hI p (n + 1)]
    omega
  obtain ⟨a, ha, hanext⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have ha0 : a ≠ 0 := by intro h; exact hanext (h ▸ Ideal.zero_mem _)
  refine ⟨a, ha, ha0, ?_⟩
  have hva := (p.intValuation_le_pow_iff_mem a n).mpr (hle ha)
  have hvnext := (p.intValuation_le_pow_iff_mem a (n + 1)).not.mpr hanext
  rw [p.valuation_of_algebraMap, p.intValuation_apply, p.intValuationDef_if_neg ha0]
  rw [p.intValuation_apply, p.intValuationDef_if_neg ha0, WithZero.exp_le_exp] at hva hvnext
  congr 1
  omega

/-- Every actual member has valuation at most the value attained at the
prime order of the nonzero ideal. -/
theorem ideal_member_valuation_le (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (p : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K} (ha : a ∈ I) :
    p.valuation K (algebraMap (𝓞 K) K a) ≤
      WithZero.exp (-((Associates.mk p.asIdeal).count (Associates.mk I).factors : ℤ)) := by
  rw [p.valuation_of_algebraMap]
  apply (p.intValuation_le_pow_iff_mem a _).mpr
  exact ((ideal_le_prime_pow_iff I hI p _).mpr le_rfl) ha

private theorem fractionalIdeal_count_num_den
    (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0) (p : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K p J =
      ((Associates.mk p.asIdeal).count (Associates.mk J.num).factors : ℤ) -
        (Associates.mk p.asIdeal).count
          (Associates.mk (Ideal.span {(J.den : 𝓞 K)})).factors := by
  have hnum : J.num ≠ 0 := FractionalIdeal.num_eq_zero_iff.not.mpr hJ
  have hd : (J.den : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero _
  have hspan : (Ideal.span {(J.den : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by simp [hd]
  have hS : FractionalIdeal.spanSingleton (𝓞 K)⁰
      (algebraMap (𝓞 K) K (J.den : 𝓞 K)) ≠ 0 := by
    rw [← FractionalIdeal.coeIdeal_span_singleton]
    exact FractionalIdeal.coeIdeal_ne_zero.mpr hspan
  have hc := FractionalIdeal.count_mul K p hS hJ
  rw [J.den_mul_self_eq_num', ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K p hnum, FractionalIdeal.count_coe K p hspan] at hc
  omega

/-- The actual fractional-ideal prime order bounds the valuation of every
literal element. -/
theorem fractionalIdeal_member_valuation_le
    (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0) (p : HeightOneSpectrum (𝓞 K))
    {a : K} (ha : a ∈ J) :
    p.valuation K a ≤ WithZero.exp (-FractionalIdeal.count K p J) := by
  by_cases ha0 : a = 0
  · simp [ha0]
  have hd : (J.den : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero _
  let e : J.val ≃ₗ[𝓞 K] J.num := FractionalIdeal.equivNum hd
  let x : J.val := ⟨a, ha⟩
  have he : algebraMap (𝓞 K) K (e x : 𝓞 K) =
      algebraMap (𝓞 K) K (J.den : 𝓞 K) * a := FractionalIdeal.equivNum_apply hd x
  have hb := ideal_member_valuation_le J.num
    (FractionalIdeal.num_eq_zero_iff.not.mpr hJ) p (e x).property
  change p.valuation K (algebraMap (𝓞 K) K (e x : 𝓞 K)) ≤ _ at hb
  rw [he, map_mul, p.valuation_of_algebraMap,
    p.intValuation_apply, p.intValuationDef_if_neg hd,
    ← WithZero.exp_log ((p.valuation K).ne_zero_iff.mpr ha0),
    ← WithZero.exp_add, WithZero.exp_le_exp] at hb
  rw [← WithZero.exp_log ((p.valuation K).ne_zero_iff.mpr ha0), WithZero.exp_le_exp,
    fractionalIdeal_count_num_den J hJ p]
  omega

/-- A fractional ideal contains an actual nonzero element attaining its
prime valuation bound. -/
theorem exists_fractionalIdeal_member_attaining_valuation
    (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0) (p : HeightOneSpectrum (𝓞 K)) :
    ∃ a ∈ J, a ≠ 0 ∧ p.valuation K a = WithZero.exp (-FractionalIdeal.count K p J) := by
  have hd : (J.den : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero _
  let e : J.val ≃ₗ[𝓞 K] J.num := FractionalIdeal.equivNum hd
  obtain ⟨a, ha, ha0, hva⟩ := exists_ideal_member_attaining_valuation J.num
    (FractionalIdeal.num_eq_zero_iff.not.mpr hJ) p
  let x := e.symm ⟨a, ha⟩
  have hx : (x : K) ≠ 0 := by
    intro h
    have hx0 : x = 0 := Subtype.ext h
    have hax := congrArg e hx0
    have hy0 : (⟨a, ha⟩ : J.num) = 0 := by
      calc
        _ = e x := (e.apply_symm_apply ⟨a, ha⟩).symm
        _ = 0 := hax.trans (map_zero e)
    exact ha0 (congrArg (fun y : J.num => (y : 𝓞 K)) hy0)
  refine ⟨x, x.property, hx, ?_⟩
  have he' : algebraMap (𝓞 K) K (e x : 𝓞 K) =
      algebraMap (𝓞 K) K (J.den : 𝓞 K) * (x : K) := FractionalIdeal.equivNum_apply hd x
  have he := congrArg (p.valuation K) he'
  simp only [x, e.apply_symm_apply, Subtype.coe_mk] at he
  rw [hva, map_mul, p.valuation_of_algebraMap,
    p.intValuation_apply, p.intValuationDef_if_neg hd] at he
  apply mul_left_cancel₀ (WithZero.exp_ne_zero (a :=
    -((Associates.mk p.asIdeal).count
      (Associates.mk (Ideal.span {(J.den : 𝓞 K)})).factors : ℤ)))
  rw [← he, ← WithZero.exp_add, fractionalIdeal_count_num_den J hJ p]
  congr 1
  omega

/-- Prime factorization of the genuine absolute norm of a fractional ideal,
with the actual normalized finite-place masses. -/
theorem fractionalIdeal_log_absNorm_eq_normalized_weighted_tsum
    (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0) :
    Real.log (FractionalIdeal.absNorm J : ℝ) =
      ∑' p : HeightOneSpectrum (𝓞 K),
        (normalizedNumberFieldAdelicStructure K).v.real {normalizedPrimeParameter p} *
          normalizedPlaceLogScale (normalizedPrimeParameter p) *
            (FractionalIdeal.count K p J : ℝ) := by
  classical
  have hfinite : {p : HeightOneSpectrum (𝓞 K) | FractionalIdeal.count K p J ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors J)
  let s := hfinite.toFinset
  let f := fun p : HeightOneSpectrum (𝓞 K) =>
    (p.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FractionalIdeal.count K p J
  have hp (p : HeightOneSpectrum (𝓞 K)) :
      (p.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr p.ne_bot
  have hprod : ∏ p ∈ s, f p = J := by
    exact (finprod_eq_finsetProd_of_mulSupport_subset (s := s) f (by
      intro p hpf
      by_contra hps
      have hc : FractionalIdeal.count K p J = 0 := by
        exact not_not.mp (fun hc => hps (hfinite.mem_toFinset.mpr hc))
      exact hpf (by simp [f, hc]))).symm.trans
        (FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ)
  have hnorm : (FractionalIdeal.absNorm J : ℝ) =
      ∏ p ∈ s, ((Ideal.absNorm p.asIdeal : ℝ) ^ FractionalIdeal.count K p J) := by
    calc
      _ = (FractionalIdeal.absNorm (∏ p ∈ s, f p) : ℝ) :=
        congrArg (fun I => (FractionalIdeal.absNorm I : ℝ)) hprod.symm
      _ = _ := by
        simp only [map_prod, Rat.cast_prod, f, map_zpow₀, Rat.cast_zpow,
          FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
  rw [hnorm, Real.log_prod (fun p _ => zpow_ne_zero _
    (Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot)))]
  simp only [Real.log_zpow]
  rw [tsum_eq_sum (s := s) (fun p hps => by
    have hc : FractionalIdeal.count K p J = 0 := by
      exact not_not.mp (fun hc => hps (hfinite.mem_toFinset.mpr hc))
    simp [hc])]
  apply Finset.sum_congr rfl
  intro p hp
  rw [normalized_weighted_prime_log_scale]
  ring

/-- The prime order of an actual principal fractional ideal is exactly
minus the additive logarithm of the actual discrete valuation. -/
theorem fractionalIdeal_count_spanSingleton
    (p : HeightOneSpectrum (𝓞 K)) {a : K} (ha : a ≠ 0) :
    FractionalIdeal.count K p (FractionalIdeal.spanSingleton (𝓞 K)⁰ a) =
      -(p.valuation K a).log := by
  let J := FractionalIdeal.spanSingleton (𝓞 K)⁰ a
  have hJ : J ≠ 0 := FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr ha
  have hamem : a ∈ J := FractionalIdeal.mem_spanSingleton_self _ _
  have hle := fractionalIdeal_member_valuation_le J hJ p hamem
  obtain ⟨b, hb, _, hvb⟩ := exists_fractionalIdeal_member_attaining_valuation J hJ p
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_spanSingleton (𝓞 K)⁰).mp hb
  have hv : p.valuation K b ≤ p.valuation K a := by
    rw [← hc, Algebra.smul_def, map_mul]
    exact (mul_le_mul' (p.valuation_le_one c) le_rfl).trans_eq (one_mul _)
  have he := le_antisymm hle (hvb ▸ hv)
  have hl := congrArg WithZero.log he
  rw [WithZero.log_exp] at hl
  change (p.valuation K a).log = -FractionalIdeal.count K p
    (FractionalIdeal.spanSingleton (𝓞 K)⁰ a) at hl
  omega

theorem fractionalIdeal_summable_normalized_weighted_count
    (J : FractionalIdeal (𝓞 K)⁰ K) :
    Summable (fun p : HeightOneSpectrum (𝓞 K) =>
      (normalizedNumberFieldAdelicStructure K).v.real {normalizedPrimeParameter p} *
        normalizedPlaceLogScale (normalizedPrimeParameter p) *
          (FractionalIdeal.count K p J : ℝ)) := by
  classical
  have hfinite : {p : HeightOneSpectrum (𝓞 K) | FractionalIdeal.count K p J ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors J)
  apply summable_of_ne_finset_zero (s := hfinite.toFinset)
  intro p hp
  have hc : FractionalIdeal.count K p J = 0 :=
    not_not.mp (fun hc => hp (hfinite.mem_toFinset.mpr hc))
  simp [hc]

/-- Actual fractional prime orders give the literal cyclic quotient
index of an actual nonzero element. -/
theorem fractionalIdeal_cyclicQuotient_log_card_eq_normalized_weighted_tsum
    (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0)
    (x : J.val) (hx : x ≠ 0) :
    Real.log (Nat.card (J.val ⧸ Submodule.span (𝓞 K) {x})) =
      ∑' p : HeightOneSpectrum (𝓞 K),
        (normalizedNumberFieldAdelicStructure K).v.real {normalizedPrimeParameter p} *
          normalizedPlaceLogScale (normalizedPrimeParameter p) *
            ((FractionalIdeal.count K p (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) : ℝ) -
              FractionalIdeal.count K p J) := by
  have hxK : (x : K) ≠ 0 := fun h => hx (Subtype.ext h)
  rw [fractionalIdeal_cyclicQuotient_log_card J hJ x hx,
    fractionalIdeal_log_absNorm_eq_normalized_weighted_tsum _
      (FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hxK),
    fractionalIdeal_log_absNorm_eq_normalized_weighted_tsum J hJ,
    ← (fractionalIdeal_summable_normalized_weighted_count _).tsum_sub
      (fractionalIdeal_summable_normalized_weighted_count J)]
  apply tsum_congr
  intro p
  ring

end ArakelovGeometry.NumberFieldLineIndex

namespace ArakelovGeometry.NormFamily

open AdelicStructure ActualPrimeIndexing NumberFieldLineIndex MeasureTheory

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- An actual pure finite norm of a nonzero rational vector is attained
by the actual normalized absolute value of a rational scalar. -/
theorem exists_normalized_scalar_norm_eq_of_globalImpurity_eq_zero
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) (hξ : ξ.IsUltrametric)
    (hσ : ξ.globalImpurity = 0) (p : HeightOneSpectrum (𝓞 K)) {x : E} (hx : x ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ ξ.norm (normalizedPrimeParameter p) (1 ⊗ₜ[K] x) =
      (normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p) a := by
  classical
  let S := normalizedNumberFieldAdelicStructure K
  let ω := normalizedPrimeParameter p
  have hf := normalizedPrimeParameter_mem_fin p
  let b := ξ.rationalLocalUnitBallGenericBasis ω hf
    (NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω)) hξ
  have hn : ξ.norm ω (1 ⊗ₜ[K] x) = ‖fun i => S.ϕ ω (b.equivFun x i)‖ := by
    rw [← (ξ.globalImpurity_eq_zero_iff.mp hσ) ω hf,
      ξ.completedUnitBallGauge_eq_basisNorm ω hf _ hξ]
    exact ofBasis_norm_rational b ω x
  have hi : ∃ i, b.equivFun x i ≠ 0 := by
    by_contra! h
    apply hx
    apply b.equivFun.injective
    ext i
    simp only [h i, map_zero, Pi.zero_apply]
  obtain ⟨i, _⟩ := hi
  let : Nonempty (Fin (Module.finrank (S.rationalLocalRing ω hf)
      (ξ.rationalUnitBallModule ω hf hξ))) := ⟨i⟩
  obtain ⟨j, hj⟩ := (IsGreatest.pi_norm (fun i => S.ϕ ω (b.equivFun x i))).1
  have hj' : S.ϕ ω (b.equivFun x j) = ξ.norm ω (1 ⊗ₜ[K] x) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (apply_nonneg _ _), ← hn] using hj
  refine ⟨b.equivFun x j, ?_, hj'.symm⟩
  intro h
  have hpos := ξ.norm_rational_pos ω hx
  rw [h, map_zero] at hj'
  exact hpos.ne' hj'.symm

/-- The actual coordinate fractional ideal of the literal global ball
under a field-linear coordinate of the actual line. -/
def normalizedLineCoordinateIdeal
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) (hξ : ξ.IsUltrametric)
    (hfg : (ξ.globalUnitBallModule hξ).FG) (e : K ≃ₗ[K] E) :
    FractionalIdeal (𝓞 K)⁰ K :=
  ⟨(ξ.globalUnitBallModule hξ).map (e.symm.toLinearMap.restrictScalars (𝓞 K)),
    FractionalIdeal.isFractional_of_fg (hfg.map _)⟩

omit [FiniteDimensional K E] in
theorem mem_normalizedLineCoordinateIdeal
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) (hξ : ξ.IsUltrametric)
    (hfg : (ξ.globalUnitBallModule hξ).FG) (e : K ≃ₗ[K] E) (a : K) :
    a ∈ ξ.normalizedLineCoordinateIdeal hξ hfg e ↔ e a ∈ ξ.globalUnitBall := by
  change a ∈ (ξ.globalUnitBallModule hξ).map
    (e.symm.toLinearMap.restrictScalars (𝓞 K)) ↔ _
  constructor
  · rintro ⟨x, hx, ha⟩
    have he : e a = x := by rw [← ha]; exact e.apply_symm_apply x
    exact he ▸ hx
  · intro hx
    exact ⟨e a, hx, e.symm_apply_apply a⟩

omit [FiniteDimensional K E] in
theorem normalizedLineCoordinateIdeal_ne_zero
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) (hξ : ξ.IsUltrametric)
    (hfinite : ξ.HasFiniteNormExceptions) (hfg : (ξ.globalUnitBallModule hξ).FG)
    (e : K ≃ₗ[K] E) : ξ.normalizedLineCoordinateIdeal hξ hfg e ≠ 0 := by
  obtain ⟨a, ha, hax⟩ := hfinite.exists_integral_smul_mem_globalUnitBall
    (fun ω _ => NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω)) (e 1)
  have hmem : algebraMap (𝓞 K) K a ∈ ξ.normalizedLineCoordinateIdeal hξ hfg e := by
    rw [ξ.mem_normalizedLineCoordinateIdeal]
    simpa only [← e.map_smul, smul_eq_mul, mul_one] using hax
  intro h
  have haK : algebraMap (𝓞 K) K a = 0 := by
    simpa only [h, FractionalIdeal.mem_zero_iff] using hmem
  exact ha ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mp haK)

/-- Pure finite norms and genuine coherence recover the prime order of
the actual coordinate ideal of the literal global ball. -/
theorem normalizedLineCoordinateIdeal_logNorm_one
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) (hξ : ξ.IsUltrametric)
    (hfinite : ξ.HasFiniteNormExceptions) (hfg : (ξ.globalUnitBallModule hξ).FG)
    (hσ : ξ.globalImpurity = 0) (e : K ≃ₗ[K] E) (p : HeightOneSpectrum (𝓞 K)) :
    ξ.logNorm (e 1) (normalizedPrimeParameter p) =
      normalizedPrimeLogScale p * FractionalIdeal.count K p
        (ξ.normalizedLineCoordinateIdeal hξ hfg e) := by
  let J := ξ.normalizedLineCoordinateIdeal hξ hfg e
  have hJ : J ≠ 0 := ξ.normalizedLineCoordinateIdeal_ne_zero hξ hfinite hfg e
  have he1 : e 1 ≠ 0 := by
    intro h
    exact one_ne_zero (e.injective (h.trans (map_zero e).symm))
  have hγ := normalizedPrimeLogScale_pos p
  obtain ⟨a, ha, ha0, hva⟩ := exists_fractionalIdeal_member_attaining_valuation J hJ p
  have hamem : a • e 1 ∈ ξ.globalUnitBall := by
    have h := (ξ.mem_normalizedLineCoordinateIdeal hξ hfg e a).mp ha
    simpa only [← e.map_smul, smul_eq_mul, mul_one] using h
  have hlogle : ξ.logNorm (a • e 1) (normalizedPrimeParameter p) ≤ 0 := by
    exact Real.log_nonpos (ξ.norm_nonneg _ _)
      (hamem _ (normalizedPrimeParameter_mem_fin p))
  rw [ξ.logNorm_smul ha0 he1, normalizedPrime_log_value p ha0,
    hva, WithZero.log_exp, Int.cast_neg] at hlogle
  obtain ⟨b, hb, hbnorm⟩ :=
    ξ.exists_normalized_scalar_norm_eq_of_globalImpurity_eq_zero hξ hσ p he1
  have hlocal : b⁻¹ • e 1 ∈ ξ.rationalUnitBall (normalizedPrimeParameter p) := by
    change ξ.norm _ (1 ⊗ₜ[K] (b⁻¹ • e 1)) ≤ 1
    rw [ξ.norm_rational_smul, hbnorm, map_inv₀, inv_mul_cancel₀
      ((((normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p)).pos hb).ne')]
  obtain ⟨d, hd, hdy⟩ := hfinite.exists_primeCompl_smul_mem_globalUnitBall p hlocal
  have hdv : p.valuation K (algebraMap (𝓞 K) K d) = 1 := by
    rw [p.valuation_of_algebraMap]
    exact p.intValuation_eq_one_iff.mpr hd
  have hcoeff : algebraMap (𝓞 K) K d * b⁻¹ ∈ J := by
    rw [ξ.mem_normalizedLineCoordinateIdeal]
    simpa only [mul_smul, ← e.map_smul, smul_eq_mul, mul_one] using hdy
  have hv := fractionalIdeal_member_valuation_le J hJ p hcoeff
  rw [map_mul, map_inv₀, hdv, one_mul] at hv
  have hvb : p.valuation K b ≠ 0 := (p.valuation K).ne_zero_iff.mpr hb
  rw [← WithZero.exp_log hvb, ← WithZero.exp_neg, WithZero.exp_le_exp] at hv
  have hvR : (FractionalIdeal.count K p J : ℝ) ≤ ((p.valuation K b).log : ℝ) := by
    exact_mod_cast (neg_le_neg_iff.mp hv)
  have hnorm : ξ.logNorm (e 1) (normalizedPrimeParameter p) =
      normalizedPrimeLogScale p * ((p.valuation K b).log : ℝ) := by
    exact (congrArg Real.log hbnorm).trans (normalizedPrime_log_value p hb)
  exact le_antisymm (by linarith)
    (hnorm ▸ mul_le_mul_of_nonneg_left hvR hγ.le)

/-- On a genuine pure coherent line, the finite logarithmic norm of an
actual nonzero vector reads the actual coordinate-ideal prime order. -/
theorem normalizedLineCoordinateIdeal_logNorm
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) (hξ : ξ.IsUltrametric)
    (hfinite : ξ.HasFiniteNormExceptions) (hfg : (ξ.globalUnitBallModule hξ).FG)
    (hσ : ξ.globalImpurity = 0) (e : K ≃ₗ[K] E) (p : HeightOneSpectrum (𝓞 K))
    {x : E} (hx : x ≠ 0) :
    ξ.logNorm x (normalizedPrimeParameter p) = normalizedPrimeLogScale p *
      (((p.valuation K (e.symm x)).log : ℝ) +
        FractionalIdeal.count K p (ξ.normalizedLineCoordinateIdeal hξ hfg e)) := by
  have ha : e.symm x ≠ 0 := fun h => hx (e.symm.injective (h.trans (map_zero e.symm).symm))
  have he1 : e 1 ≠ 0 := fun h => one_ne_zero (e.injective (h.trans (map_zero e).symm))
  have hx' : x = e.symm x • e 1 := by
    rw [← e.map_smul, smul_eq_mul, mul_one, e.apply_symm_apply]
  conv_lhs => rw [hx']
  rw [ξ.logNorm_smul ha he1, normalizedPrime_log_value p ha,
    ξ.normalizedLineCoordinateIdeal_logNorm_one hξ hfinite hfg hσ e p]
  ring

/-- The actual normalized finite-place sum of minus log norms equals
the logarithm of the literal global-ball cyclic quotient index. -/
theorem normalizedLineGlobalUnitBall_finite_log_index
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) (hξ : ξ.IsUltrametric)
    (hfinite : ξ.HasFiniteNormExceptions) (hfg : (ξ.globalUnitBallModule hξ).FG)
    (hσ : ξ.globalImpurity = 0) (hrank : Module.finrank K E = 1)
    (x : ξ.globalUnitBallModule hξ) (hx : x ≠ 0) :
    (∑' p : HeightOneSpectrum (𝓞 K),
      (normalizedNumberFieldAdelicStructure K).v.real {normalizedPrimeParameter p} *
        (-ξ.logNorm (x : E) (normalizedPrimeParameter p))) =
      Real.log (Nat.card ((ξ.globalUnitBallModule hξ) ⧸ Submodule.span (𝓞 K) {x})) := by
  classical
  let e : K ≃ₗ[K] E := (Module.nonempty_linearEquiv_of_finrank_eq_one hrank).some
  let J := ξ.normalizedLineCoordinateIdeal hξ hfg e
  let g : (ξ.globalUnitBallModule hξ) ≃ₗ[𝓞 K] J.val :=
    Submodule.equivMapOfInjective (e.symm.toLinearMap.restrictScalars (𝓞 K))
      e.symm.injective (ξ.globalUnitBallModule hξ)
  have hJ : J ≠ 0 := ξ.normalizedLineCoordinateIdeal_ne_zero hξ hfinite hfg e
  have hgx : g x ≠ 0 := fun h => hx (g.injective (h.trans (map_zero g).symm))
  have hxE : (x : E) ≠ 0 := fun h => hx (Subtype.ext h)
  have ha : e.symm (x : E) ≠ 0 :=
    fun h => hxE (e.symm.injective (h.trans (map_zero e.symm).symm))
  rw [NumberFieldBoundedIndex.cyclicQuotient_card_eq g x,
    fractionalIdeal_cyclicQuotient_log_card_eq_normalized_weighted_tsum J hJ (g x) hgx]
  apply tsum_congr
  intro p
  have hg : (g x : K) = e.symm (x : E) := rfl
  rw [hg, fractionalIdeal_count_spanSingleton p ha,
    ξ.normalizedLineCoordinateIdeal_logNorm hξ hfinite hfg hσ e p hxE,
    normalizedPlaceLogScale_prime]
  push_cast
  ring

/-- The finite-locus integral of the actual completed logarithmic norms
is the literal cyclic quotient index; purity is used only at finite places. -/
theorem normalizedLineGlobalUnitBall_finite_integral_log_index
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) (hξ : ξ.IsUltrametric)
    (hfinite : ξ.HasFiniteNormExceptions) (hdom : ξ.IsDominated) (hm : ξ.IsMeasurable)
    (hσ : ξ.globalImpurity = 0) (hrank : Module.finrank K E = 1)
    (x : ξ.globalUnitBallModule hξ) (hx : x ≠ 0) :
    (∫ ω in (normalizedNumberFieldAdelicStructure K).Ωfin,
      -ξ.logNorm (x : E) ω ∂(normalizedNumberFieldAdelicStructure K).v) =
      Real.log (Nat.card ((ξ.globalUnitBallModule hξ) ⧸ Submodule.span (𝓞 K) {x})) := by
  classical
  let S := normalizedNumberFieldAdelicStructure K
  let : Countable S.Ω := inferInstanceAs
    (Countable {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
  let : MeasurableSingletonClass S.Ω := inferInstanceAs
    (MeasurableSingletonClass {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
  have hset : MeasurableSet S.Ωfin := by
    simpa only [Ωinf, Ωfin, Set.compl_ofPred, not_not] using S.measurableSet_Ωinf.compl
  have hint : Integrable (S.Ωfin.indicator (fun ω => -ξ.logNorm (x : E) ω)) S.v :=
    ((hdom.integrable_logNorm hm (x : E)).neg).indicator hset
  rw [← integral_indicator hset, integral_countable hint]
  let f := fun ω : S.Ω => S.v.real {ω} • S.Ωfin.indicator (fun ω => -ξ.logNorm (x : E) ω) ω
  have hsupport : Function.support f ⊆ S.Ωfin := by
    intro ω hω
    by_contra hf
    exact hω (by simp [f, Set.indicator_of_notMem hf])
  change ∑' ω : S.Ω, f ω = _
  rw [← tsum_subtype_eq_of_support_subset hsupport,
    ← (normalizedPrimeEquivFinite (K := K)).tsum_eq]
  have heq (p : HeightOneSpectrum (𝓞 K)) :
      f (normalizedPrimeEquivFinite p) =
        S.v.real {normalizedPrimeParameter p} *
          (-ξ.logNorm (x : E) (normalizedPrimeParameter p)) := by
    change S.v.real {normalizedPrimeParameter p} *
      S.Ωfin.indicator (fun ω => -ξ.logNorm (x : E) ω) (normalizedPrimeParameter p) = _
    rw [Set.indicator_of_mem (normalizedPrimeParameter_mem_fin p)]
  simp_rw [heq]
  exact ξ.normalizedLineGlobalUnitBall_finite_log_index hξ hfinite
    (hdom.fg_normalizedGlobalUnitBallModule hξ) hσ hrank x hx

/-- The genuine vector degree on an actual pure coherent line separates
into the actual finite cyclic index and the actual infinite-locus integral. -/
theorem normalizedLineGlobalUnitBall_vectorDegree
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) (hξ : ξ.IsUltrametric)
    (hfinite : ξ.HasFiniteNormExceptions) (hdom : ξ.IsDominated) (hm : ξ.IsMeasurable)
    (hσ : ξ.globalImpurity = 0) (hrank : Module.finrank K E = 1)
    (x : ξ.globalUnitBallModule hξ) (hx : x ≠ 0) :
    ξ.vectorDegree hdom hm ⟨(x : E), fun h => hx (Subtype.ext h)⟩ =
      Real.log (Nat.card ((ξ.globalUnitBallModule hξ) ⧸ Submodule.span (𝓞 K) {x})) -
        ∫ ω in (normalizedNumberFieldAdelicStructure K).Ωinf,
          ξ.logNorm (x : E) ω ∂(normalizedNumberFieldAdelicStructure K).v := by
  let S := normalizedNumberFieldAdelicStructure K
  have hsplit := integral_add_compl S.measurableSet_Ωinf
    (hdom.integrable_logNorm hm (x : E))
  have hfin := ξ.normalizedLineGlobalUnitBall_finite_integral_log_index
    hξ hfinite hdom hm hσ hrank x hx
  rw [integral_neg] at hfin
  have hcompl : S.Ωinfᶜ = S.Ωfin := by simp only [Ωinf, Ωfin, Set.compl_ofPred, not_not]
  rw [hcompl] at hsplit
  rw [ξ.vectorDegree_eq_neg_integral]
  linarith

end ArakelovGeometry.NormFamily
