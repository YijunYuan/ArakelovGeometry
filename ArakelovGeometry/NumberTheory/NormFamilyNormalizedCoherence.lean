/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NormFamilyNormalizedGlobalFiniteGeneration

/-!
# Actual local reconstruction from source coherence

The genuine finite-exception hypothesis produces integral denominators outside
each actual finite prime. The literal global unit-ball module then localizes
to the literal rational local unit-ball module of the actual normalized curve.
-/

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct BigOperators

noncomputable section

namespace ArakelovGeometry.NormFamily

open AdelicStructure ActualPrimeIndexing

variable {K : Type*} [Field K] [NumberField K]
  {E : Type*} [AddCommGroup E] [Module K E]

private abbrev S := normalizedNumberFieldAdelicStructure K

/-- The actual normalized prime value is equivalent to the actual finite value. -/
theorem normalizedPrimeValue_isEquiv (p : HeightOneSpectrum (𝓞 K)) :
    ((S (K := K)).ϕ (normalizedPrimeParameter p)).IsEquiv (FinitePlace.mk p).val :=
  Quotient.eq'.mp (normalizedPlaceValue_class (normalizedPrimeParameter p))

/-- The accepted isolated integer contracts at the actual normalized prime and
has value one at every other actual normalized prime. -/
theorem exists_normalized_integral_isolated_prime (q : HeightOneSpectrum (𝓞 K)) :
    ∃ f : 𝓞 K, f ≠ 0 ∧
      (S (K := K)).ϕ (normalizedPrimeParameter q) (algebraMap (𝓞 K) K f) < 1 ∧
      ∀ p : HeightOneSpectrum (𝓞 K), p ≠ q →
        (S (K := K)).ϕ (normalizedPrimeParameter p) (algebraMap (𝓞 K) K f) = 1 := by
  obtain ⟨f, hf, hq, hother⟩ := exists_integral_isolated_finitePlace K (FinitePlace.mk q)
  refine ⟨f, hf, (normalizedPrimeValue_isEquiv q).lt_one_iff.mpr hq, ?_⟩
  intro p hp
  apply (normalizedPrimeValue_isEquiv p).eq_one_iff.mpr
  exact hother (FinitePlace.mk p) (fun h => hp (FinitePlace.mk_eq_iff.mp h))

/-- A power of an actual isolated integer absorbs a vector at a chosen prime
while keeping its denominator outside a different actual prime. -/
theorem exists_integral_smul_mem_rationalUnitBall_primeCompl
    (ξ : NormFamily (S (K := K)) E) (p q : HeightOneSpectrum (𝓞 K)) (hqp : q ≠ p)
    (x : E) :
    ∃ a : 𝓞 K, a ∈ p.asIdeal.primeCompl ∧
      algebraMap (𝓞 K) K a • x ∈ ξ.rationalUnitBall (normalizedPrimeParameter q) := by
  obtain ⟨f, _, hfq, hother⟩ := exists_normalized_integral_isolated_prime q
  obtain ⟨n, hn⟩ := ξ.exists_pow_smul_mem_rationalUnitBall
    (normalizedPrimeParameter q) hfq x
  have hfone : (FinitePlace.mk p) (algebraMap (𝓞 K) K f) = 1 :=
    (normalizedPrimeValue_isEquiv p).eq_one_iff.mp (hother p hqp.symm)
  have hfn : (FinitePlace.mk p) (algebraMap (𝓞 K) K (f ^ n)) = 1 := by
    rw [map_pow, map_pow, hfone, one_pow]
  have hout : f ^ n ∉ p.asIdeal := by
    apply (FinitePlace.norm_eq_one_iff_notMem K p (f ^ n)).mp
    rwa [← FinitePlace.norm_embedding_eq, FinitePlace.maximalIdeal_mk] at hfn
  exact ⟨f ^ n, hout, by simpa only [map_pow] using hn⟩

/-- Products of the produced prime-complement denominators absorb a vector
at every prime of a finite set avoiding the prescribed prime. -/
theorem exists_integral_smul_mem_rationalUnitBall_on_finset_primeCompl
    (ξ : NormFamily (S (K := K)) E) (p : HeightOneSpectrum (𝓞 K))
    (s : Finset (HeightOneSpectrum (𝓞 K))) (hs : ∀ q ∈ s, q ≠ p) (x : E) :
    ∃ a : 𝓞 K, a ∈ p.asIdeal.primeCompl ∧ ∀ q ∈ s,
      algebraMap (𝓞 K) K a • x ∈ ξ.rationalUnitBall (normalizedPrimeParameter q) := by
  classical
  choose a ha hball using fun q : s =>
    ξ.exists_integral_smul_mem_rationalUnitBall_primeCompl p q.1 (hs q.1 q.2) x
  let d := ∏ q : s, a q
  refine ⟨d, p.asIdeal.primeCompl.prod_mem (fun q _ => ha q), ?_⟩
  intro q hq
  obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem a (Finset.mem_univ (⟨q, hq⟩ : s))
  have hd : d = r * a ⟨q, hq⟩ := hr.trans (mul_comm _ _)
  have hrabs := NumberField.abs_le_one_of_isIntegral (normalizedPrimeParameter_mem_fin q)
    (NumberField.RingOfIntegers.isIntegral_coe r)
  change ξ.norm (normalizedPrimeParameter q) (1 ⊗ₜ[K] (algebraMap (𝓞 K) K d • x)) ≤ 1
  rw [hd, map_mul, ← smul_smul, ξ.norm_rational_smul]
  exact (mul_le_mul hrabs (hball ⟨q, hq⟩) (ξ.norm_nonneg _ _) zero_le_one).trans_eq
    (mul_one 1)

/-- Source coherence gives a genuine denominator outside the actual prime
carrying every actual local unit-ball vector into the literal global ball. -/
theorem HasFiniteNormExceptions.exists_primeCompl_smul_mem_globalUnitBall
    {ξ : NormFamily (S (K := K)) E} (hfinite : ξ.HasFiniteNormExceptions)
    (p : HeightOneSpectrum (𝓞 K)) {x : E}
    (hx : x ∈ ξ.rationalUnitBall (normalizedPrimeParameter p)) :
    ∃ a : 𝓞 K, a ∈ p.asIdeal.primeCompl ∧
      algebraMap (𝓞 K) K a • x ∈ ξ.globalUnitBall := by
  classical
  have hbad : {q : HeightOneSpectrum (𝓞 K) |
      1 < ξ.norm (normalizedPrimeParameter q) (1 ⊗ₜ[K] x)}.Finite := by
    apply ((hfinite x).preimage normalizedPrimeParameter_injective.injOn).subset
    intro q hq
    exact ⟨normalizedPrimeParameter_mem_fin q, hq⟩
  let s := hbad.toFinset
  obtain ⟨a, ha, hball⟩ := ξ.exists_integral_smul_mem_rationalUnitBall_on_finset_primeCompl
    p s (fun q hq hqp => by
      have hbadq := hbad.mem_toFinset.mp hq
      subst q
      change 1 < ξ.norm (normalizedPrimeParameter p) (1 ⊗ₜ[K] x) at hbadq
      exact (not_lt_of_ge hx) hbadq) x
  refine ⟨a, ha, fun ω hω => ?_⟩
  obtain ⟨q, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
  by_cases hq : q ∈ s
  · exact hball q hq
  · have hxq : x ∈ ξ.rationalUnitBall (normalizedPrimeParameter q) := by
      by_contra hnot
      apply hq
      apply hbad.mem_toFinset.mpr
      change 1 < ξ.norm (normalizedPrimeParameter q) (1 ⊗ₜ[K] x)
      exact not_le.mp hnot
    change ξ.norm (normalizedPrimeParameter q) (1 ⊗ₜ[K] (algebraMap (𝓞 K) K a • x)) ≤ 1
    rw [ξ.norm_rational_smul]
    have haabs := NumberField.abs_le_one_of_isIntegral (normalizedPrimeParameter_mem_fin q)
      (NumberField.RingOfIntegers.isIntegral_coe a)
    exact (mul_le_mul haabs hxq (ξ.norm_nonneg _ _) zero_le_one).trans_eq (mul_one 1)

/-- The canonical inclusion of the literal global unit-ball module into the
literal local unit-ball module, using their actual integral scalar actions. -/
def globalToRationalUnitBall
    (ξ : NormFamily (S (K := K)) E) (hξ : ξ.IsUltrametric)
    (p : HeightOneSpectrum (𝓞 K)) :
    ξ.globalUnitBallModule hξ →ₗ[𝓞 K]
      ξ.rationalUnitBallModule (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p) hξ
    where
  toFun x := ⟨x.1, x.2 _ (normalizedPrimeParameter_mem_fin p)⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp]
theorem globalToRationalUnitBall_coe
    (ξ : NormFamily (S (K := K)) E) (hξ : ξ.IsUltrametric)
    (p : HeightOneSpectrum (𝓞 K)) (x : ξ.globalUnitBallModule hξ) :
    (ξ.globalToRationalUnitBall hξ p x : E) = x := rfl

/-- The actual local inclusion is injective without a coherence hypothesis. -/
theorem globalToRationalUnitBall_injective
    (ξ : NormFamily (S (K := K)) E) (hξ : ξ.IsUltrametric)
    (p : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (ξ.globalToRationalUnitBall hξ p) := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : ξ.rationalUnitBallModule
    (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p) hξ => (z : E)) h)

/-- Source coherence and the produced actual prime-complement denominators
identify the literal local ball as localization of the literal global ball. -/
theorem HasFiniteNormExceptions.isLocalizedModule_globalToRationalUnitBall
    {ξ : NormFamily (S (K := K)) E} (hfinite : ξ.HasFiniteNormExceptions)
    (hξ : ξ.IsUltrametric) (p : HeightOneSpectrum (𝓞 K)) :
    IsLocalizedModule p.asIdeal.primeCompl (ξ.globalToRationalUnitBall hξ p) := by
  let : IsLocalizedModule p.asIdeal.primeCompl (LinearMap.id :
      ξ.rationalUnitBallModule (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p)
        hξ →ₗ[𝓞 K] ξ.rationalUnitBallModule (normalizedPrimeParameter p)
          (normalizedPrimeParameter_mem_fin p) hξ) := by
    simpa only [FinitePlace.maximalIdeal_mk] using
      ξ.isLocalizedModule_rationalUnitBall_of_finitePlace (normalizedPrimeParameter p)
        (normalizedPrimeParameter_mem_fin p) hξ (FinitePlace.mk p)
        (normalizedPrimeValue_isEquiv p)
  refine ⟨?_, ?_, ?_⟩
  · exact IsLocalizedModule.map_units (LinearMap.id :
      ξ.rationalUnitBallModule (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p)
        hξ →ₗ[𝓞 K] ξ.rationalUnitBallModule (normalizedPrimeParameter p)
          (normalizedPrimeParameter_mem_fin p) hξ)
  · intro x
    obtain ⟨a, ha, hax⟩ := hfinite.exists_primeCompl_smul_mem_globalUnitBall p x.2
    exact ⟨(⟨algebraMap (𝓞 K) K a • (x : E), hax⟩, ⟨a, ha⟩), Subtype.ext rfl⟩
  · intro x y h
    have hxy := ξ.globalToRationalUnitBall_injective hξ p h
    exact ⟨1, congrArg (fun z => (1 : p.asIdeal.primeCompl) • z) hxy⟩

/-- The actual coefficient-ring base change of the coherent global module
recovers the actual rational local unit-ball module. -/
def HasFiniteNormExceptions.normalizedGlobalLocalEquiv
    {ξ : NormFamily (S (K := K)) E} (hfinite : ξ.HasFiniteNormExceptions)
    (hξ : ξ.IsUltrametric) (p : HeightOneSpectrum (𝓞 K)) :
    ((S (K := K)).rationalLocalRing (normalizedPrimeParameter p)
      (normalizedPrimeParameter_mem_fin p)) ⊗[𝓞 K] (ξ.globalUnitBallModule hξ) ≃ₗ[
      (S (K := K)).rationalLocalRing (normalizedPrimeParameter p)
        (normalizedPrimeParameter_mem_fin p)]
      ξ.rationalUnitBallModule (normalizedPrimeParameter p)
        (normalizedPrimeParameter_mem_fin p) hξ := by
  letI : IsLocalization p.asIdeal.primeCompl ((S (K := K)).rationalLocalRing
      (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p)) := by
    simpa only [FinitePlace.maximalIdeal_mk] using
      (S (K := K)).isLocalization_rationalLocalRing_of_finitePlace
        (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p) (FinitePlace.mk p)
        (normalizedPrimeValue_isEquiv p)
  letI := hfinite.isLocalizedModule_globalToRationalUnitBall hξ p
  exact (IsLocalizedModule.isBaseChange p.asIdeal.primeCompl
    ((S (K := K)).rationalLocalRing (normalizedPrimeParameter p)
      (normalizedPrimeParameter_mem_fin p)) (ξ.globalToRationalUnitBall hξ p)).equiv

@[simp]
theorem HasFiniteNormExceptions.normalizedGlobalLocalEquiv_tmul
    {ξ : NormFamily (S (K := K)) E} (hfinite : ξ.HasFiniteNormExceptions)
    (hξ : ξ.IsUltrametric) (p : HeightOneSpectrum (𝓞 K))
    (r : (S (K := K)).rationalLocalRing (normalizedPrimeParameter p)
      (normalizedPrimeParameter_mem_fin p)) (x : ξ.globalUnitBallModule hξ) :
    hfinite.normalizedGlobalLocalEquiv hξ p (r ⊗ₜ[𝓞 K] x) =
      r • ξ.globalToRationalUnitBall hξ p x := by
  let : IsLocalization p.asIdeal.primeCompl ((S (K := K)).rationalLocalRing
      (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p)) := by
    simpa only [FinitePlace.maximalIdeal_mk] using
      (S (K := K)).isLocalization_rationalLocalRing_of_finitePlace
        (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p) (FinitePlace.mk p)
        (normalizedPrimeValue_isEquiv p)
  let := hfinite.isLocalizedModule_globalToRationalUnitBall hξ p
  exact IsBaseChange.equiv_tmul (IsLocalizedModule.isBaseChange p.asIdeal.primeCompl
    ((S (K := K)).rationalLocalRing (normalizedPrimeParameter p)
      (normalizedPrimeParameter_mem_fin p)) (ξ.globalToRationalUnitBall hξ p)) r x

private theorem normalizedValue_isNontrivial (ω : (S (K := K)).Ω) :
    ((S (K := K)).ϕ ω).IsNontrivial :=
  NormalizedNumberFieldPlaces.parameter_isNontrivial
    (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω)

/-- Actual global integral absorption identifies the original vector space
as localization of the coherent literal global module at nonzero integers. -/
theorem HasFiniteNormExceptions.isLocalizedModule_normalizedGlobalGenericFibre
    {ξ : NormFamily (S (K := K)) E} (hfinite : ξ.HasFiniteNormExceptions)
    (hξ : ξ.IsUltrametric) :
    IsLocalizedModule (nonZeroDivisors (𝓞 K)) (ξ.globalUnitBallModule hξ).subtype := by
  let : IsLocalizedModule (nonZeroDivisors (𝓞 K)) (LinearMap.id : E →ₗ[𝓞 K] E) :=
    isLocalizedModule_id (nonZeroDivisors (𝓞 K)) E K
  refine ⟨IsLocalizedModule.map_units (LinearMap.id : E →ₗ[𝓞 K] E), ?_, ?_⟩
  · intro x
    obtain ⟨a, ha, hax⟩ := hfinite.exists_integral_smul_mem_globalUnitBall
      (fun ω _ => normalizedValue_isNontrivial ω) x
    exact ⟨(⟨algebraMap (𝓞 K) K a • x, hax⟩,
      ⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩), rfl⟩
  · intro x y h
    have hxy : x = y := Subtype.ext h
    exact ⟨1, congrArg (fun z => (1 : nonZeroDivisors (𝓞 K)) • z) hxy⟩

/-- The canonical actual generic fibre of the coherent literal global module. -/
def HasFiniteNormExceptions.normalizedGlobalGenericFibreEquiv
    {ξ : NormFamily (S (K := K)) E} (hfinite : ξ.HasFiniteNormExceptions)
    (hξ : ξ.IsUltrametric) : K ⊗[𝓞 K] (ξ.globalUnitBallModule hξ) ≃ₗ[K] E := by
  letI := hfinite.isLocalizedModule_normalizedGlobalGenericFibre hξ
  exact (IsLocalizedModule.isBaseChange (nonZeroDivisors (𝓞 K))
    K (ξ.globalUnitBallModule hξ).subtype).equiv

@[simp]
theorem HasFiniteNormExceptions.normalizedGlobalGenericFibreEquiv_tmul
    {ξ : NormFamily (S (K := K)) E} (hfinite : ξ.HasFiniteNormExceptions)
    (hξ : ξ.IsUltrametric) (a : K) (x : ξ.globalUnitBallModule hξ) :
    hfinite.normalizedGlobalGenericFibreEquiv hξ (a ⊗ₜ[𝓞 K] x) = a • (x : E) := by
  let := hfinite.isLocalizedModule_normalizedGlobalGenericFibre hξ
  exact IsBaseChange.equiv_tmul (IsLocalizedModule.isBaseChange (nonZeroDivisors (𝓞 K))
    K (ξ.globalUnitBallModule hξ).subtype) a x

/-- Actual integral global absorption implies the genuine finite-exception
condition by the proved finite support of nonzero normalized scalar values. -/
theorem hasFiniteNormExceptions_of_integral_global_absorption
    (ξ : NormFamily (S (K := K)) E)
    (habs : ∀ x : E, ∃ a : 𝓞 K, a ≠ 0 ∧
      algebraMap (𝓞 K) K a • x ∈ ξ.globalUnitBall) : ξ.HasFiniteNormExceptions := by
  intro x
  obtain ⟨a, ha, hax⟩ := habs x
  have haK : algebraMap (𝓞 K) K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha
  have hs : {ω : (S (K := K)).Ω |
      (S (K := K)).ϕ ω (algebraMap (𝓞 K) K a) ≠ 1}.Finite :=
    normalizedPlaceValue_hasFiniteMulSupport haK
  apply hs.subset
  intro ω hω
  change (S (K := K)).ϕ ω (algebraMap (𝓞 K) K a) ≠ 1
  intro hone
  have hbound := hax ω hω.1
  change ξ.norm ω (1 ⊗ₜ[K] (algebraMap (𝓞 K) K a • x)) ≤ 1 at hbound
  rw [ξ.norm_rational_smul, hone, one_mul] at hbound
  exact (not_lt_of_ge hbound) hω.2

/-- Source coherence is equivalent to actual global generic-fibre localization;
the reverse implication uses genuine scalar-support finiteness. -/
theorem hasFiniteNormExceptions_iff_isLocalizedModule_normalizedGlobalGenericFibre
    (ξ : NormFamily (S (K := K)) E) (hξ : ξ.IsUltrametric) :
    ξ.HasFiniteNormExceptions ↔
      IsLocalizedModule (nonZeroDivisors (𝓞 K)) (ξ.globalUnitBallModule hξ).subtype := by
  refine ⟨fun h => h.isLocalizedModule_normalizedGlobalGenericFibre hξ, ?_⟩
  intro h
  let := h
  apply ξ.hasFiniteNormExceptions_of_integral_global_absorption
  intro x
  obtain ⟨⟨m, d⟩, hmd⟩ := IsLocalizedModule.surj (nonZeroDivisors (𝓞 K))
    (ξ.globalUnitBallModule hξ).subtype x
  exact ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp d.property, hmd ▸ m.property⟩

/-- Domination gives actual finite generation, while the independent genuine
coherence hypothesis gives actual global spanning. -/
theorem IsDominated.fg_and_span_normalizedGlobalUnitBallModule [FiniteDimensional K E]
    {ξ : NormFamily (S (K := K)) E} (hdom : ξ.IsDominated)
    (hξ : ξ.IsUltrametric) (hfinite : ξ.HasFiniteNormExceptions) :
    (ξ.globalUnitBallModule hξ).FG ∧ Submodule.span K ξ.globalUnitBall = ⊤ :=
  ⟨hdom.fg_normalizedGlobalUnitBallModule hξ,
    hfinite.span_globalUnitBall_eq_top (fun ω _ => normalizedValue_isNontrivial ω)⟩

end ArakelovGeometry.NormFamily

end
