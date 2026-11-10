/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldPurity
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldFullLatticeReplacement
import ArakelovGeometry.NumberTheory.NormalizedNumberFieldInfiniteMass
import ArakelovGeometry.AdelicVectorBundle.StrongSubquotient
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Actual integral models of dominated pure number-field norm families -/

open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

open AdelicStructure ActualPrimeIndexing CompletedUnitBallGauge

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]

theorem IsPureAtFinitePlaces.exists_logNorm_eq_int_mul_primeScale
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsPureAtFinitePlaces) (p : HeightOneSpectrum (𝓞 K))
    {z : ((normalizedNumberFieldAdelicStructure K).ϕ
      (normalizedPrimeParameter p)).Completion ⊗[K] E} (hz : z ≠ 0) :
    ∃ m : ℤ, Real.log (ξ.norm (normalizedPrimeParameter p) z) =
      -(m : ℝ) * normalizedPrimeLogScale p := by
  obtain ⟨a, ha, hnorm⟩ := hξ _ (normalizedPrimeParameter_mem_fin p) z hz
  obtain ⟨m, hm⟩ := completed_norm_eq_uniformizer_zpow p ha
  refine ⟨m, ?_⟩
  rw [hnorm, hm, Real.log_zpow, primeUniformizer_log_norm]
  ring

variable [FiniteDimensional K E]

theorem pure_primeScale_le_localDist_of_norm_ne
    (ξ η : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsPureAtFinitePlaces) (hη : η.IsPureAtFinitePlaces)
    (p : HeightOneSpectrum (𝓞 K))
    (hne : ξ.norm (normalizedPrimeParameter p) ≠ η.norm (normalizedPrimeParameter p)) :
    normalizedPrimeLogScale p ≤ ξ.localDist η (normalizedPrimeParameter p) := by
  have hex : ∃ z, ξ.norm (normalizedPrimeParameter p) z ≠
      η.norm (normalizedPrimeParameter p) z := by
    by_contra! he
    exact hne (Seminorm.ext he)
  obtain ⟨z, hzval⟩ := hex
  have hz : z ≠ 0 := by
    intro hz
    subst z
    exact hzval (by rw [ξ.norm_zero, η.norm_zero])
  obtain ⟨m, hm⟩ := hξ.exists_logNorm_eq_int_mul_primeScale p hz
  obtain ⟨n, hn⟩ := hη.exists_logNorm_eq_int_mul_primeScale p hz
  have hmn : m - n ≠ 0 := by
    intro he
    have hme : m = n := sub_eq_zero.mp he
    apply hzval
    apply Real.log_injOn_pos (ξ.norm_pos _ hz) (η.norm_pos _ hz)
    rw [hm, hn, hme]
  have habs : (1 : ℝ) ≤ |((m - n : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hmn
  have hlog : Real.log (ξ.norm (normalizedPrimeParameter p) z) -
      Real.log (η.norm (normalizedPrimeParameter p) z) =
        -((m - n : ℤ) : ℝ) * normalizedPrimeLogScale p := by
    rw [hm, hn]
    push_cast
    ring
  have hd := ξ.log_norm_sub_le_localDist η (normalizedPrimeParameter p) z
  rw [hlog, abs_mul, abs_neg, abs_of_pos (normalizedPrimeLogScale_pos p)] at hd
  exact (le_mul_of_one_le_left (normalizedPrimeLogScale_pos p).le habs).trans hd

theorem pure_log_two_le_weighted_localDist_of_norm_ne
    (ξ η : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsPureAtFinitePlaces) (hη : η.IsPureAtFinitePlaces)
    (p : HeightOneSpectrum (𝓞 K))
    (hne : ξ.norm (normalizedPrimeParameter p) ≠ η.norm (normalizedPrimeParameter p)) :
    Real.log 2 ≤ (normalizedNumberFieldAdelicStructure K).v.real {normalizedPrimeParameter p} *
      ξ.localDist η (normalizedPrimeParameter p) := by
  have hgap := normalized_weighted_prime_log_gap p
  rw [normalizedPlaceLogScale_prime] at hgap
  exact hgap.trans (mul_le_mul_of_nonneg_left
    (pure_primeScale_le_localDist_of_norm_ne ξ η hξ hη p hne) ENNReal.toReal_nonneg)

theorem summable_normalized_weighted_localDist_of_integrable
    (ξ η : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hI : Integrable (ξ.localDist η) (normalizedNumberFieldAdelicStructure K).v) :
    Summable (fun ω => (normalizedNumberFieldAdelicStructure K).v.real {ω} *
      ξ.localDist η ω) := by
  let S := normalizedNumberFieldAdelicStructure K
  let : Countable S.Ω := inferInstanceAs
    (Countable {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
  let : MeasurableSingletonClass S.Ω := inferInstanceAs
    (MeasurableSingletonClass {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
  have hI' : Integrable (ξ.localDist η) (Measure.sum fun ω => S.v {ω} • Measure.dirac ω) := by
    rw [Measure.sum_smul_dirac]
    exact hI
  have hs := (integrable_sum_dirac_iff (x := id) (c := fun ω => S.v {ω})
    (f := ξ.localDist η) (fun ω => normalizedSingleton_ne_top ω)).mp hI'
  apply hs.congr
  intro ω
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg (ξ.localDist_nonneg η ω)]
  rfl

theorem finite_finiteNorm_disagreements_of_integrable
    (ξ η : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsPureAtFinitePlaces) (hη : η.IsPureAtFinitePlaces)
    (hI : Integrable (ξ.localDist η) (normalizedNumberFieldAdelicStructure K).v) :
    {ω | ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin ∧ ξ.norm ω ≠ η.norm ω}.Finite := by
  have hs := summable_normalized_weighted_localDist_of_integrable ξ η hI
  have he := hs.tendsto_cofinite_zero.eventually_lt_const
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  apply (Filter.eventually_cofinite.mp he).subset
  rintro ω ⟨hω, hne⟩
  obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
  exact not_lt_of_ge (pure_log_two_le_weighted_localDist_of_norm_ne ξ η hξ hη p hne)

theorem IsDominated.integrable_localDist_normalizedBasisMixed
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E} (hdom : ξ.IsDominated)
    (hξ : ξ.IsUltrametric) {ι : Type*} [Fintype ι] (b : Module.Basis ι K E) :
    Integrable (ξ.localDist (ofBasisMixed (normalizedNumberFieldAdelicStructure K) E b))
      (normalizedNumberFieldAdelicStructure K).v := by
  let S := normalizedNumberFieldAdelicStructure K
  let : DiscreteMeasurableSpace S.Ω := inferInstanceAs
    (DiscreteMeasurableSpace {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
  have hstrong := (ξ.isStronglyDominated_iff_isDominated_of_ultrametric hξ
    (normalizedNumberFieldArchimedeanCompletions (K := K))).mpr hdom
  have hb := ofBasisMixed_isStronglyDominated (S := S) b
    (normalizedNumberFieldArchimedeanCompletions (K := K))
  have hfin : S.v S.Ωinf < ⊤ := by
    rw [normalizedNumberFieldAdelicStructure_v_Ωinf]
    exact ENNReal.natCast_lt_top _
  exact (hstrong.localDist hb hfin).integrable Measurable.of_discrete.aestronglyMeasurable

theorem IsDominated.finite_normalizedBasisMixed_disagreements
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E} (hdom : ξ.IsDominated)
    (hξ : ξ.IsUltrametric) (hpure : ξ.IsPureAtFinitePlaces)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι K E) :
    {ω | ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin ∧
      ξ.norm ω ≠ (ofBasisMixed (normalizedNumberFieldAdelicStructure K) E b).norm ω}.Finite :=
  finite_finiteNorm_disagreements_of_integrable ξ _ hpure (ofBasisMixed_isPureAtFinitePlaces b)
    (hdom.integrable_localDist_normalizedBasisMixed hξ b)

theorem IsDominated.hasFiniteNormExceptions_of_pure
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E} (hdom : ξ.IsDominated)
    (hξ : ξ.IsUltrametric) (hpure : ξ.IsPureAtFinitePlaces) : ξ.HasFiniteNormExceptions := by
  let b := Module.finBasis K E
  have hbad := hdom.finite_normalizedBasisMixed_disagreements hξ hpure b
  intro x
  apply (hbad.union (normalizedBasisMixed_hasFiniteNormExceptions b x)).subset
  rintro ω ⟨hω, hx⟩
  by_cases he : ξ.norm ω = (ofBasisMixed (normalizedNumberFieldAdelicStructure K) E b).norm ω
  · exact Or.inr ⟨hω, by rwa [← he]⟩
  · exact Or.inl ⟨hω, he⟩

theorem IsDominated.finite_primeBasisGauge_disagreements
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E} (hdom : ξ.IsDominated)
    (hξ : ξ.IsUltrametric) (hpure : ξ.IsPureAtFinitePlaces)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι K E) :
    {p : HeightOneSpectrum (𝓞 K) | ξ.norm (normalizedPrimeParameter p) ≠
      (ofBasis (normalizedNumberFieldAdelicStructure K) E b).norm
        (normalizedPrimeParameter p)}.Finite := by
  have hf := hdom.finite_normalizedBasisMixed_disagreements hξ hpure b
  apply (hf.preimage normalizedPrimeParameter_injective.injOn).subset
  intro p hp
  refine ⟨normalizedPrimeParameter_mem_fin p, ?_⟩
  intro he
  apply hp
  exact he.trans (Seminorm.ext
    (ofBasisMixed_norm_of_finite b _ (normalizedPrimeParameter_mem_fin p)))

theorem IsDominated.exists_primeBasisGauge_eq_off_finset
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E} (hdom : ξ.IsDominated)
    (hξ : ξ.IsUltrametric) (hpure : ξ.IsPureAtFinitePlaces)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι K E) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ p ∉ T, ∀ z,
      ξ.norm (normalizedPrimeParameter p) z =
        (ofBasis (normalizedNumberFieldAdelicStructure K) E b).norm
          (normalizedPrimeParameter p) z := by
  classical
  have hf := hdom.finite_primeBasisGauge_disagreements hξ hpure b
  refine ⟨hf.toFinset, ?_⟩
  intro p hp z
  have he : ξ.norm (normalizedPrimeParameter p) =
      (ofBasis (normalizedNumberFieldAdelicStructure K) E b).norm (normalizedPrimeParameter p) := by
    by_contra hn
    exact hp (hf.mem_toFinset.mpr hn)
  rw [he]

theorem IsDominated.pure_normalizedGlobalUnitBall_finite_projective_span
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E} (hdom : ξ.IsDominated)
    (hξ : ξ.IsUltrametric) (hpure : ξ.IsPureAtFinitePlaces) :
    (ξ.globalUnitBallModule hξ).FG ∧ Module.Projective (𝓞 K) (ξ.globalUnitBallModule hξ) ∧
      Submodule.span K ξ.globalUnitBall = ⊤ := by
  have hc := hdom.hasFiniteNormExceptions_of_pure hξ hpure
  have hm := hdom.fg_and_span_normalizedGlobalUnitBallModule hξ hc
  exact ⟨hm.1, NumberFieldFullLattice.projective (ξ.globalUnitBallModule hξ) hm.1, hm.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem IsDominated.exists_pure_fullLatticeGaugeFamily_eq
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E} (hdom : ξ.IsDominated)
    (hξ : ξ.IsUltrametric) (hpure : ξ.IsPureAtFinitePlaces) :
    ∃ (hfg : (ξ.globalUnitBallModule hξ).FG)
      (hspan : Submodule.span K ξ.globalUnitBall = ⊤),
      NumberFieldFullLattice.fullLatticeGaugeFamily
        (ξ.globalUnitBallModule hξ) hfg hspan ξ = ξ := by
  have hc := hdom.hasFiniteNormExceptions_of_pure hξ hpure
  have hm := hdom.fg_and_span_normalizedGlobalUnitBallModule hξ hc
  refine ⟨hm.1, hm.2, ?_⟩
  exact (hc.latticeGaugeFamily_eq_fullLatticeGaugeFamily ξ hξ hm.1).symm.trans
    (hpure.latticeGaugeFamily_eq hξ)

end ArakelovGeometry.NormFamily
