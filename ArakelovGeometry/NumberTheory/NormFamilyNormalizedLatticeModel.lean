/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.ExternalResults.Measure
public import ArakelovGeometry.NumberTheory.NormFamilyNormalizedCoherenceCriteria

/-!
# Actual common-basis lattice models

A literal completed coordinate gauge outside finitely many actual primes
produces coherence and domination, including upper domination of the actual
completed operator dual. Finite error terms use actual finite singleton masses.
-/

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField TensorProduct ENNReal

noncomputable section

namespace ArakelovGeometry.NormFamily

open AdelicStructure ActualPrimeIndexing

variable {K : Type*} [Field K] [NumberField K]
  {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local notation "N" => normalizedNumberFieldAdelicStructure K

/-- The actual normalized infinite locus is a finite image of actual infinite places. -/
theorem normalizedInfiniteLocus_finite : (N).Ωinf.Finite := by
  let f : InfinitePlace K → (N).Ω := fun w =>
    ⟨Quotient.mk' w.val, mk_infinitePlace_ne_trivialPlace w⟩
  apply (Set.finite_range f).subset
  intro ω hω
  rcases place_trichotomy ω.val with ht | ⟨v, hv⟩ | ⟨w, hw⟩
  · exact False.elim (ω.property ht)
  · have heq : ω = normalizedPrimeParameter v.maximalIdeal := by
      apply Subtype.ext
      change ω.val = Quotient.mk' (FinitePlace.mk v.maximalIdeal).val
      rw [FinitePlace.mk_maximalIdeal]
      exact hv
    change ¬ ω ∈ (N).Ωfin at hω
    exact False.elim (hω (heq.symm ▸ normalizedPrimeParameter_mem_fin _))
  · exact ⟨w, Subtype.ext hw.symm⟩

/-- Actual singleton masses are finite actual completion degrees. -/
theorem normalizedSingleton_ne_top (ω : (N).Ω) :
    (N).v {ω} ≠ ⊤ := by
  intro h
  exact ENNReal.natCast_ne_top _
    ((normalizedNumberFieldAdelicStructure_v_singleton ω).symm.trans h)

/-- Actual finite support, without a measurability certificate, gives integrability. -/
theorem integrable_normalized_of_finiteSupport (g : (N).Ω → ℝ)
    (hg : (Function.support g).Finite) : Integrable g (N).v := by
  classical
  let : MeasurableSingletonClass (N).Ω :=
    inferInstanceAs (MeasurableSingletonClass
      {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
  apply integrable_of_support_subset_finset (s := hg.toFinset)
  · simpa only [Set.Finite.coe_toFinset] using (Set.Subset.refl (Function.support g))
  · intro ω _
    exact normalizedSingleton_ne_top ω

/-- Actual completed norm equality off a finite set makes the distance integrable. -/
theorem integrable_localDist_of_norm_eq_off_finite (ξ η : NormFamily (N) E)
    (F : Set (N).Ω) (hF : F.Finite)
    (heq : ∀ ω ∉ F, ∀ z, ξ.norm ω z = η.norm ω z) :
    Integrable (ξ.localDist η) (N).v := by
  apply integrable_normalized_of_finiteSupport
  apply hF.subset
  intro ω hω
  by_contra hωF
  exact hω ((ξ.localDist_eq_zero_iff η ω).mpr (Seminorm.ext (heq ω hωF)))

/-- Finite changes of actual completed norms preserve upper domination. -/
theorem isUpperDominated_of_norm_eq_off_finite (ξ η : NormFamily (N) E)
    (F : Set (N).Ω) (hF : F.Finite)
    (heq : ∀ ω ∉ F, ∀ z, ξ.norm ω z = η.norm ω z) (hη : η.IsUpperDominated) :
    ξ.IsUpperDominated := by
  apply hη.of_localDist
  exact ⟨η.localDist ξ, integrable_localDist_of_norm_eq_off_finite η ξ F hF
    (fun ω hω z => (heq ω hω z).symm), Filter.Eventually.of_forall (fun _ => le_rfl)⟩

omit [NumberField K] in
/-- Equality of entire completed primal norms preserves actual operator dual norms. -/
theorem dual_norm_eq_of_completedNorm_eq {S : AdelicStructure K}
    (ξ η : NormFamily S E) (ω : S.Ω)
    (heq : ∀ z, ξ.norm ω z = η.norm ω z)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K E) :
    ξ.dual.norm ω z = η.dual.norm ω z := by
  rw [ξ.dual_norm_eq_sSup, η.dual_norm_eq_sSup]
  simp only [heq]

/-- A literal completed finite-place gauge has the actual dual-basis gauge. -/
theorem dual_basisGauge_eq_of_basisGauge_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ξ : NormFamily (N) E) (b : Module.Basis ι K E)
    (p : HeightOneSpectrum (𝓞 K))
    (heq : ∀ z, ξ.norm (normalizedPrimeParameter p) z =
      (ofBasis (N) E b).norm (normalizedPrimeParameter p) z)
    (z : ((N).ϕ (normalizedPrimeParameter p)).Completion ⊗[K] Module.Dual K E) :
    ξ.dual.norm (normalizedPrimeParameter p) z =
      (ofBasis (N) (Module.Dual K E) b.dualBasis).norm
        (normalizedPrimeParameter p) z := by
  classical
  have h := dual_norm_eq_of_completedNorm_eq ξ (ofBasisMixed (N) E b)
    (normalizedPrimeParameter p) (fun x => (heq x).trans
      (ofBasisMixed_norm_of_finite b _ (normalizedPrimeParameter_mem_fin p) x).symm) z
  rwa [ofBasisMixed_dual] at h

/-- The literal common-basis model produces both primal and actual dual domination. -/
theorem isDominated_of_basisGauge_eq_off_finite_primes {ι : Type*} [Fintype ι]
    (ξ : NormFamily (N) E) (b : Module.Basis ι K E)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hmodel : ∀ p ∉ T, ∀ z, ξ.norm (normalizedPrimeParameter p) z =
      (ofBasis (N) E b).norm (normalizedPrimeParameter p) z) :
    ξ.IsDominated := by
  classical
  let F : Set (N).Ω := (N).Ωinf ∪
    normalizedPrimeParameter '' (T : Set (HeightOneSpectrum (𝓞 K)))
  have hF : F.Finite := normalizedInfiniteLocus_finite.union (T.finite_toSet.image _)
  have hpω (ω : (N).Ω) (hω : ω ∉ F) :
      ∃ p ∉ T, normalizedPrimeParameter p = ω := by
    have hfin : ω ∈ (N).Ωfin := by
      by_contra h
      exact hω (Or.inl h)
    obtain ⟨p, hp⟩ := exists_normalizedPrimeParameter_eq ω hfin
    exact ⟨p, fun h => hω (Or.inr ⟨p, h, hp⟩), hp⟩
  constructor
  · apply isUpperDominated_of_norm_eq_off_finite ξ (ofBasis (N) E b) F hF
      _ (ofBasis_isUpperDominated b)
    intro ω hω z
    obtain ⟨p, hp, rfl⟩ := hpω ω hω
    exact hmodel p hp z
  · apply isUpperDominated_of_norm_eq_off_finite ξ.dual
      (ofBasis (N) (Module.Dual K E) b.dualBasis) F hF
      _ (ofBasis_isUpperDominated b.dualBasis)
    intro ω hω z
    obtain ⟨p, hp, rfl⟩ := hpω ω hω
    exact dual_basisGauge_eq_of_basisGauge_eq ξ b p (hmodel p hp) z

omit [FiniteDimensional K E] in
/-- The actual mixed-basis family is coherent on the normalized number-field curve. -/
theorem normalizedBasisMixed_hasFiniteNormExceptions {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K E) : (ofBasisMixed (N) E b).HasFiniteNormExceptions := by
  apply hasFiniteNormExceptions_of_span_normalizedGlobalUnitBall_eq_top
    (ofBasisMixed (N) E b) (ofBasisMixed_isUltrametric b)
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩ ω hω
  rw [mem_rationalUnitBall, ofBasisMixed_norm_of_finite b ω hω,
    ofBasis_norm_tmul_basis, norm_one]

omit [FiniteDimensional K E] in
/-- Literal finite model gauges produce genuine finite-exception coherence. -/
theorem hasFiniteNormExceptions_of_basisGauge_eq_off_finite_primes
    {ι : Type*} [Fintype ι] (ξ : NormFamily (N) E) (b : Module.Basis ι K E)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hmodel : ∀ p ∉ T, ∀ z, ξ.norm (normalizedPrimeParameter p) z =
      (ofBasis (N) E b).norm (normalizedPrimeParameter p) z) :
    ξ.HasFiniteNormExceptions := by
  intro x
  apply ((T.finite_toSet.image normalizedPrimeParameter).union
    (normalizedBasisMixed_hasFiniteNormExceptions b x)).subset
  intro ω hω
  by_cases hωT : ω ∈ normalizedPrimeParameter '' (T : Set (HeightOneSpectrum (𝓞 K)))
  · exact Or.inl hωT
  · obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω.1
    have hp : p ∉ T := fun h => hωT ⟨p, h, rfl⟩
    refine Or.inr ⟨hω.1, ?_⟩
    rw [ofBasisMixed_norm_of_finite b _ hω.1, ← hmodel p hp]
    exact hω.2

/-- Genuine common gauges imply the two source conclusions, without assuming either. -/
theorem coherent_and_dominated_of_basisGauge_eq_off_finite_primes
    {ι : Type*} [Fintype ι] (ξ : NormFamily (N) E) (b : Module.Basis ι K E)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hmodel : ∀ p ∉ T, ∀ z, ξ.norm (normalizedPrimeParameter p) z =
      (ofBasis (N) E b).norm (normalizedPrimeParameter p) z) :
    ξ.HasFiniteNormExceptions ∧ ξ.IsDominated :=
  ⟨hasFiniteNormExceptions_of_basisGauge_eq_off_finite_primes ξ b T hmodel,
    isDominated_of_basisGauge_eq_off_finite_primes ξ b T hmodel⟩

end ArakelovGeometry.NormFamily
