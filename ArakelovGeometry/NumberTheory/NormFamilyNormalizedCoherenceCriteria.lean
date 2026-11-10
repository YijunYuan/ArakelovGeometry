/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NormFamilyNormalizedCoherence

/-!
# Actual canonical-map coherence criteria

The source's all-place, one-place and generic-fibre criteria concern the actual
canonical maps. Tensor-image induction puts their images in the rational span
of the literal global ball. Actual local spanning and finite scalar support
then prove the reverse coherence implications without assuming global coherence.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

open AdelicStructure ActualPrimeIndexing

variable {K : Type*} [Field K] [NumberField K]
  {E : Type*} [AddCommGroup E] [Module K E]

local notation "N" => normalizedNumberFieldAdelicStructure K

/-- The original canonical rational local tensor map, with no coherence input. -/
def normalizedGlobalLocalTensorMap (ξ : NormFamily (N) E)
    (hξ : ξ.IsUltrametric) (p : HeightOneSpectrum (𝓞 K)) :
    ((N).rationalLocalRing (normalizedPrimeParameter p)
      (normalizedPrimeParameter_mem_fin p)) ⊗[𝓞 K] (ξ.globalUnitBallModule hξ) →ₗ[
      (N).rationalLocalRing (normalizedPrimeParameter p)
        (normalizedPrimeParameter_mem_fin p)]
      ξ.rationalUnitBallModule (normalizedPrimeParameter p)
        (normalizedPrimeParameter_mem_fin p) hξ :=
  (ξ.globalToRationalUnitBall hξ p).liftBaseChange
    ((N).rationalLocalRing (normalizedPrimeParameter p)
      (normalizedPrimeParameter_mem_fin p))

@[simp]
theorem normalizedGlobalLocalTensorMap_tmul (ξ : NormFamily (N) E)
    (hξ : ξ.IsUltrametric) (p : HeightOneSpectrum (𝓞 K))
    (a : (N).rationalLocalRing (normalizedPrimeParameter p)
      (normalizedPrimeParameter_mem_fin p)) (x : ξ.globalUnitBallModule hξ) :
    ξ.normalizedGlobalLocalTensorMap hξ p (a ⊗ₜ[𝓞 K] x) =
      a • ξ.globalToRationalUnitBall hξ p x :=
  LinearMap.liftBaseChange_tmul _ _ a x

/-- The actual coherent local equivalence is the original canonical local map. -/
theorem HasFiniteNormExceptions.normalizedGlobalLocalEquiv_coe
    {ξ : NormFamily (N) E} (hfinite : ξ.HasFiniteNormExceptions)
    (hξ : ξ.IsUltrametric) (p : HeightOneSpectrum (𝓞 K)) :
    (hfinite.normalizedGlobalLocalEquiv hξ p).toLinearMap =
      ξ.normalizedGlobalLocalTensorMap hξ p := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  exact (hfinite.normalizedGlobalLocalEquiv_tmul hξ p a x).trans
    (ξ.normalizedGlobalLocalTensorMap_tmul hξ p a x).symm

/-- The original canonical global generic map, with no coherence input. -/
def normalizedGlobalGenericFibreMap (ξ : NormFamily (N) E)
    (hξ : ξ.IsUltrametric) : K ⊗[𝓞 K] (ξ.globalUnitBallModule hξ) →ₗ[K] E :=
  (ξ.globalUnitBallModule hξ).subtype.liftBaseChange K

@[simp]
theorem normalizedGlobalGenericFibreMap_tmul (ξ : NormFamily (N) E)
    (hξ : ξ.IsUltrametric) (a : K) (x : ξ.globalUnitBallModule hξ) :
    ξ.normalizedGlobalGenericFibreMap hξ (a ⊗ₜ[𝓞 K] x) = a • (x : E) :=
  LinearMap.liftBaseChange_tmul _ _ a x

/-- The actual coherent generic equivalence is the original canonical generic map. -/
theorem HasFiniteNormExceptions.normalizedGlobalGenericFibreEquiv_coe
    {ξ : NormFamily (N) E} (hfinite : ξ.HasFiniteNormExceptions)
    (hξ : ξ.IsUltrametric) :
    (hfinite.normalizedGlobalGenericFibreEquiv hξ).toLinearMap =
      ξ.normalizedGlobalGenericFibreMap hξ := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  exact (hfinite.normalizedGlobalGenericFibreEquiv_tmul hξ a x).trans
    (ξ.normalizedGlobalGenericFibreMap_tmul hξ a x).symm

/-- Every actual local tensor image lies in the rational span of the global ball. -/
theorem normalizedGlobalLocalTensorMap_coe_mem_span (ξ : NormFamily (N) E)
    (hξ : ξ.IsUltrametric) (p : HeightOneSpectrum (𝓞 K))
    (t : ((N).rationalLocalRing (normalizedPrimeParameter p)
      (normalizedPrimeParameter_mem_fin p)) ⊗[𝓞 K] (ξ.globalUnitBallModule hξ)) :
    (ξ.normalizedGlobalLocalTensorMap hξ p t : E) ∈ Submodule.span K ξ.globalUnitBall := by
  induction t using TensorProduct.inductionOn with
  | tmul a x =>
    rw [ξ.normalizedGlobalLocalTensorMap_tmul]
    exact (Submodule.span K ξ.globalUnitBall).smul_mem (a : K)
      (Submodule.subset_span x.property)
  | add t u ht hu =>
    simpa only [map_add, Submodule.coe_add] using
      (Submodule.span K ξ.globalUnitBall).add_mem ht hu

/-- Surjectivity at one actual finite prime forces full global rational span. -/
theorem span_normalizedGlobalUnitBall_eq_top_of_localTensorMap_surjective
    (ξ : NormFamily (N) E) (hξ : ξ.IsUltrametric)
    (p : HeightOneSpectrum (𝓞 K)) (hsurj : Function.Surjective
      (ξ.normalizedGlobalLocalTensorMap hξ p)) : Submodule.span K ξ.globalUnitBall = ⊤ := by
  apply top_unique
  rw [← ξ.span_rationalUnitBall_eq_top (normalizedPrimeParameter p)
    (normalizedPrimeParameter_mem_fin p)
    (NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm
        (normalizedPrimeParameter p)))]
  apply Submodule.span_le.mpr
  intro x hx
  obtain ⟨t, ht⟩ := hsurj ⟨x, hx⟩
  have hm := ξ.normalizedGlobalLocalTensorMap_coe_mem_span hξ p t
  rwa [ht] at hm

/-- Every actual generic tensor image lies in the rational span of the global ball. -/
theorem normalizedGlobalGenericFibreMap_mem_span (ξ : NormFamily (N) E)
    (hξ : ξ.IsUltrametric) (t : K ⊗[𝓞 K] (ξ.globalUnitBallModule hξ)) :
    ξ.normalizedGlobalGenericFibreMap hξ t ∈ Submodule.span K ξ.globalUnitBall := by
  induction t using TensorProduct.inductionOn with
  | tmul a x =>
    rw [ξ.normalizedGlobalGenericFibreMap_tmul]
    exact (Submodule.span K ξ.globalUnitBall).smul_mem a (Submodule.subset_span x.property)
  | add t u ht hu =>
    simpa only [map_add] using (Submodule.span K ξ.globalUnitBall).add_mem ht hu

/-- The original generic tensor surjection forces full global rational span. -/
theorem span_normalizedGlobalUnitBall_eq_top_of_genericFibreMap_surjective
    (ξ : NormFamily (N) E) (hξ : ξ.IsUltrametric)
    (hsurj : Function.Surjective (ξ.normalizedGlobalGenericFibreMap hξ)) :
    Submodule.span K ξ.globalUnitBall = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨t, rfl⟩ := hsurj x
  exact ξ.normalizedGlobalGenericFibreMap_mem_span hξ t

/-- Actual global rational spanning gives source coherence by genuine span
induction, ultrametric addition and actual finite scalar evaluation support. -/
theorem hasFiniteNormExceptions_of_span_normalizedGlobalUnitBall_eq_top
    (ξ : NormFamily (N) E) (hξ : ξ.IsUltrametric)
    (hspan : Submodule.span K ξ.globalUnitBall = ⊤) : ξ.HasFiniteNormExceptions := by
  intro x
  have hx : x ∈ Submodule.span K ξ.globalUnitBall := hspan.symm ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    apply Set.finite_empty.subset
    intro ω hω
    exact (not_lt_of_ge (hx ω hω.1)) hω.2
  | zero =>
    apply Set.finite_empty.subset
    intro ω hω
    have h : (1 : ℝ) < 0 := by
      simpa only [TensorProduct.tmul_zero, ξ.norm_zero] using hω.2
    exact False.elim ((not_lt_of_ge (show (0 : ℝ) ≤ 1 from zero_le_one)) h)
  | add x y _ _ hx hy =>
    apply (hx.union hy).subset
    intro ω hω
    by_contra hout
    have hxω : ξ.norm ω (1 ⊗ₜ[K] x) ≤ 1 := by
      by_contra h
      exact hout (Or.inl ⟨hω.1, not_le.mp h⟩)
    have hyω : ξ.norm ω (1 ⊗ₜ[K] y) ≤ 1 := by
      by_contra h
      exact hout (Or.inr ⟨hω.1, not_le.mp h⟩)
    exact (not_lt_of_ge ((by simpa only [TensorProduct.tmul_add] using
      (hξ ω hω.1 (1 ⊗ₜ[K] x) (1 ⊗ₜ[K] y)).trans (max_le hxω hyω)) :
        ξ.norm ω (1 ⊗ₜ[K] (x + y)) ≤ 1)) hω.2
  | smul a x _ hx =>
    by_cases ha : a = 0
    · subst a
      apply Set.finite_empty.subset
      intro ω hω
      have h : (1 : ℝ) < 0 := by
        simpa only [zero_smul, TensorProduct.tmul_zero, ξ.norm_zero] using hω.2
      exact False.elim ((not_lt_of_ge (show (0 : ℝ) ≤ 1 from zero_le_one)) h)
    · apply (hx.union (normalizedPlaceValue_hasFiniteMulSupport ha)).subset
      intro ω hω
      by_contra hout
      have hxω : ξ.norm ω (1 ⊗ₜ[K] x) ≤ 1 := by
        by_contra h
        exact hout (Or.inl ⟨hω.1, not_le.mp h⟩)
      have haω : (N).ϕ ω a = 1 := by
        by_contra h
        exact hout (Or.inr h)
      have haxω : ξ.norm ω (1 ⊗ₜ[K] (a • x)) ≤ 1 := by
        rw [ξ.norm_rational_smul, haω, one_mul]
        exact hxω
      exact (not_lt_of_ge haxω) hω.2

/-- Actual global spanning is equivalent to genuine source coherence. -/
theorem hasFiniteNormExceptions_iff_span_normalizedGlobalUnitBall_eq_top
    (ξ : NormFamily (N) E) (hξ : ξ.IsUltrametric) :
    ξ.HasFiniteNormExceptions ↔ Submodule.span K ξ.globalUnitBall = ⊤ := by
  constructor
  · intro hfinite
    exact hfinite.span_globalUnitBall_eq_top (fun ω _ =>
      NormalizedNumberFieldPlaces.parameter_isNontrivial
        (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω))
  · exact hasFiniteNormExceptions_of_span_normalizedGlobalUnitBall_eq_top ξ hξ

/-- Source coherence criterion (4), for the original canonical generic-fibre map. -/
theorem hasFiniteNormExceptions_iff_normalizedGlobalGenericFibreMap_bijective
    (ξ : NormFamily (N) E) (hξ : ξ.IsUltrametric) :
    ξ.HasFiniteNormExceptions ↔ Function.Bijective (ξ.normalizedGlobalGenericFibreMap hξ) := by
  constructor
  · intro hfinite
    rw [← hfinite.normalizedGlobalGenericFibreEquiv_coe hξ]
    exact (hfinite.normalizedGlobalGenericFibreEquiv hξ).bijective
  · intro h
    apply hasFiniteNormExceptions_of_span_normalizedGlobalUnitBall_eq_top ξ hξ
    exact ξ.span_normalizedGlobalUnitBall_eq_top_of_genericFibreMap_surjective hξ h.2

/-- Source coherence criterion (2), for the actual canonical map at every actual prime. -/
theorem hasFiniteNormExceptions_iff_normalizedGlobalLocalTensorMap_all_bijective
    (ξ : NormFamily (N) E) (hξ : ξ.IsUltrametric) :
    ξ.HasFiniteNormExceptions ↔ ∀ p : HeightOneSpectrum (𝓞 K),
      Function.Bijective (ξ.normalizedGlobalLocalTensorMap hξ p) := by
  constructor
  · intro hfinite p
    rw [← hfinite.normalizedGlobalLocalEquiv_coe hξ p]
    exact (hfinite.normalizedGlobalLocalEquiv hξ p).bijective
  · intro h
    apply hasFiniteNormExceptions_of_span_normalizedGlobalUnitBall_eq_top ξ hξ
    let p : HeightOneSpectrum (𝓞 K) := Classical.arbitrary _
    exact ξ.span_normalizedGlobalUnitBall_eq_top_of_localTensorMap_surjective hξ p (h p).2

/-- Source coherence criterion (3), with genuine canonical-map bijectivity at one prime. -/
theorem hasFiniteNormExceptions_iff_normalizedGlobalLocalTensorMap_exists_bijective
    (ξ : NormFamily (N) E) (hξ : ξ.IsUltrametric) :
    ξ.HasFiniteNormExceptions ↔ ∃ p : HeightOneSpectrum (𝓞 K),
      Function.Bijective (ξ.normalizedGlobalLocalTensorMap hξ p) := by
  constructor
  · intro hfinite
    exact ⟨Classical.arbitrary _,
      (hasFiniteNormExceptions_iff_normalizedGlobalLocalTensorMap_all_bijective ξ hξ).mp
        hfinite _⟩
  · rintro ⟨p, hp⟩
    apply hasFiniteNormExceptions_of_span_normalizedGlobalUnitBall_eq_top ξ hξ
    exact ξ.span_normalizedGlobalUnitBall_eq_top_of_localTensorMap_surjective hξ p hp.2

/-- One genuine canonical local surjection already gives all source coherence criteria. -/
theorem hasFiniteNormExceptions_iff_normalizedGlobalLocalTensorMap_exists_surjective
    (ξ : NormFamily (N) E) (hξ : ξ.IsUltrametric) :
    ξ.HasFiniteNormExceptions ↔ ∃ p : HeightOneSpectrum (𝓞 K),
      Function.Surjective (ξ.normalizedGlobalLocalTensorMap hξ p) := by
  constructor
  · intro hfinite
    obtain ⟨p, hp⟩ :=
      (hasFiniteNormExceptions_iff_normalizedGlobalLocalTensorMap_exists_bijective ξ hξ).mp
        hfinite
    exact ⟨p, hp.2⟩
  · rintro ⟨p, hp⟩
    apply hasFiniteNormExceptions_of_span_normalizedGlobalUnitBall_eq_top ξ hξ
    exact ξ.span_normalizedGlobalUnitBall_eq_top_of_localTensorMap_surjective hξ p hp

end ArakelovGeometry.NormFamily

end
