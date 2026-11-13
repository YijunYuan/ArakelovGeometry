/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Strong
public import ArakelovGeometry.NumberTheory.NumberField.Model.Open.Lattice

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.NumberTheory.NumberField.Lattice.Coherence.Model
import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Normalization.Hermitian

/-!
# Actual open model norms imply coherence and domination

Actual section-ring local freeness produces finite projectivity. The original
model gauge on its literal completed tensor images then produces a common
completed frame outside actual finite exceptional primes, hence the source
coherence and domination conclusions.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NumberFieldOpenModel

open NumberFieldOpenRegularFunctions
open AdelicStructure ActualPrimeIndexing

variable {K : Type*} [Field K] [NumberField K]

/-- The actual ring of regular functions on a nonempty number-field open is Noetherian. -/
theorem regularFunctions_isNoetherianRing
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) :
    IsNoetherianRing (regularFunctions U) := by
  let := regularFunctionsLocalization U hU
  exact IsLocalization.isNoetherianRing (Submonoid.powers (openGenerator U hU))
    (regularFunctions U) inferInstance

/-- Actual finite section-ring modules have finite presentation by produced Noetherianity. -/
theorem openModule_finitePresentation
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (M : Type*) [AddCommGroup M] [Module (regularFunctions U) M]
    [Module.Finite (regularFunctions U) M] : Module.FinitePresentation (regularFunctions U) M := by
  let := regularFunctions_isNoetherianRing U hU
  exact Module.finitePresentation_of_finite (regularFunctions U) M

/-- Actual local freeness of a finite original Γ(U)-module produces projectivity. -/
theorem openModule_projective_of_localizations_free
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (M : Type*) [AddCommGroup M] [Module (regularFunctions U) M]
    [Module.Finite (regularFunctions U) M]
    (hfree : ∀ (I : Ideal (regularFunctions U)) (_hI : I.IsMaximal),
      Module.Free (Localization.AtPrime I) (LocalizedModule I.primeCompl M)) :
    Module.Projective (regularFunctions U) M := by
  let := openModule_finitePresentation U hU M
  exact projective_of_localizations_free hfree

/-- The actual excluded finite primes and actual principal frame divisors. -/
def openModelBadPrimes (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K))) (f : 𝓞 K) :
    Set (HeightOneSpectrum (𝓞 K)) :=
  {p | primePoint p ∉ U} ∪ {p | f ∈ p.asIdeal}

/-- Every produced nonzero frame denominator gives a genuinely finite actual bad set. -/
theorem openModelBadPrimes_finite (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) (f : 𝓞 K) (hf : f ≠ 0) :
    (openModelBadPrimes U f).Finite :=
  (finite_excludedPrimes U hU).union (NumberFieldModel.finite_prime_divisors hf)

omit [NumberField K] in
theorem not_mem_openModelBadPrimes
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K))) (f : 𝓞 K)
    (p : HeightOneSpectrum (𝓞 K)) :
    p ∉ openModelBadPrimes U f ↔ primePoint p ∈ U ∧ f ∉ p.asIdeal := by
  simp only [openModelBadPrimes, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not]

local notation "N" => normalizedNumberFieldAdelicStructure K
local notation "Fp" => fun (p : HeightOneSpectrum (𝓞 K)) ↦
  AbsoluteValue.Completion (AdelicStructure.ϕ (N) (normalizedPrimeParameter p))

/-- The literal intrinsic scalar-infimum gauge of the actual completed model tensor range. -/
def completedModelGauge (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E M : Type*) [AddCommGroup E] [Module K E]
    [AddCommGroup M] [Module (regularFunctions U) M]
    (p : HeightOneSpectrum (𝓞 K)) (hp : primePoint p ∈ U) :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientGenericScalarTower U hU E
    (K ⊗[regularFunctions U] M ≃ₗ[K] E) → (Fp p ⊗[K] E → ℝ) := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientGenericScalarTower U hU E
  let := coefficientModule U hU (Fp p ⊗[K] E)
  let := completedCoefficientAlgebra U hU p hp
  intro e
  exact scalarLatticeGauge (F := Fp p)
    ((completedModelTensorMap U hU E M p hp e).range : Set (Fp p ⊗[K] E))

theorem completedModelGauge_eq_tensorRange
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E M : Type*) [AddCommGroup E] [Module K E]
    [AddCommGroup M] [Module (regularFunctions U) M]
    (p : HeightOneSpectrum (𝓞 K)) (hp : primePoint p ∈ U) :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientGenericScalarTower U hU E
    letI := coefficientModule U hU (Fp p ⊗[K] E)
    letI := completedCoefficientAlgebra U hU p hp
    ∀ (e : K ⊗[regularFunctions U] M ≃ₗ[K] E) (z : Fp p ⊗[K] E),
      completedModelGauge U hU E M p hp e z = scalarLatticeGauge (F := Fp p)
        ((completedModelTensorMap U hU E M p hp e).range : Set (Fp p ⊗[K] E)) z := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientGenericScalarTower U hU E
  let := coefficientModule U hU (Fp p ⊗[K] E)
  let := completedCoefficientAlgebra U hU p hp
  intro e z
  rfl

/-- The original actual model-gauge hypothesis produces a common completed rational frame
outside the actual open complement and the produced denominator's actual divisors. -/
theorem exists_basisGauge_eq_off_openModelBadPrimes
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E M : Type*) [AddCommGroup E] [Module K E]
    [AddCommGroup M] [Module (regularFunctions U) M]
    [Module.Finite (regularFunctions U) M] [Module.Projective (regularFunctions U) M]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι K E) (ξ : NormFamily (N) E) :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientGenericScalarTower U hU E
    ∀ e : K ⊗[regularFunctions U] M ≃ₗ[K] E,
      (∀ (p : HeightOneSpectrum (𝓞 K)) (hp : primePoint p ∈ U),
        ∀ z, ξ.norm (normalizedPrimeParameter p) z = completedModelGauge U hU E M p hp e z) →
      ∃ f : 𝓞 K, f ≠ 0 ∧ (openModelBadPrimes U f).Finite ∧
        ∀ p ∉ openModelBadPrimes U f, ∀ z,
          ξ.norm (normalizedPrimeParameter p) z =
            (NormFamily.ofBasis (N) E b).norm (normalizedPrimeParameter p) z := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientGenericScalarTower U hU E
  let := coefficientScalarTower U hU E
  intro e hmodel
  obtain ⟨L, hfg, hspan, _, _, hcompleted⟩ := exists_model_completed_integral_descent U hU E M e
  obtain ⟨f, hf, _, hgauge⟩ := NumberFieldModel.exists_completed_lattice_gauge_frame L hfg hspan b
  refine ⟨f, hf, openModelBadPrimes_finite U hU f hf, ?_⟩
  intro p hp z
  obtain ⟨hpU, hpf⟩ := (not_mem_openModelBadPrimes U f p).mp hp
  let := coefficientModule U hU (Fp p ⊗[K] E)
  let := completedCoefficientAlgebra U hU p hpU
  rw [hmodel p hpU, completedModelGauge_eq_tensorRange, hcompleted p hpU,
    NumberFieldModel.range_completedLatticeTensorMap]
  exact hgauge p hpf z

section NormConclusions

variable (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
  (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
  (E M : Type*) [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup M] [Module (regularFunctions U) M] [Module.Finite (regularFunctions U) M]

/-- The original actual open-model gauge implies genuine finite-exception coherence
and domination, via a produced integral lattice and completed frame. -/
theorem coherent_and_dominated_of_open_model [Module.Projective (regularFunctions U) M]
    (ξ : NormFamily (N) E) :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientGenericScalarTower U hU E
    ∀ e : K ⊗[regularFunctions U] M ≃ₗ[K] E,
      (∀ (p : HeightOneSpectrum (𝓞 K)) (hp : primePoint p ∈ U),
        ∀ z, ξ.norm (normalizedPrimeParameter p) z = completedModelGauge U hU E M p hp e z) →
      ξ.HasFiniteNormExceptions ∧ ξ.IsDominated := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientGenericScalarTower U hU E
  intro e hmodel
  let b := Module.finBasis K E
  obtain ⟨f, _, hT, hframe⟩ := exists_basisGauge_eq_off_openModelBadPrimes U hU E M b ξ e hmodel
  apply NormFamily.coherent_and_dominated_of_basisGauge_eq_off_finite_primes ξ b hT.toFinset
  intro p hp z
  exact hframe p (by simpa only [hT.mem_toFinset] using hp) z

/-- Actual normalized Archimedean completions upgrade the original finite-ultrametric
model conclusion to strong domination without an extra normalization hypothesis. -/
theorem coherent_and_stronglyDominated_of_open_model [Module.Projective (regularFunctions U) M]
    (ξ : NormFamily (N) E) [hξ : ξ.IsUltrametricAtFinitePlaces] :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientGenericScalarTower U hU E
    ∀ e : K ⊗[regularFunctions U] M ≃ₗ[K] E,
      (∀ (p : HeightOneSpectrum (𝓞 K)) (hp : primePoint p ∈ U),
        ∀ z, ξ.norm (normalizedPrimeParameter p) z = completedModelGauge U hU E M p hp e z) →
      ξ.HasFiniteNormExceptions ∧ ξ.IsDominated ∧ ξ.IsStronglyDominated := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientGenericScalarTower U hU E
  intro e hmodel
  obtain ⟨hc, hd⟩ := coherent_and_dominated_of_open_model U hU E M ξ e hmodel
  exact ⟨hc, hd, (ξ.isStronglyDominated_iff_isDominated_of_ultrametric
   ).mpr hd⟩

/-- The source's actual locally free finite regular-function module implies the
coherence and domination conclusions; projectivity is produced from actual local freeness. -/
theorem coherent_and_dominated_of_locallyFree_open_model
    (hfree : ∀ (I : Ideal (regularFunctions U)) (_hI : I.IsMaximal),
      Module.Free (Localization.AtPrime I) (LocalizedModule I.primeCompl M))
    (ξ : NormFamily (N) E) :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientGenericScalarTower U hU E
    ∀ e : K ⊗[regularFunctions U] M ≃ₗ[K] E,
      (∀ (p : HeightOneSpectrum (𝓞 K)) (hp : primePoint p ∈ U),
        ∀ z, ξ.norm (normalizedPrimeParameter p) z = completedModelGauge U hU E M p hp e z) →
      ξ.HasFiniteNormExceptions ∧ ξ.IsDominated := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientGenericScalarTower U hU E
  let := openModule_projective_of_localizations_free U hU M hfree
  exact coherent_and_dominated_of_open_model U hU E M ξ

/-- The genuine actual locally free Γ(U)-model and its literal gauge equality imply
coherence, domination, and strong domination of the original finite-ultrametric family. -/
theorem coherent_and_stronglyDominated_of_locallyFree_open_model
    (hfree : ∀ (I : Ideal (regularFunctions U)) (_hI : I.IsMaximal),
      Module.Free (Localization.AtPrime I) (LocalizedModule I.primeCompl M))
    (ξ : NormFamily (N) E) [hξ : ξ.IsUltrametricAtFinitePlaces] :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientGenericScalarTower U hU E
    ∀ e : K ⊗[regularFunctions U] M ≃ₗ[K] E,
      (∀ (p : HeightOneSpectrum (𝓞 K)) (hp : primePoint p ∈ U),
        ∀ z, ξ.norm (normalizedPrimeParameter p) z = completedModelGauge U hU E M p hp e z) →
      ξ.HasFiniteNormExceptions ∧ ξ.IsDominated ∧ ξ.IsStronglyDominated := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientGenericScalarTower U hU E
  let := openModule_projective_of_localizations_free U hU M hfree
  exact coherent_and_stronglyDominated_of_open_model U hU E M ξ

end NormConclusions

end ArakelovGeometry.NumberFieldOpenModel
