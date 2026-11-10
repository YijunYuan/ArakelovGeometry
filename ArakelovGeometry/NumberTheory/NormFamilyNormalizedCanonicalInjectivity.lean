/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NormFamilyNormalizedCoherenceCriteria
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Unconditional canonical inclusions of the actual global unit ball

Localization preserves the literal global-to-local inclusion. The canonical
local and generic tensor maps are therefore injective without coherence or
domination. Their surjectivity remains the independent coherence condition.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct

namespace ArakelovGeometry

/-- An injective map into an already localized module has injective scalar
extension to the actual localization ring. -/
theorem linearMap_liftBaseChange_injective_of_isLocalization
    {R A M N : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S : Submonoid R) [IsLocalization S A]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [Module A N] [IsScalarTower R A N] (f : M →ₗ[R] N)
    (hf : Function.Injective f) : Function.Injective (f.liftBaseChange A) := by
  let j := TensorProduct.mk R A M 1
  let : IsLocalizedModule S (LinearMap.id : N →ₗ[R] N) :=
    isLocalizedModule_id S N A
  have he : IsLocalizedModule.map S j (LinearMap.id : N →ₗ[R] N) f =
      (f.liftBaseChange A).restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext S j (LinearMap.id : N →ₗ[R] N)
    rw [IsLocalizedModule.map_comp]
    ext m
    simp [j]
  have hi := IsLocalizedModule.map_injective S j (LinearMap.id : N →ₗ[R] N) f hf
  rw [he] at hi
  exact hi

namespace NormFamily

open AdelicStructure ActualPrimeIndexing

variable {K : Type*} [Field K] [NumberField K]
  {E : Type*} [AddCommGroup E] [Module K E]

/-- The source's actual localized global inclusion is injective for every
ultrametric family, with no coherence or domination input. -/
theorem normalizedGlobalLocalTensorMap_injective
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsUltrametric) (p : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (ξ.normalizedGlobalLocalTensorMap hξ p) := by
  let : IsLocalization p.asIdeal.primeCompl
      ((normalizedNumberFieldAdelicStructure K).rationalLocalRing
        (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p)) := by
    simpa only [FinitePlace.maximalIdeal_mk] using
      (normalizedNumberFieldAdelicStructure K).isLocalization_rationalLocalRing_of_finitePlace
        (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p) (FinitePlace.mk p)
        (Quotient.eq'.mp (normalizedPlaceValue_class (normalizedPrimeParameter p)))
  exact linearMap_liftBaseChange_injective_of_isLocalization p.asIdeal.primeCompl
    (ξ.globalToRationalUnitBall hξ p) (ξ.globalToRationalUnitBall_injective hξ p)

/-- The literal global-ball generic tensor inclusion is injective without a
coherence or domination hypothesis. -/
theorem normalizedGlobalGenericFibreMap_injective
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsUltrametric) :
    Function.Injective (ξ.normalizedGlobalGenericFibreMap hξ) :=
  linearMap_liftBaseChange_injective_of_isLocalization (nonZeroDivisors (𝓞 K))
    (ξ.globalUnitBallModule hξ).subtype (ξ.globalUnitBallModule hξ).subtype_injective

end NormFamily
end ArakelovGeometry
