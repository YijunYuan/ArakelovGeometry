/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Coherence.Basic
public import ArakelovGeometry.NumberTheory.NumberField.Local.Lattice.UnitBallBasis

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction

/-!
# Actual completed unit-ball reconstruction from source coherence

The canonical completed coefficient extension of the literal global unit ball
recovers the literal completed unit ball. Genuine finite-exception coherence
produces the rational localization; actual tensor cancellation and the proved
local completed unit-ball equivalence give its completed reconstruction.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.AdelicStructure

universe u

variable {K : Type u} [Field K] (S : AdelicStructure K)

/-- The actual integral coefficient map into the actual completed valuation ring. -/
def integralCompletedLocalCoefficientMap (ω : S.Ω) (hω : ω ∈ S.Ωfin) :
    𝓞 K →+* S.completedLocalRing ω hω :=
  (S.completedLocalCoefficientMap ω hω).comp (S.integralLocalCoefficientMap ω hω)

@[simp]
theorem integralCompletedLocalCoefficientMap_coe (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (a : 𝓞 K) :
    (S.integralCompletedLocalCoefficientMap ω hω a : (S.ϕ ω).Completion) =
      algebraMap K (S.ϕ ω).Completion (algebraMap (𝓞 K) K a) := rfl

/-- Canonical integral scalars act through their actual completion images. -/
instance completedLocalRing_integralAlgebra (ω : S.Ω) (hω : ω ∈ S.Ωfin) :
    Algebra (𝓞 K) (S.completedLocalRing ω hω) :=
  (S.integralCompletedLocalCoefficientMap ω hω).toAlgebra

/-- The integral, rational local and completed coefficient actions agree. -/
instance completedLocalRing_integralRationalScalarTower (ω : S.Ω) (hω : ω ∈ S.Ωfin) :
    IsScalarTower (𝓞 K) (S.rationalLocalRing ω hω) (S.completedLocalRing ω hω) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The completed integral action agrees with the actual completed-field action. -/
instance completedLocalRing_integralCompletionScalarTower (ω : S.Ω) (hω : ω ∈ S.Ωfin) :
    IsScalarTower (𝓞 K) (S.completedLocalRing ω hω) (S.ϕ ω).Completion :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end ArakelovGeometry.AdelicStructure

namespace ArakelovGeometry.NormFamily

open AdelicStructure ActualPrimeIndexing

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E]

/-- The literal completed ball inherits its actual integral coefficient action. -/
instance completedUnitBall_integralModule (ξ : NormFamily S E)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) [hξ : ξ.IsUltrametricAtFinitePlaces] :
    Module (𝓞 K) (ξ.completedUnitBallModule ω hω) :=
  Module.compHom (ξ.completedUnitBallModule ω hω)
    (S.integralCompletedLocalCoefficientMap ω hω)

local instance (ξ : NormFamily S E) (ω : S.Ω) (hω : ω ∈ S.Ωfin) [ξ.IsUltrametricAtFinitePlaces] :
    SMul (𝓞 K) (ξ.completedUnitBallModule ω hω) :=
  (ξ.completedUnitBall_integralModule ω hω).toSMul

/-- Integral and completed coefficient actions on the literal ball agree. -/
instance completedUnitBall_integralScalarTower (ξ : NormFamily S E)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) [hξ : ξ.IsUltrametricAtFinitePlaces] :
    IsScalarTower (𝓞 K) (S.completedLocalRing ω hω)
      (ξ.completedUnitBallModule ω hω) := by
  constructor
  intro a r x
  change (S.integralCompletedLocalCoefficientMap ω hω a * r) • x =
    S.integralCompletedLocalCoefficientMap ω hω a • (r • x)
  exact mul_smul _ _ _

/-- Restriction through the actual rational coefficient map agrees with the
completed integral action. -/
instance completedUnitBall_integralRationalScalarTower (ξ : NormFamily S E)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) [hξ : ξ.IsUltrametricAtFinitePlaces] :
    IsScalarTower (𝓞 K) (S.rationalLocalRing ω hω)
      (ξ.completedUnitBallModule ω hω) := by
  apply IsScalarTower.of_algebraMap_smul
  intro a x
  change (S.integralLocalCoefficientMap ω hω a) • x =
    S.completedLocalCoefficientMap ω hω (S.integralLocalCoefficientMap ω hω a) • x
  exact (IsScalarTower.algebraMap_smul (S.completedLocalRing ω hω)
    (S.integralLocalCoefficientMap ω hω a) x).symm

variable [NumberField K]

local notation "N" => normalizedNumberFieldAdelicStructure K

/-- The actual global-to-completed unit-ball map, before any coherence hypothesis. -/
def normalizedGlobalUnitBallCompletionMap (ξ : NormFamily (N) E)
    [hξ : ξ.IsUltrametricAtFinitePlaces] (p : HeightOneSpectrum (𝓞 K)) :
    ξ.globalUnitBallModule →ₗ[𝓞 K]
      ξ.completedUnitBallModule (normalizedPrimeParameter p)
        (normalizedPrimeParameter_mem_fin p) :=
  ((ξ.rationalUnitBallCompletionMap (normalizedPrimeParameter p)
      (normalizedPrimeParameter_mem_fin p)).restrictScalars (𝓞 K)).comp
    (ξ.globalToRationalUnitBall p)

@[simp]
theorem normalizedGlobalUnitBallCompletionMap_coe (ξ : NormFamily (N) E)
    [hξ : ξ.IsUltrametricAtFinitePlaces] (p : HeightOneSpectrum (𝓞 K))
    (x : ξ.globalUnitBallModule) :
    (ξ.normalizedGlobalUnitBallCompletionMap p x :
      ((N).ϕ (normalizedPrimeParameter p)).Completion ⊗[K] E) =
      1 ⊗ₜ[K] (x : E) := rfl

/-- The canonical completed coefficient extension of the actual global ball. -/
def normalizedGlobalUnitBallCompletedTensorMap (ξ : NormFamily (N) E)
    [hξ : ξ.IsUltrametricAtFinitePlaces] (p : HeightOneSpectrum (𝓞 K)) :
    ((N).completedLocalRing (normalizedPrimeParameter p)
      (normalizedPrimeParameter_mem_fin p)) ⊗[𝓞 K] (ξ.globalUnitBallModule) →ₗ[
      (N).completedLocalRing (normalizedPrimeParameter p)
        (normalizedPrimeParameter_mem_fin p)]
      ξ.completedUnitBallModule (normalizedPrimeParameter p)
        (normalizedPrimeParameter_mem_fin p) :=
  (ξ.normalizedGlobalUnitBallCompletionMap p).liftBaseChange
    ((N).completedLocalRing (normalizedPrimeParameter p)
      (normalizedPrimeParameter_mem_fin p))

@[simp]
theorem normalizedGlobalUnitBallCompletedTensorMap_tmul (ξ : NormFamily (N) E)
    [hξ : ξ.IsUltrametricAtFinitePlaces] (p : HeightOneSpectrum (𝓞 K))
    (a : (N).completedLocalRing (normalizedPrimeParameter p)
      (normalizedPrimeParameter_mem_fin p)) (x : ξ.globalUnitBallModule) :
    ξ.normalizedGlobalUnitBallCompletedTensorMap p (a ⊗ₜ[𝓞 K] x) =
      a • ξ.normalizedGlobalUnitBallCompletionMap p x :=
  LinearMap.liftBaseChange_tmul _ _ a x

variable [FiniteDimensional K E]

/-- Coherence, actual tensor cancellation and the actual local completed-ball
equivalence reconstruct the actual completed ball from the literal global module. -/
def normalizedGlobalCompletedTensorEquiv
    (ξ : NormFamily (N) E) [ξ.HasFiniteNormExceptions]
    [ξ.IsUltrametricAtFinitePlaces] (p : HeightOneSpectrum (𝓞 K)) :
    ((N).completedLocalRing (normalizedPrimeParameter p)
      (normalizedPrimeParameter_mem_fin p)) ⊗[𝓞 K] (ξ.globalUnitBallModule) ≃ₗ[
      (N).completedLocalRing (normalizedPrimeParameter p)
        (normalizedPrimeParameter_mem_fin p)]
      ξ.completedUnitBallModule (normalizedPrimeParameter p)
        (normalizedPrimeParameter_mem_fin p) :=
  let R := (N).rationalLocalRing (normalizedPrimeParameter p)
    (normalizedPrimeParameter_mem_fin p)
  let O := (N).completedLocalRing (normalizedPrimeParameter p)
    (normalizedPrimeParameter_mem_fin p)
  ((TensorProduct.AlgebraTensorModule.cancelBaseChange (𝓞 K) R O O
      (ξ.globalUnitBallModule)).symm.trans
    ((ξ.normalizedGlobalLocalEquiv p).baseChange R O _ _)).trans
    (ξ.normalizedRationalUnitBallCompletedTensorEquiv (normalizedPrimeParameter p)
      (normalizedPrimeParameter_mem_fin p))

@[simp]
theorem normalizedGlobalCompletedTensorEquiv_tmul
    (ξ : NormFamily (N) E) [ξ.HasFiniteNormExceptions]
    [ξ.IsUltrametricAtFinitePlaces] (p : HeightOneSpectrum (𝓞 K))
    (a : (N).completedLocalRing (normalizedPrimeParameter p)
      (normalizedPrimeParameter_mem_fin p)) (x : ξ.globalUnitBallModule) :
    ξ.normalizedGlobalCompletedTensorEquiv p (a ⊗ₜ[𝓞 K] x) =
      a • ξ.normalizedGlobalUnitBallCompletionMap p x := by
  simp only [normalizedGlobalCompletedTensorEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearEquiv.baseChange_tmul, ξ.normalizedGlobalLocalEquiv_tmul,
    one_smul, ξ.normalizedRationalUnitBallCompletedTensorEquiv_tmul]
  rfl

/-- The produced equivalence is the original canonical completed tensor map. -/
theorem normalizedGlobalCompletedTensorEquiv_coe
    (ξ : NormFamily (N) E) [ξ.HasFiniteNormExceptions]
    [ξ.IsUltrametricAtFinitePlaces] (p : HeightOneSpectrum (𝓞 K)) :
    (ξ.normalizedGlobalCompletedTensorEquiv p).toLinearMap =
      ξ.normalizedGlobalUnitBallCompletedTensorMap p := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  exact (ξ.normalizedGlobalCompletedTensorEquiv_tmul p a x).trans
    (ξ.normalizedGlobalUnitBallCompletedTensorMap_tmul p a x).symm

/-- Genuine source coherence makes the literal canonical completed global map bijective. -/
theorem HasFiniteNormExceptions.normalizedGlobalUnitBallCompletedTensorMap_bijective
    {ξ : NormFamily (N) E} (hfinite : ξ.HasFiniteNormExceptions)
    (hξ : ξ.IsUltrametricAtFinitePlaces) (p : HeightOneSpectrum (𝓞 K)) :
    Function.Bijective (ξ.normalizedGlobalUnitBallCompletedTensorMap p) := by
  rw [← ξ.normalizedGlobalCompletedTensorEquiv_coe p]
  exact (ξ.normalizedGlobalCompletedTensorEquiv p).bijective

/-- Every actual normalized finite parameter admits the actual canonical
completed global reconstruction, by genuine exhaustivity of prime indexing. -/
theorem HasFiniteNormExceptions.exists_normalizedGlobalCompletedTensorEquivAt
    {ξ : NormFamily (N) E} (hfinite : ξ.HasFiniteNormExceptions)
    (hξ : ξ.IsUltrametricAtFinitePlaces) (ω : (N).Ω) (hω : ω ∈ (N).Ωfin) :
    ∃ e : ((N).completedLocalRing ω hω) ⊗[𝓞 K]
        (ξ.globalUnitBallModule) ≃ₗ[(N).completedLocalRing ω hω]
        ξ.completedUnitBallModule ω hω,
      ∀ (a : (N).completedLocalRing ω hω) (x : ξ.globalUnitBallModule),
        (e (a ⊗ₜ[𝓞 K] x) : ((N).ϕ ω).Completion ⊗[K] E) =
          (a : ((N).ϕ ω).Completion) • (1 ⊗ₜ[K] (x : E)) := by
  obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
  refine ⟨ξ.normalizedGlobalCompletedTensorEquiv p, ?_⟩
  intro a x
  rw [ξ.normalizedGlobalCompletedTensorEquiv_tmul]
  rfl

/-- The canonical actual completed global equivalence at an arbitrary actual
finite normalized parameter, with existence and formula already produced. -/
def normalizedGlobalCompletedTensorEquivAt
    (ξ : NormFamily (N) E) [hfinite : ξ.HasFiniteNormExceptions]
    [hξ : ξ.IsUltrametricAtFinitePlaces] (ω : (N).Ω) (hω : ω ∈ (N).Ωfin) :
    ((N).completedLocalRing ω hω) ⊗[𝓞 K]
      (ξ.globalUnitBallModule) ≃ₗ[(N).completedLocalRing ω hω]
      ξ.completedUnitBallModule ω hω :=
  (hfinite.exists_normalizedGlobalCompletedTensorEquivAt hξ ω hω).choose

@[simp]
theorem normalizedGlobalCompletedTensorEquivAt_tmul
    (ξ : NormFamily (N) E) [hfinite : ξ.HasFiniteNormExceptions]
    [hξ : ξ.IsUltrametricAtFinitePlaces] (ω : (N).Ω) (hω : ω ∈ (N).Ωfin)
    (a : (N).completedLocalRing ω hω) (x : ξ.globalUnitBallModule) :
    (ξ.normalizedGlobalCompletedTensorEquivAt ω hω (a ⊗ₜ[𝓞 K] x) :
      ((N).ϕ ω).Completion ⊗[K] E) =
        (a : ((N).ϕ ω).Completion) • (1 ⊗ₜ[K] (x : E)) :=
  (hfinite.exists_normalizedGlobalCompletedTensorEquivAt hξ ω hω).choose_spec a x

end ArakelovGeometry.NormFamily

end
