/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Lattice.UnitBall.Spanning
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

import ArakelovGeometry.Analysis.AbsoluteValue.Ostrowski

/-!
# The actual prime localization of a rational local coefficient ring

The intrinsic ring `{x : K | |x|_ω ≤ 1}` is canonically the localization
of the actual number-field integer ring at the actual classified finite prime.
No prime-localization conclusion or absolute-value normalization is assumed.
-/

@[expose] public section

open scoped NumberField TensorProduct

namespace ArakelovGeometry.AdelicStructure

universe u

variable {K : Type u} [Field K] (S : AdelicStructure K)

/-- The actual integer-ring inclusion, with codomain restricted to the actual
rational local coefficient ring by the nonarchimedean integral bound. -/
noncomputable def integralLocalCoefficientMap (ω : S.Ω) (hω : ω ∈ S.Ωfin) :
    𝓞 K →+* S.rationalLocalRing ω hω :=
  (algebraMap (𝓞 K) K).codRestrict (S.rationalLocalRing ω hω) fun a ↦ by
    exact (S.mem_rationalLocalRing ω hω _).mpr
      (NumberField.abs_le_one_of_isIntegral hω (NumberField.RingOfIntegers.isIntegral_coe a))

@[simp]
theorem integralLocalCoefficientMap_coe (ω : S.Ω) (hω : ω ∈ S.Ωfin) (a : 𝓞 K) :
    (S.integralLocalCoefficientMap ω hω a : K) = algebraMap (𝓞 K) K a := rfl

noncomputable instance rationalLocalRing_algebra (ω : S.Ω) (hω : ω ∈ S.Ωfin) :
    Algebra (𝓞 K) (S.rationalLocalRing ω hω) :=
  (S.integralLocalCoefficientMap ω hω).toAlgebra

instance rationalLocalRing_scalarTower (ω : S.Ω) (hω : ω ∈ S.Ωfin) :
    IsScalarTower (𝓞 K) (S.rationalLocalRing ω hω) K :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The canonical actual coefficient inclusion is injective. -/
theorem integralLocalCoefficientMap_injective (ω : S.Ω) (hω : ω ∈ S.Ωfin) :
    Function.Injective (S.integralLocalCoefficientMap ω hω) := by
  intro a b h
  exact Subtype.ext (congrArg (fun r : S.rationalLocalRing ω hω ↦ (r : K)) h)

/-- Equivalence with an actual finite value identifies the literal coefficient
ring with the actual integral subring of its integer-valued prime valuation. -/
theorem rationalLocalRing_eq_finitePlaceInteger [NumberField K] (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (p : NumberField.FinitePlace K) (hp : (S.ϕ ω).IsEquiv p.val) :
    S.rationalLocalRing ω hω = (p.maximalIdeal.valuation K).integer := by
  ext x
  rw [S.mem_rationalLocalRing, Valuation.mem_integer_iff]
  refine hp.le_one_iff.trans ?_
  have hnorm := NumberField.FinitePlace.norm_embedding' p.maximalIdeal x
  rw [NumberField.FinitePlace.norm_embedding_eq] at hnorm
  have hnn :
      ((WithZeroMulInt.toNNReal
        (NumberField.HeightOneSpectrum.absNorm_ne_zero p.maximalIdeal)
        (p.maximalIdeal.valuation K x) : NNReal) : ℝ) ≤ 1 ↔
        p.maximalIdeal.valuation K x ≤ 1 := by
    exact_mod_cast WithZeroMulInt.toNNReal_le_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p.maximalIdeal)
  exact (Iff.of_eq (congrArg (fun r : ℝ ↦ r ≤ 1) hnorm)).trans hnn

/-- The intrinsic local coefficient ring is the genuine prime localization of
its actual integer ring, under the canonical inclusion just constructed. -/
theorem isLocalization_rationalLocalRing_of_finitePlace [NumberField K] (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (p : NumberField.FinitePlace K) (hp : (S.ϕ ω).IsEquiv p.val) :
    IsLocalization p.maximalIdeal.asIdeal.primeCompl (S.rationalLocalRing ω hω) := by
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · intro d
    have hpd : p.val (algebraMap (𝓞 K) K d) = 1 := by
      have h := (NumberField.FinitePlace.norm_eq_one_iff_notMem
        K p.maximalIdeal (d : 𝓞 K)).mpr d.property
      rwa [NumberField.FinitePlace.norm_embedding_eq] at h
    have hd : (S.ϕ ω) (algebraMap (𝓞 K) K d) = 1 := by
      apply le_antisymm
      · exact NumberField.abs_le_one_of_isIntegral hω
          (NumberField.RingOfIntegers.isIntegral_coe (d : 𝓞 K))
      · apply not_lt.mp
        intro hlt
        have hplt := hp.lt_one_iff.mp hlt
        rw [hpd] at hplt
        exact (lt_irrefl 1) hplt
    apply (Valuation.integer.integers (S.rationalValuation ω hω)).isUnit_iff_valuation_eq_one.mpr
    exact Subtype.ext hd
  · intro x
    have hv : p.maximalIdeal.valuation K (x : K) ≤ 1 := by
      apply (Valuation.mem_integer_iff _ _).mp
      rw [← S.rationalLocalRing_eq_finitePlaceInteger ω hω p hp]
      exact x.property
    obtain ⟨m, d, hmd⟩ := p.maximalIdeal.exists_primeCompl_mul_eq_of_integer (x : K) hv
    refine ⟨(m, d), ?_⟩
    exact Subtype.ext hmd
  · intro a b hab
    have heq : a = b := (IsFractionRing.injective (𝓞 K) K)
      (congrArg (fun r : S.rationalLocalRing ω hω ↦ (r : K)) hab)
    exact ⟨1, congrArg (fun c : 𝓞 K ↦ 1 * c) heq⟩

/-- Nontriviality produces both the actual classified finite prime and the
actual integer-ring localization identification; neither is an endpoint premise. -/
theorem exists_finitePlace_rationalLocalRing_localization [NumberField K] (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) :
    ∃ p : NumberField.FinitePlace K, (S.ϕ ω).IsEquiv p.val ∧
      IsLocalization p.maximalIdeal.asIdeal.primeCompl (S.rationalLocalRing ω hω) := by
  obtain ⟨p, hp⟩ := NumberField.exists_finitePlace_of_isNonarchimedean hnt hω
  exact ⟨p, hp, S.isLocalization_rationalLocalRing_of_finitePlace ω hω p hp⟩

/-- The actual local coefficient is a field fraction with denominator outside
its actual finite prime, obtained by consuming the proved ring localization. -/
theorem exists_integral_denominator_outside_finitePlace [NumberField K]
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) (p : NumberField.FinitePlace K)
    (hp : (S.ϕ ω).IsEquiv p.val) (x : S.rationalLocalRing ω hω) :
    ∃ (m : 𝓞 K) (d : p.maximalIdeal.asIdeal.primeCompl),
      (x : K) * algebraMap (𝓞 K) K d = algebraMap (𝓞 K) K m := by
  let := S.isLocalization_rationalLocalRing_of_finitePlace ω hω p hp
  obtain ⟨⟨m, d⟩, hmd⟩ := IsLocalization.surj p.maximalIdeal.asIdeal.primeCompl x
  exact ⟨m, d, congrArg (fun r : S.rationalLocalRing ω hω ↦ (r : K)) hmd⟩

end ArakelovGeometry.AdelicStructure

namespace ArakelovGeometry.NormFamily

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E]

/-- Integral scalars act through the proved canonical coefficient map on the
existing actual local unit-ball module. -/
noncomputable instance rationalUnitBall_integralModule (ξ : NormFamily S E)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) [hξ : ξ.IsUltrametricAtFinitePlaces] :
    Module (𝓞 K) (ξ.rationalUnitBallModule ω hω) :=
  Module.compHom (ξ.rationalUnitBallModule ω hω) (S.integralLocalCoefficientMap ω hω)

instance rationalUnitBall_integralScalarTower (ξ : NormFamily S E)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) [hξ : ξ.IsUltrametricAtFinitePlaces] :
    IsScalarTower (𝓞 K) (S.rationalLocalRing ω hω) (ξ.rationalUnitBallModule ω hω) := by
  constructor
  intro a r x
  change (S.integralLocalCoefficientMap ω hω a * r) • x =
    S.integralLocalCoefficientMap ω hω a • (r • x)
  exact mul_smul _ _ _

@[simp]
theorem rationalUnitBall_integral_smul_coe (ξ : NormFamily S E)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) [hξ : ξ.IsUltrametricAtFinitePlaces]
    (a : 𝓞 K) (x : ξ.rationalUnitBallModule ω hω) :
    ((a • x : ξ.rationalUnitBallModule ω hω) : E) =
      algebraMap (𝓞 K) K a • (x : E) := rfl

/-- The actual rational local unit ball, restricted to integral coefficients,
is already a localized module at its actual finite prime. -/
theorem isLocalizedModule_rationalUnitBall_of_finitePlace [NumberField K] (ξ : NormFamily S E)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) [hξ : ξ.IsUltrametricAtFinitePlaces]
    (p : NumberField.FinitePlace K) (hp : (S.ϕ ω).IsEquiv p.val) :
    IsLocalizedModule p.maximalIdeal.asIdeal.primeCompl
      (LinearMap.id : ξ.rationalUnitBallModule ω hω →ₗ[𝓞 K]
        ξ.rationalUnitBallModule ω hω) := by
  let := S.isLocalization_rationalLocalRing_of_finitePlace ω hω p hp
  exact isLocalizedModule_id p.maximalIdeal.asIdeal.primeCompl
    (ξ.rationalUnitBallModule ω hω) (S.rationalLocalRing ω hω)

/-- The actual integer-to-local coefficient scalar extension of the genuine
rational unit ball recovers that actual local module. -/
noncomputable def rationalUnitBallIntegerLocalizationEquiv [NumberField K] (ξ : NormFamily S E)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) [hξ : ξ.IsUltrametricAtFinitePlaces]
    (p : NumberField.FinitePlace K) (hp : (S.ϕ ω).IsEquiv p.val) :
    (S.rationalLocalRing ω hω) ⊗[𝓞 K] (ξ.rationalUnitBallModule ω hω) ≃ₗ[
      S.rationalLocalRing ω hω] ξ.rationalUnitBallModule ω hω := by
  letI := S.isLocalization_rationalLocalRing_of_finitePlace ω hω p hp
  letI := ξ.isLocalizedModule_rationalUnitBall_of_finitePlace ω hω p hp
  exact (IsLocalizedModule.isBaseChange p.maximalIdeal.asIdeal.primeCompl
    (S.rationalLocalRing ω hω) (LinearMap.id :
      ξ.rationalUnitBallModule ω hω →ₗ[𝓞 K] ξ.rationalUnitBallModule ω hω)).equiv

@[simp]
theorem rationalUnitBallIntegerLocalizationEquiv_tmul [NumberField K] (ξ : NormFamily S E)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) [hξ : ξ.IsUltrametricAtFinitePlaces]
    (p : NumberField.FinitePlace K) (hp : (S.ϕ ω).IsEquiv p.val)
    (r : S.rationalLocalRing ω hω) (x : ξ.rationalUnitBallModule ω hω) :
    ξ.rationalUnitBallIntegerLocalizationEquiv ω hω p hp (r ⊗ₜ[𝓞 K] x) = r • x := by
  let := S.isLocalization_rationalLocalRing_of_finitePlace ω hω p hp
  let := ξ.isLocalizedModule_rationalUnitBall_of_finitePlace ω hω p hp
  exact IsBaseChange.equiv_tmul
    (IsLocalizedModule.isBaseChange p.maximalIdeal.asIdeal.primeCompl
      (S.rationalLocalRing ω hω) (LinearMap.id :
        ξ.rationalUnitBallModule ω hω →ₗ[𝓞 K] ξ.rationalUnitBallModule ω hω)) r x

end ArakelovGeometry.NormFamily
