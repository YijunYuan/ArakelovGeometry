/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NormFamilyDominatedPrimeThresholds
import ArakelovGeometry.NumberTheory.ValuationModuleFinite
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Actual rounded valuation modules from lower domination

The weighted threshold producer supplies finite positive support for the
actual nonzero-prime bound family in the rank-one proof of Proposition 4.4.6.
This file consumes that support to produce an actual common denominator and
actual module finite generation. The arithmetic indexing/gap hypotheses and
the separate literal-norm identification boundary are explicit.
-/

open scoped NumberField

namespace ArakelovGeometry.NormFamily

universe u v w

variable {K : Type u} [Field K] [NumberField K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E]
  [MeasurableSingletonClass S.Ω] {ξ : NormFamily S E}

/-- The actual prime-order allowance obtained by rounding the actual
completed rational norm with the prescribed positive local scale. -/
noncomputable def roundedPrimeBound (ξ : NormFamily S E) (x : E)
    (e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → S.Ω) (γ : S.Ω → ℝ) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℤ :=
  fun p => -⌈ξ.logNorm x (e p) / γ (e p)⌉

omit [NumberField K] in
/-- Injective actual prime indexing transports the proved weighted-gap
negative ceiling support to finite positive actual prime support. -/
theorem IsLowerDominated.finite_positive_roundedPrimeBound
    (hξ : ξ.IsLowerDominated) (hμ : ∀ ω, 0 < S.v {ω}) {x : E} (hx : x ≠ 0)
    (e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → S.Ω) (he : Function.Injective e)
    (γ : S.Ω → ℝ) (hγ : ∀ p, 0 < γ (e p)) {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ p, ε ≤ S.v.real {e p} * γ (e p)) :
    {p | 0 < ξ.roundedPrimeBound x e γ p}.Finite := by
  have hfinite := hξ.finite_negative_rounded_orders hμ hx (Set.range e) γ
    (fun ω ⟨p, hp⟩ => hp ▸ hγ p) hε (fun ω ⟨p, hp⟩ => hp ▸ hgap p)
  have hpre := Set.Finite.preimage (fun _ _ _ _ h => he h) hfinite
  refine hpre.subset ?_
  intro p hp
  exact ⟨Set.mem_range_self p, neg_pos.mp hp⟩

/-- The rounded actual valuation module has a genuine nonzero actual
integer common denominator, including the possible zero-module case. -/
theorem IsLowerDominated.exists_rounded_valuation_common_denominator
    (hξ : ξ.IsLowerDominated) (hμ : ∀ ω, 0 < S.v {ω}) {x : E} (hx : x ≠ 0)
    (e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → S.Ω) (he : Function.Injective e)
    (γ : S.Ω → ℝ) (hγ : ∀ p, 0 < γ (e p)) {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ p, ε ≤ S.v.real {e p} * γ (e p)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ a ∈ FiniteValuation.valuationModule (K := K)
      (ξ.roundedPrimeBound x e γ),
      algebraMap (𝓞 K) K d * a ∈ (algebraMap (𝓞 K) K).range :=
  FiniteValuation.exists_common_denominator_of_finite_positive
    (hξ.finite_positive_roundedPrimeBound hμ hx e he γ hγ hε hgap)

/-- The actual rounded valuation module is finitely generated; this
conclusion is produced from domination rather than assumed as a certificate. -/
theorem IsLowerDominated.fg_rounded_valuationModule
    (hξ : ξ.IsLowerDominated) (hμ : ∀ ω, 0 < S.v {ω}) {x : E} (hx : x ≠ 0)
    (e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → S.Ω) (he : Function.Injective e)
    (γ : S.Ω → ℝ) (hγ : ∀ p, 0 < γ (e p)) {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ p, ε ≤ S.v.real {e p} * γ (e p)) :
    (FiniteValuation.valuationModule (K := K) (ξ.roundedPrimeBound x e γ)).FG :=
  FiniteValuation.fg_valuationModule_of_finite_positive
    (hξ.finite_positive_roundedPrimeBound hμ hx e he γ hγ hε hgap)

end ArakelovGeometry.NormFamily
