/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Basic
public import ArakelovGeometry.AdelicVectorBundle.Measurability.Density.Basic
public import ArakelovGeometry.AdelicVectorBundle.Operator.Norm

import ArakelovGeometry.AdelicVectorBundle.Operator.Measurable
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Local and global heights of linear maps

The local height is the logarithm of the actual completed operator norm and
is defined for nonzero rational maps. Its integrable lower envelope comes from
one rational vector with nonzero image. The global height uses the genuine
lower envelope integral, with the separate zero-map convention `⊥`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped TensorProduct

namespace ArakelovGeometry

universe u w w'

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F]

namespace NormFamily

/-- Source Definition4.3.15, restricted to nonzero maps as stipulated there. -/
noncomputable def localHeight (ξ : NormFamily S E) (η : NormFamily S F)
    (f : {f : E →ₗ[K] F // f ≠ 0}) (ω : S.Ω) : ℝ :=
  Real.log (ξ.operatorNorm η ω f.val)

/-- Exponentiating the local height recovers the positive completed operator norm. -/
theorem exp_localHeight (ξ : NormFamily S E) (η : NormFamily S F)
    (f : {f : E →ₗ[K] F // f ≠ 0}) (ω : S.Ω) :
    Real.exp (ξ.localHeight η f ω) = ξ.operatorNorm η ω f.val :=
  Real.exp_log (ξ.operatorNorm_pos η ω f.property)

/-- The exact base hypotheses make local map heights measurable. -/
theorem IsMeasurable.localHeight_of_discrete_or_countable
    {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsMeasurable) (hη : η.IsMeasurable)
    [hS : S.HasMeasurableBase]
    (f : {f : E →ₗ[K] F // f ≠ 0}) : Measurable (ξ.localHeight η f) :=
  (hξ.operatorNorm_of_discrete_or_countable hη f.val).log

/-- Any rational vector with nonzero image gives a pointwise lower bound. -/
theorem logNorm_sub_le_localHeight (ξ : NormFamily S E) (η : NormFamily S F)
    (f : {f : E →ₗ[K] F // f ≠ 0}) {x : E} (hx : f.val x ≠ 0) (ω : S.Ω) :
    η.logNorm (f.val x) ω - ξ.logNorm x ω ≤ ξ.localHeight η f ω := by
  have hx0 : x ≠ 0 := by
    intro h
    exact hx (by rw [h, map_zero])
  have hb := ξ.norm_baseChange_le_operatorNorm η ω f.val
    ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x)
  simp only [LinearMap.baseChange_tmul] at hb
  have hlog := Real.log_le_log (η.norm_rational_pos ω hx) hb
  rw [Real.log_mul (ne_of_gt (ξ.operatorNorm_pos η ω f.property))
    (ne_of_gt (ξ.norm_rational_pos ω hx0))] at hlog
  exact (sub_le_iff_le_add).mpr hlog

end NormFamily

namespace AdelicVectorBundle

variable [FiniteDimensional K F]

/-- Domination and measurability of the two actual families give a genuine
integrable lower envelope; no countability hypothesis is needed for this bound. -/
theorem localHeight_hasIntegrableLowerBound (V : AdelicVectorBundle S)
    (W : AdelicVectorBundle S) (f : {f : V →ₗ[K] W // f ≠ 0}) :
    HasIntegrableLowerBound (V.toNormFamily.localHeight W.toNormFamily f) S.v := by
  obtain ⟨x, hx⟩ : ∃ x, f.val x ≠ 0 := by
    by_contra! h
    exact f.property (LinearMap.ext h)
  exact ⟨fun ω => W.toNormFamily.logNorm (f.val x) ω - V.toNormFamily.logNorm x ω,
    (W.isDominated.integrable_logNorm W.isMeasurable _).sub
      (V.isDominated.integrable_logNorm V.isMeasurable _),
    Eventually.of_forall (V.toNormFamily.logNorm_sub_le_localHeight W.toNormFamily f hx)⟩

/-- Source Definition4.3.17 uses the lower envelope integral. The value for
zero is an explicit convention, not the real logarithm of its zero norm. -/
noncomputable def mapHeight (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    (f : V →ₗ[K] W) : EReal := by
  classical
  exact if hf : f = 0 then ⊥ else
    lowerEnvelopeIntegral (V.toNormFamily.localHeight W.toNormFamily ⟨f, hf⟩) S.v

@[simp]
theorem mapHeight_zero (V : AdelicVectorBundle S) (W : AdelicVectorBundle S) :
    V.mapHeight W 0 = ⊥ := by
  simp [mapHeight]

/-- The height of a nonzero map is exactly the stipulated lower integral. -/
theorem mapHeight_eq_lowerEnvelopeIntegral (V : AdelicVectorBundle S)
    (W : AdelicVectorBundle S) {f : V →ₗ[K] W} (hf : f ≠ 0) :
    V.mapHeight W f =
      lowerEnvelopeIntegral (V.toNormFamily.localHeight W.toNormFamily ⟨f, hf⟩) S.v := by
  simp [mapHeight, hf]

/-- A nonzero map has height strictly greater than negative infinity. -/
theorem bot_lt_mapHeight (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    {f : V →ₗ[K] W} (hf : f ≠ 0) : ⊥ < V.mapHeight W f := by
  rw [V.mapHeight_eq_lowerEnvelopeIntegral W hf]
  exact hasIntegrableLowerBound_iff_bot_lt_lowerEnvelopeIntegral.mp
    (V.localHeight_hasIntegrableLowerBound W ⟨f, hf⟩)

/-- Once integrability is proved, the genuine lower integral equals the ordinary integral. -/
theorem mapHeight_eq_integral (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    {f : V →ₗ[K] W} (hf : f ≠ 0)
    (hi : Integrable (V.toNormFamily.localHeight W.toNormFamily ⟨f, hf⟩) S.v) :
    V.mapHeight W f = (∫ ω, V.toNormFamily.localHeight W.toNormFamily ⟨f, hf⟩ ω ∂S.v : ℝ) := by
  rw [V.mapHeight_eq_lowerEnvelopeIntegral W hf]
  exact lowerEnvelopeIntegral_eq_integral hi

end AdelicVectorBundle

end ArakelovGeometry
