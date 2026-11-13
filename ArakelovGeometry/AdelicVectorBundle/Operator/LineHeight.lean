/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Line
public import ArakelovGeometry.AdelicVectorBundle.Operator.Height

import ArakelovGeometry.AdelicVectorBundle.NormFamily.Line
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Heights of maps from adelic lines

The completed operator norm on a one-dimensional source is its ratio at any
nonzero rational generator. The height of a nonzero map between adelic lines
is consequently the source degree minus the target degree.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F]

namespace NormFamily

/-- Every completed vector of a rational line is a scalar multiple of a
rational generator, so the operator norm is its single evaluation ratio. -/
theorem operatorNorm_eq_div_of_finrank_one (ξ : NormFamily S E) (η : NormFamily S F)
    (hr : Module.finrank K E = 1) (f : E →ₗ[K] F) {x : E} (hx : x ≠ 0) (ω : S.Ω) :
    ξ.operatorNorm η ω f =
      η.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] f x) /
        ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) := by
  have hpos := ξ.norm_rational_pos ω hx
  apply le_antisymm
  · apply ξ.operatorNorm_le η ω f (div_nonneg (η.norm_nonneg ω _) hpos.le)
    intro z
    have hc : Module.finrank (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E) = 1 :=
      Module.finrank_baseChange.trans hr
    have hx' : (1 : (S.ϕ ω).Completion) ⊗ₜ[K] x ≠ 0 :=
      fun h => (ne_of_gt hpos) (h ▸ ξ.norm_zero ω)
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_one hc hx' z
    rw [← ha, map_smul, η.norm_smul, ξ.norm_smul, LinearMap.baseChange_tmul]
    exact le_of_eq (by field_simp)
  · exact (div_le_iff₀ hpos).mpr (by
      simpa only [LinearMap.baseChange_tmul] using
        ξ.norm_baseChange_le_operatorNorm η ω f
          ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x))

/-- On a line, local height is the exact difference of two rational log norms. -/
theorem localHeight_eq_logNorm_sub_of_finrank_one
    (ξ : NormFamily S E) (η : NormFamily S F) (hr : Module.finrank K E = 1)
    (f : {f : E →ₗ[K] F // f ≠ 0}) {x : E} (hx : x ≠ 0) (hfx : f.val x ≠ 0)
    (ω : S.Ω) :
    ξ.localHeight η f ω = η.logNorm (f.val x) ω - ξ.logNorm x ω := by
  dsimp only [localHeight, logNorm]
  rw [ξ.operatorNorm_eq_div_of_finrank_one η hr f.val hx ω,
    Real.log_div (ne_of_gt (η.norm_rational_pos ω hfx))
      (ne_of_gt (ξ.norm_rational_pos ω hx))]

end NormFamily

namespace AdelicVectorBundle

variable [FiniteDimensional K F]

/-- A nonzero map from an adelic line has integrable local height. -/
theorem integrable_localHeight_of_isLine (V : AdelicVectorBundle.{w} S)
    (W : AdelicVectorBundle.{w'} S) [hV : V.IsLine]
    (f : {f : V →ₗ[K] W // f ≠ 0}) :
    Integrable (V.toNormFamily.localHeight W.toNormFamily f) S.v := by
  obtain ⟨x, hx⟩ : ∃ x, f.val x ≠ 0 := by
    by_contra! h
    exact f.property (LinearMap.ext h)
  have hx0 : x ≠ 0 := fun h => hx (by rw [h, map_zero])
  have he : V.toNormFamily.localHeight W.toNormFamily f =
      fun ω => W.toNormFamily.logNorm (f.val x) ω - V.toNormFamily.logNorm x ω :=
    funext (V.toNormFamily.localHeight_eq_logNorm_sub_of_finrank_one
      W.toNormFamily hV.rank_eq_one f hx0 hx)
  rw [he]
  exact (W.isDominated.integrable_logNorm W.isMeasurable _).sub
    (V.isDominated.integrable_logNorm V.isMeasurable _)

/-- The height of a nonzero line map is the source degree minus target degree. -/
theorem mapHeight_eq_lineDegree_sub [S.IsProper]
    (V : AdelicVectorBundle.{w} S) (W : AdelicVectorBundle.{w'} S)
    [hV : V.IsLine] [hW : W.IsLine] {f : V →ₗ[K] W} (hf : f ≠ 0) :
    V.mapHeight W f = ((V.lineDegree - W.lineDegree : ℝ) : EReal) := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra! h
    exact hf (LinearMap.ext h)
  have hx0 : x ≠ 0 := fun h => hx (by rw [h, map_zero])
  rw [V.mapHeight_eq_integral W hf (V.integrable_localHeight_of_isLine W ⟨f, hf⟩),
    V.lineDegree_eq_neg_integral ⟨x, hx0⟩,
    W.lineDegree_eq_neg_integral ⟨f x, hx⟩]
  simp_rw [V.toNormFamily.localHeight_eq_logNorm_sub_of_finrank_one
    W.toNormFamily hV.rank_eq_one ⟨f, hf⟩ hx0 hx]
  rw [integral_sub (W.isDominated.integrable_logNorm W.isMeasurable _)
    (V.isDominated.integrable_logNorm V.isMeasurable _)]
  congr 1
  ring

end AdelicVectorBundle

end ArakelovGeometry
