/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.MapHeight

/-!
# Operator norms under changes of norm

Local distance bounds the change of local map height. Canonical pullback along
a linear equivalence leaves the completed operator norm unchanged.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w w' w''

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- Changing both fibre norms changes the operator norm by at most the two
local-distance factors. The zero map is included. -/
theorem operatorNorm_le_exp_localDist_mul (ξ ξ' : NormFamily S E)
    (η η' : NormFamily S F) (ω : S.Ω) (f : E →ₗ[K] F) :
    ξ.operatorNorm η ω f ≤ Real.exp (ξ.localDist ξ' ω + η.localDist η' ω) *
      ξ'.operatorNorm η' ω f := by
  apply ξ.operatorNorm_le η ω f
    (mul_nonneg (Real.exp_pos _).le (ξ'.operatorNorm_nonneg η' ω f))
  intro x
  have hs := ξ.norm_le_exp_localDist_mul ξ' ω x
  calc
    η.norm ω (f.baseChange (S.ϕ ω).Completion x)
        ≤ Real.exp (η.localDist η' ω) * η'.norm ω (f.baseChange (S.ϕ ω).Completion x) :=
      by simpa only [localDist_comm η' η] using η'.norm_le_exp_localDist_mul η ω _
    _ ≤ Real.exp (η.localDist η' ω) * (ξ'.operatorNorm η' ω f * ξ'.norm ω x) :=
      mul_le_mul_of_nonneg_left (ξ'.norm_baseChange_le_operatorNorm η' ω f x)
        (Real.exp_pos _).le
    _ ≤ Real.exp (η.localDist η' ω) * (ξ'.operatorNorm η' ω f *
        (Real.exp (ξ.localDist ξ' ω) * ξ.norm ω x)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs
        (ξ'.operatorNorm_nonneg η' ω f)) (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_add]; ring

/-- A one-sided bound for logarithmic heights of a nonzero map. -/
theorem localHeight_sub_le_localDist (ξ ξ' : NormFamily S E)
    (η η' : NormFamily S F) (ω : S.Ω) (f : {f : E →ₗ[K] F // f ≠ 0}) :
    ξ.localHeight η f ω - ξ'.localHeight η' f ω ≤
      ξ.localDist ξ' ω + η.localDist η' ω := by
  have h := Real.log_le_log (ξ.operatorNorm_pos η ω f.property)
    (ξ.operatorNorm_le_exp_localDist_mul ξ' η η' ω f.val)
  rw [Real.log_mul (Real.exp_ne_zero _) (ξ'.operatorNorm_pos η' ω f.property).ne',
    Real.log_exp] at h
  exact (sub_le_iff_le_add).mpr h

/-- The absolute change in local height is bounded by the sum of local distances. -/
theorem abs_localHeight_sub_le_localDist (ξ ξ' : NormFamily S E)
    (η η' : NormFamily S F) (ω : S.Ω) (f : {f : E →ₗ[K] F // f ≠ 0}) :
    |ξ.localHeight η f ω - ξ'.localHeight η' f ω| ≤
      ξ.localDist ξ' ω + η.localDist η' ω := by
  apply abs_sub_le_iff.mpr
  refine ⟨ξ.localHeight_sub_le_localDist ξ' η η' ω f, ?_⟩
  simpa only [localDist_comm ξ' ξ, localDist_comm η' η] using
    ξ'.localHeight_sub_le_localDist ξ η' η ω f

omit [FiniteDimensional K F] in
/-- Pullback by a linear equivalence preserves the actual completed operator norm. -/
theorem operatorNorm_comp_equiv {E' : Type w''} [AddCommGroup E'] [Module K E']
    [FiniteDimensional K E'] (ξ : NormFamily S E) (η : NormFamily S F)
    (e : E' ≃ₗ[K] E) (f : E →ₗ[K] F) (ω : S.Ω) :
    (ξ.pullback e.toLinearMap e.injective).operatorNorm η ω (f.comp e.toLinearMap) =
      ξ.operatorNorm η ω f := by
  rw [operatorNorm_eq_sSup, operatorNorm_eq_sSup]
  congr 1
  ext r
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨LinearEquiv.baseChange K (S.ϕ ω).Completion E' E e x, ?_⟩
    simpa only [pullback_norm, LinearMap.baseChange_comp, LinearMap.comp_apply,
      ← LinearEquiv.coe_toLinearMap, LinearEquiv.coe_baseChange] using hx
  · rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := (LinearEquiv.baseChange K (S.ϕ ω).Completion E' E e).surjective x
    refine ⟨y, ?_⟩
    simpa only [pullback_norm, LinearMap.baseChange_comp, LinearMap.comp_apply,
      ← LinearEquiv.coe_toLinearMap, LinearEquiv.coe_baseChange] using hx

end ArakelovGeometry.NormFamily
