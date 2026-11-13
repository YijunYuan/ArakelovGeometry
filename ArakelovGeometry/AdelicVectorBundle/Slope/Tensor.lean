/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Tensor.Pair
public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Hermitian

import ArakelovGeometry.AdelicVectorBundle.Degree.Supermodular
import ArakelovGeometry.AdelicVectorBundle.Degree.Tensor
import ArakelovGeometry.AdelicVectorBundle.Degree.TensorHermitian
import ArakelovGeometry.AdelicVectorBundle.Slope.Finite
import ArakelovGeometry.AdelicVectorBundle.Slope.LinearMap
import ArakelovGeometry.AdelicVectorBundle.Tensor.PairMap
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.RingTheory.Flat.Basic

/-!
# Slopes of actual binary tensor bundles

The mixed tensor mean inequality is the corrected source Proposition 4.3.34.
The orthogonal Hermitian tensor has equality. Mean slope comparisons require
both factors to have positive rank; a zero tensor has mean slope zero.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u v w wF

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} {F : Type wF} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  (V : AdelicVectorBundle.{w} S) (W : AdelicVectorBundle.{wF} S)
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]

/-- The corrected mixed tensor mean slope comparison, with both rank guards. -/
theorem slope_add_slope_le_slope_mixedTensorPair
    (hE : 0 < Module.finrank K V) (hF : 0 < Module.finrank K W) :
    V.slope + W.slope ≤ (V.mixedTensorPair W).slope := by
  have he : (0 : ℝ) < Module.finrank K V := Nat.cast_pos.mpr hE
  have hf : (0 : ℝ) < Module.finrank K W := Nat.cast_pos.mpr hF
  have hw := V.rank_mul_degree_add_rank_mul_degree_le_degree_mixedTensorPair W
  unfold slope
  rw [Module.finrank_tensorProduct, Nat.cast_mul]
  apply (le_div_iff₀ (mul_pos he hf)).mpr
  have ha : (V.degree / (Module.finrank K V : ℝ) +
      W.degree / (Module.finrank K W : ℝ)) *
        ((Module.finrank K V : ℝ) * (Module.finrank K W : ℝ)) =
      (Module.finrank K W : ℝ) * V.degree +
        (Module.finrank K V : ℝ) * W.degree := by
    field_simp
  rwa [ha]

/-- The Hermitian orthogonal tensor mean slope is the sum of the factor means. -/
theorem slope_orthogonalTensorPair [hV : V.IsHermitian] [hW : W.IsHermitian]
    (hE : 0 < Module.finrank K V) (hF : 0 < Module.finrank K W) :
    (V ⊗ʰ W).slope =
      V.slope + W.slope := by
  have he : (Module.finrank K V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hE)
  have hf : (Module.finrank K W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hF)
  unfold slope
  rw [V.degree_orthogonalTensorPair W,
    Module.finrank_tensorProduct, Nat.cast_mul]
  field_simp

/-- A mixed tensor with a zero left factor has the source's zero mean convention. -/
theorem slope_mixedTensorPair_eq_zero_of_left_finrank_eq_zero
    (hE : Module.finrank K V = 0) : (V.mixedTensorPair W).slope = 0 := by
  apply slope_eq_zero_of_finrank_eq_zero
  rw [Module.finrank_tensorProduct, hE, zero_mul]

/-- A mixed tensor with a zero right factor has mean slope zero. -/
theorem slope_mixedTensorPair_eq_zero_of_right_finrank_eq_zero
    (hF : Module.finrank K W = 0) : (V.mixedTensorPair W).slope = 0 := by
  apply slope_eq_zero_of_finrank_eq_zero
  rw [Module.finrank_tensorProduct, hF, mul_zero]

/-- The zero left factor convention also applies to actual Hermitian tensors. -/
theorem slope_orthogonalTensorPair_eq_zero_of_left_finrank_eq_zero
    [hV : V.IsHermitian] [hW : W.IsHermitian] (hE : Module.finrank K V = 0) :
    (V ⊗ʰ W).slope = 0 := by
  apply slope_eq_zero_of_finrank_eq_zero
  rw [Module.finrank_tensorProduct, hE, zero_mul]

/-- The zero right factor convention also applies to actual Hermitian tensors. -/
theorem slope_orthogonalTensorPair_eq_zero_of_right_finrank_eq_zero
    [hV : V.IsHermitian] [hW : W.IsHermitian] (hF : Module.finrank K W = 0) :
    (V ⊗ʰ W).slope = 0 := by
  apply slope_eq_zero_of_finrank_eq_zero
  rw [Module.finrank_tensorProduct, hF, mul_zero]

/-- The actual tensor inclusion compares the means of any two positive-rank
subspaces with the maximal slope of the ambient mixed tensor bundle. -/
theorem restrict_slope_add_restrict_slope_le_maximalSlope_mixedTensorPair
    (U : Submodule K V) (T : Submodule K W)
    (hU : 0 < Module.finrank K U) (hT : 0 < Module.finrank K T) :
    ((V.restrictOfMeasurableBase U).slope : EReal) +
      ((W.restrictOfMeasurableBase T).slope : EReal) ≤
        (V.mixedTensorPair W).maximalSlope := by
  let P := V.restrictOfMeasurableBase U
  let Q := W.restrictOfMeasurableBase T
  let A := P.mixedTensorPair Q
  let B := V.mixedTensorPair W
  let f := TensorProduct.map U.subtype T.subtype
  have hr : 0 < Module.finrank K (U ⊗[K] T) := by
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos hU hT
  have hf : Function.Injective f := TensorProduct.map_injective_of_flat_flat
    U.subtype T.subtype U.subtype_injective T.subtype_injective
  have hh : A.mapHeight B f ≤ 0 := A.mapHeight_le_zero_of_completed_contraction B f
    (fun ω z ↦ V.toNormFamily.mixedTensorPair_restrict_map_norm_le W.toNormFamily U T ω z)
  have hm := A.maximalSlope_le_maximalSlope_add_mapHeight_of_injective B f hf
  have hs := EReal.coe_le_coe (P.slope_add_slope_le_slope_mixedTensorPair Q hU hT)
  rw [EReal.coe_add] at hs
  exact hs.trans ((A.slope_le_maximalSlope hr).trans
    (hm.trans ((add_le_add le_rfl hh).trans_eq (add_zero _))))

/-- Source equation (4.54) on the actual mixed tensor, without attainment
assumptions. Two independent suprema are compared in extended real arithmetic. -/
theorem maximalSlope_add_maximalSlope_le_maximalSlope_mixedTensorPair :
    V.maximalSlope + W.maximalSlope ≤
      (V.mixedTensorPair W).maximalSlope := by
  by_cases hE : Module.finrank K V = 0
  · rw [V.maximalSlope_eq_bot_of_finrank_eq_zero hE, EReal.bot_add]
    exact bot_le
  by_cases hF : Module.finrank K W = 0
  · rw [W.maximalSlope_eq_bot_of_finrank_eq_zero hF, EReal.add_bot]
    exact bot_le
  have hb : V.maximalSlope ≠ ⊥ :=
    ne_of_gt (V.bot_lt_maximalSlope (Nat.pos_of_ne_zero hE))
  have ht : V.maximalSlope ≠ ⊤ := ne_of_lt (V.maximalSlope_lt_top)
  rw [add_comm]
  apply (EReal.le_sub_iff_add_le (Or.inl hb) (Or.inl ht)).mp
  apply W.maximalSlope_le
  intro T hT
  apply (EReal.le_sub_iff_add_le (Or.inl hb) (Or.inl ht)).mpr
  rw [add_comm]
  apply (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mp
  apply V.maximalSlope_le
  intro U hU
  apply (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mpr
  exact V.restrict_slope_add_restrict_slope_le_maximalSlope_mixedTensorPair W U T hU hT

/-- Positive-rank Hermitian subspaces use their actual orthogonal tensor norm,
whose completed tensor inclusion contracts on every vector. -/
theorem restrict_slope_add_restrict_slope_le_maximalSlope_orthogonalTensorPair
    [hV : V.IsHermitian] [hW : W.IsHermitian]
    (U : Submodule K V) (T : Submodule K W)
    (hU : 0 < Module.finrank K U) (hT : 0 < Module.finrank K T) :
    ((V.restrictOfMeasurableBase U).slope : EReal) +
      ((W.restrictOfMeasurableBase T).slope : EReal) ≤
        (V ⊗ʰ W).maximalSlope := by
  let P := V.restrictOfMeasurableBase U
  let Q := W.restrictOfMeasurableBase T
  have hP : P.IsHermitian := NormFamily.IsHermitian.restrict hV U
  have hQ : Q.IsHermitian := NormFamily.IsHermitian.restrict hW T
  let A := P.orthogonalTensorPair Q (hV := hP) (hW := hQ)
  let B := V.orthogonalTensorPair W
  let f := TensorProduct.map U.subtype T.subtype
  have hr : 0 < Module.finrank K (U ⊗[K] T) := by
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos hU hT
  have hf : Function.Injective f := TensorProduct.map_injective_of_flat_flat
    U.subtype T.subtype U.subtype_injective T.subtype_injective
  have hh : A.mapHeight B f ≤ 0 := A.mapHeight_le_zero_of_completed_contraction B f
    (fun ω z ↦ V.toNormFamily.orthogonalTensorPair_restrict_map_norm_le
      W.toNormFamily U T ω z)
  have hm := A.maximalSlope_le_maximalSlope_add_mapHeight_of_injective B f hf
  have hs : ((P.slope + Q.slope : ℝ) : EReal) = (A.slope : EReal) :=
    congrArg (fun x : ℝ ↦ (x : EReal))
      (P.slope_orthogonalTensorPair Q (hV := hP) (hW := hQ) hU hT).symm
  rw [EReal.coe_add] at hs
  exact hs.le.trans ((A.slope_le_maximalSlope hr).trans
    (hm.trans ((add_le_add le_rfl hh).trans_eq (add_zero _))))

/-- Source equation (4.55) for the actual orthogonal Hermitian tensor bundle,
including the negative-infinite maximal slope of every zero-factor tensor. -/
theorem maximalSlope_add_maximalSlope_le_maximalSlope_orthogonalTensorPair
    [hV : V.IsHermitian] [hW : W.IsHermitian] :
    V.maximalSlope + W.maximalSlope ≤
      (V ⊗ʰ W).maximalSlope := by
  by_cases hE : Module.finrank K V = 0
  · rw [V.maximalSlope_eq_bot_of_finrank_eq_zero hE, EReal.bot_add]
    exact bot_le
  by_cases hF : Module.finrank K W = 0
  · rw [W.maximalSlope_eq_bot_of_finrank_eq_zero hF, EReal.add_bot]
    exact bot_le
  have hb : V.maximalSlope ≠ ⊥ :=
    ne_of_gt (V.bot_lt_maximalSlope (Nat.pos_of_ne_zero hE))
  have ht : V.maximalSlope ≠ ⊤ := ne_of_lt (V.maximalSlope_lt_top)
  rw [add_comm]
  apply (EReal.le_sub_iff_add_le (Or.inl hb) (Or.inl ht)).mp
  apply W.maximalSlope_le
  intro T hT
  apply (EReal.le_sub_iff_add_le (Or.inl hb) (Or.inl ht)).mpr
  rw [add_comm]
  apply (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mp
  apply V.maximalSlope_le
  intro U hU
  apply (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mpr
  exact V.restrict_slope_add_restrict_slope_le_maximalSlope_orthogonalTensorPair
    W U T hU hT

end

end ArakelovGeometry.AdelicVectorBundle
