/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Operator.Height
public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic

import ArakelovGeometry.AdelicVectorBundle.Slope.Finite
import ArakelovGeometry.AdelicVectorBundle.Slope.LinearMap
import ArakelovGeometry.AdelicVectorBundle.Slope.Quotient
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Minimal slope in an actual extension

Source Proposition 4.3.32 follows by testing every nonzero actual quotient.
A quotient either detects the given linear map or factors through its
cokernel with the same actual quotient norm. This argument proves the bound
for all linear maps, hence in particular for the source's injective maps.
Extended-real heights and zero quotients are retained throughout.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace NormFamily

/-- Factoring a quotient by an included kernel preserves the actual
quotient norm on every completed vector, by actual pushforward composition. -/
theorem pushforward_factor_norm_eq (ξ : NormFamily S E) (U W : Submodule K E)
    (h : U ≤ W) (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] (E ⧸ W)) :
    ((ξ.quotient U).pushforward (Submodule.factor h)
      (Submodule.factor_surjective h)).norm ω z = (ξ.quotient W).norm ω z := by
  have hc : (Submodule.factor h).comp U.mkQ = W.mkQ := by
    ext x
    exact Submodule.factor_mk h x
  change ((ξ.pushforward U.mkQ U.mkQ_surjective).pushforward (Submodule.factor h)
    (Submodule.factor_surjective h)).norm ω z = (ξ.pushforward W.mkQ W.mkQ_surjective).norm ω z
  rw [ξ.pushforward_comp_norm]
  simp only [hc]

end NormFamily

namespace AdelicVectorBundle

variable [S.IsProper]

/-- The subtraction form of the actual nonzero-map slope comparison.
The target maximal slope is a finite real; the map height may be `⊤`. -/
theorem minimalSlope_sub_mapHeight_le_maximalSlope_of_ne_zero
    (V : AdelicVectorBundle.{w} S) (W : AdelicVectorBundle.{w'} S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (f : V →ₗ[K] W) (hf : f ≠ 0) :
    V.minimalSlope - V.mapHeight W f ≤ W.maximalSlope := by
  have hr : 0 < Module.finrank K f.range := Nat.pos_of_ne_zero (fun hz ↦
    hf (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)))
  have hF : 0 < Module.finrank K W := hr.trans_le f.range.finrank_le
  apply (EReal.sub_le_iff_le_add
    (Or.inr (W.maximalSlope_lt_top).ne)
    (Or.inr (W.bot_lt_maximalSlope hF).ne')).mpr
  exact V.minimalSlope_le_maximalSlope_add_mapHeight_of_ne_zero W f hf

/-- A larger quotient kernel gives an actual quotient of the smaller-kernel
quotient. Its maximal slope bounds that bundle's source minimal slope. -/
theorem minimalSlope_quotient_le_maximalSlope_quotient_of_le
    (V : AdelicVectorBundle S) (U W : Submodule K V) (h : U ≤ W)
    (hW : 0 < Module.finrank K (V ⧸ W))
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (V.quotientOfMeasurableBase U).minimalSlope ≤
      (V.quotientOfMeasurableBase W).maximalSlope := by
  let P := V.quotientOfMeasurableBase U
  let π := Submodule.factor h
  let hm := P.isMeasurable.pushforward_of_discrete_or_countable π
    (Submodule.factor_surjective h)
  have hb := P.minimalSlope_le_maximalSlope_pushforward π
    (Submodule.factor_surjective h) (hm := hm) hW
  have he : (P.pushforward π (Submodule.factor_surjective h) (hm := hm)).maximalSlope =
      (V.quotientOfMeasurableBase W).maximalSlope := by
    apply maximalSlope_eq_of_completed_isometry _ _ (LinearEquiv.refl K (V ⧸ W))
    intro ω z
    change (V.toNormFamily.quotient W).norm ω
      ((LinearEquiv.refl K (V ⧸ W)).toLinearMap.baseChange (S.ϕ ω).Completion z) =
      ((V.toNormFamily.quotient U).pushforward π (Submodule.factor_surjective h)).norm ω z
    simpa only [LinearEquiv.refl_toLinearMap, LinearMap.baseChange_id, LinearMap.id_apply] using
      (V.toNormFamily.pushforward_factor_norm_eq U W h ω z).symm
  exact hb.trans_eq he

/-- Source (4.51), proved for every actual linear map and thus for every
injective extension. The cokernel has the actual quotient norm family. -/
theorem minimalSlope_extension_lowerBound
    (V : AdelicVectorBundle.{w} S) (W : AdelicVectorBundle.{w'} S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (f : V →ₗ[K] W) :
    min (V.minimalSlope - V.mapHeight W f)
        ((W.quotientOfMeasurableBase f.range).minimalSlope) ≤
      W.minimalSlope := by
  apply W.le_minimalSlope
  intro U hU
  let Q := W.quotientOfMeasurableBase U
  let g := U.mkQ.comp f
  by_cases hg : g = 0
  · have hI : f.range ≤ U := by
      have hk : f.range ≤ U.mkQ.ker := LinearMap.range_le_ker_iff.mpr hg
      simpa only [Submodule.ker_mkQ] using hk
    exact (min_le_right _ _).trans
      (W.minimalSlope_quotient_le_maximalSlope_quotient_of_le f.range U hI hU)
  · have hf : f ≠ 0 := by
      intro hz
      apply hg
      simp only [g, hz, LinearMap.comp_zero]
    have hh : V.mapHeight Q g ≤ V.mapHeight W f := by
      apply V.mapHeight_le_of_operatorNorm_le W V Q f g hf hg
      intro ω
      exact V.toNormFamily.operatorNorm_postQuotient_le W.toNormFamily f U ω
    exact (min_le_left _ _).trans ((EReal.sub_le_sub le_rfl hh).trans
      (V.minimalSlope_sub_mapHeight_le_maximalSlope_of_ne_zero Q g hg))

/-- Source Proposition 4.3.32's equality criterion, with the actual
cokernel minimum and without excluding a zero cokernel by assumption. -/
theorem minimalSlope_eq_cokernel_of_minimalSlope_sub_mapHeight_ge
    (V : AdelicVectorBundle.{w} S) (W : AdelicVectorBundle.{w'} S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (f : V →ₗ[K] W)
    (hgap : (W.quotientOfMeasurableBase f.range).minimalSlope ≤
      V.minimalSlope - V.mapHeight W f) :
    W.minimalSlope = (W.quotientOfMeasurableBase f.range).minimalSlope := by
  apply le_antisymm (W.minimalSlope_le_minimalSlope_quotient f.range)
  have h := V.minimalSlope_extension_lowerBound W f
  rwa [min_eq_right hgap] at h

/-- The actual quotient by zero preserves the source minimal slope,
including its positive-infinite rank-zero convention. -/
theorem minimalSlope_quotient_bot (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (V.quotientOfMeasurableBase ⊥).minimalSlope = V.minimalSlope := by
  symm
  let e : V ≃ₗ[K] V ⧸ (⊥ : Submodule K V) :=
    LinearEquiv.ofBijective (⊥ : Submodule K V).mkQ
      ⟨LinearMap.ker_eq_bot.mp (Submodule.ker_mkQ ⊥), Submodule.mkQ_surjective ⊥⟩
  apply minimalSlope_eq_of_completed_isometry _ _ e
  intro ω z
  exact V.toNormFamily.quotient_bot_norm_mk ω z

omit [FiniteDimensional K E] in
/-- If the extension map is zero, its actual cokernel is the original
target isometrically. This covers the source's zero-domain case. -/
theorem minimalSlope_cokernel_eq_of_zero
    (W : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (f : E →ₗ[K] W) (hf : f = 0) :
    (W.quotientOfMeasurableBase f.range).minimalSlope = W.minimalSlope := by
  rw [hf, LinearMap.range_zero]
  exact W.minimalSlope_quotient_bot

/-- The source's zero-domain branch, expressed with its actual dimension:
the cokernel has the original target minimum, also when both spaces vanish. -/
theorem minimalSlope_cokernel_eq_of_source_finrank_eq_zero
    (W : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (f : E →ₗ[K] W) (hE : Module.finrank K E = 0) :
    (W.quotientOfMeasurableBase f.range).minimalSlope = W.minimalSlope := by
  let : Subsingleton E := Module.finrank_zero_iff.mp hE
  apply W.minimalSlope_cokernel_eq_of_zero f
  ext x
  rw [Subsingleton.elim x 0]
  simp only [map_zero]

end AdelicVectorBundle

end ArakelovGeometry
