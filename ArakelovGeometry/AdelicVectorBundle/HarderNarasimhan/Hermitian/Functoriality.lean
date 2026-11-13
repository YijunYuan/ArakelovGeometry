/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Basic
public import ArakelovGeometry.AdelicVectorBundle.Operator.Height

import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Truncations
import ArakelovGeometry.AdelicVectorBundle.Operator.StrongHeight
import ArakelovGeometry.AdelicVectorBundle.Slope.Extension
import ArakelovGeometry.AdelicVectorBundle.Slope.LinearMap
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Functoriality of the actual Hermitian Harder--Narasimhan filtration

Nonzero maps between Hermitian adelic bundles have finite genuine map height.
Restriction of the source and quotient of the target decrease that height.
The actual HN truncation slope bounds then imply the height-shifted image inclusion.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct BigOperators

namespace ArakelovGeometry

noncomputable section

universe u w w'

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} {F : Type w'} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace NormFamily

/-- Restriction of the source followed by an actual target quotient
cannot increase the operator norm on any completed fibre. -/
theorem operatorNorm_restrict_postQuotient_le (ξ : NormFamily S E) (η : NormFamily S F)
    (f : E →ₗ[K] F) (U : Submodule K E) (T : Submodule K F) (ω : S.Ω) :
    (ξ.restrict U).operatorNorm (η.quotient T) ω (T.mkQ.comp (f.comp U.subtype)) ≤
      ξ.operatorNorm η ω f := by
  apply (ξ.restrict U).operatorNorm_le (η.quotient T) ω _
    (ξ.operatorNorm_nonneg η ω f)
  intro z
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply]
  exact (η.quotient_norm_mk_le T ω _).trans (ξ.norm_baseChange_le_operatorNorm η ω f _)


end NormFamily

namespace AdelicVectorBundle

variable [S.IsProper] (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]
  [hV : V.toNormFamily.IsHermitian] [hW : W.toNormFamily.IsHermitian]
include hS hN hV hW

omit [S.IsProper] in
/-- A nonzero map between the actual Hermitian bundles has its genuine
lower-integral height equal to a finite real integral. -/
theorem mapHeight_eq_integral_of_isHermitian (f : V →ₗ[K] W) (hf : f ≠ 0) :
    V.mapHeight W f =
      ((∫ ω, V.toNormFamily.localHeight W.toNormFamily ⟨f, hf⟩ ω ∂S.v) : ℝ) := by
  exact V.mapHeight_eq_integral_of_isStronglyAdelic W
    (hV := (IsHermitian.isStronglyAdelic hV)) (hW := (IsHermitian.isStronglyAdelic hW)) hf

omit [S.IsProper] in
/-- The real coordinate of a nonzero actual Hermitian map height is
faithful: both infinite endpoints have been excluded by the produced integral. -/
theorem mapHeight_eq_coe_toReal_of_isHermitian (f : V →ₗ[K] W) (hf : f ≠ 0) :
    V.mapHeight W f = ((V.mapHeight W f).toReal : ℝ) := by
  rw [V.mapHeight_eq_integral_of_isHermitian W f hf, EReal.toReal_coe]

omit hN hV hW [S.IsProper] in
/-- The genuine height of the map from an actual restricted subspace to an
actual target quotient is bounded by the original map's genuine height. -/
theorem mapHeight_restrict_postQuotient_le (f : V →ₗ[K] W) (hf : f ≠ 0)
    (U : Submodule K V) (T : Submodule K W)
    (hg : T.mkQ.comp (f.comp U.subtype) ≠ 0) :
    (V.restrictOfNormMeasurability U).mapHeight (W.quotientOfNormMeasurability T)
      (T.mkQ.comp (f.comp U.subtype)) ≤ V.mapHeight W f := by
  apply V.mapHeight_le_of_operatorNorm_le W _ _ f _ hf hg
  intro ω
  exact V.toNormFamily.operatorNorm_restrict_postQuotient_le W.toNormFamily f U T ω



/-- Any actual finite real upper bound for a nonzero map's height gives
the corresponding inclusion of actual HN threshold subspaces. -/
theorem map_hermitianHNFiltration_le_of_mapHeight_le
    (f : V →ₗ[K] W) (hf : f ≠ 0) (c : ℝ) (hh : V.mapHeight W f ≤ (c : EReal)) (t : ℝ) :
    (V.hermitianHNFiltration t).map f ≤
      W.hermitianHNFiltration (t - c) := by
  let U := V.hermitianHNFiltration t
  let T := W.hermitianHNFiltration (t - c)
  let g := T.mkQ.comp (f.comp U.subtype)
  have hg : g = 0 := by
    by_contra hg
    have hm := minimalSlope_sub_mapHeight_le_maximalSlope_of_ne_zero
      (V.restrictOfNormMeasurability U) (W.quotientOfNormMeasurability T) g hg
    have hheight : (V.restrictOfNormMeasurability U).mapHeight
        (W.quotientOfNormMeasurability T) g ≤ (c : EReal) :=
      (V.mapHeight_restrict_postQuotient_le W f hf U T hg).trans hh
    have hlo := V.le_minimalSlope_restrict_hermitianHNFiltration t
    have hhi := W.maximalSlope_quotient_hermitianHNFiltration_lt (t - c)
    have hb : ((t - c : ℝ) : EReal) ≤
        (V.restrictOfNormMeasurability U).minimalSlope -
          (V.restrictOfNormMeasurability U).mapHeight (W.quotientOfNormMeasurability T) g := by
      rw [EReal.coe_sub]
      exact EReal.sub_le_sub hlo hheight
    exact (not_le_of_gt hhi) (hb.trans hm)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  have hz := DFunLike.congr_fun hg (⟨x, hx⟩ : U)
  have he : T.mkQ (f x) = 0 := hz
  exact (Submodule.Quotient.mk_eq_zero T).mp he

/-- A nonzero rational map carries each actual Hermitian HN threshold
subspace into the target threshold shifted by its genuine finite map height. -/
theorem map_hermitianHNFiltration_le (f : V →ₗ[K] W) (hf : f ≠ 0) (t : ℝ) :
    (V.hermitianHNFiltration t).map f ≤
      W.hermitianHNFiltration (t - (V.mapHeight W f).toReal) := by
  exact V.map_hermitianHNFiltration_le_of_mapHeight_le W f hf
    (V.mapHeight W f).toReal
    (V.mapHeight_eq_coe_toReal_of_isHermitian W f hf).le t

omit hW [FiniteDimensional K F] in
/-- The exceptional zero map has zero actual image at every real threshold. -/
theorem map_zero_hermitianHNFiltration (t : ℝ) :
    (V.hermitianHNFiltration t).map (0 : V →ₗ[K] F) = ⊥ := by
  simp

end AdelicVectorBundle

end

end ArakelovGeometry
