/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HermitianHNTruncations
public import ArakelovGeometry.AdelicVectorBundle.StrongMapHeight

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

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E F : Type (max u w)} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
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

variable [S.IsProper] (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hV : V.toNormFamily.IsHermitian hN) (hW : W.toNormFamily.IsHermitian hN)
include hS hN hV hW

omit [S.IsProper] in
/-- A nonzero map between the actual Hermitian bundles has its genuine
lower-integral height equal to a finite real integral. -/
theorem mapHeight_eq_integral_of_isHermitian (f : E →ₗ[K] F) (hf : f ≠ 0) :
    V.mapHeight W f =
      ((∫ ω, V.toNormFamily.localHeight W.toNormFamily ⟨f, hf⟩ ω ∂S.v) : ℝ) := by
  exact V.mapHeight_eq_integral_of_isStronglyAdelic W
    (IsHermitian.isStronglyAdelic hV) (IsHermitian.isStronglyAdelic hW) hS hN hf

omit [S.IsProper] in
/-- The real coordinate of a nonzero actual Hermitian map height is
faithful: both infinite endpoints have been excluded by the produced integral. -/
theorem mapHeight_eq_coe_toReal_of_isHermitian (f : E →ₗ[K] F) (hf : f ≠ 0) :
    V.mapHeight W f = ((V.mapHeight W f).toReal : ℝ) := by
  rw [V.mapHeight_eq_integral_of_isHermitian W hS hN hV hW f hf, EReal.toReal_coe]

omit hN hV hW [S.IsProper] in
/-- The genuine height of the map from an actual restricted subspace to an
actual target quotient is bounded by the original map's genuine height. -/
theorem mapHeight_restrict_postQuotient_le (f : E →ₗ[K] F) (hf : f ≠ 0)
    (U : Submodule K E) (T : Submodule K F)
    (hg : T.mkQ.comp (f.comp U.subtype) ≠ 0) :
    (V.restrictOfMeasurableBase U hS).mapHeight (W.quotientOfMeasurableBase T hS)
      (T.mkQ.comp (f.comp U.subtype)) ≤ V.mapHeight W f := by
  apply V.mapHeight_le_of_operatorNorm_le W _ _ f _ hf hg
  intro ω
  exact V.toNormFamily.operatorNorm_restrict_postQuotient_le W.toNormFamily f U T ω



/-- Any actual finite real upper bound for a nonzero map's height gives
the corresponding inclusion of actual HN threshold subspaces. -/
theorem map_hermitianHNFiltration_le_of_mapHeight_le
    (f : E →ₗ[K] F) (hf : f ≠ 0) (c : ℝ) (hh : V.mapHeight W f ≤ (c : EReal)) (t : ℝ) :
    (V.hermitianHNFiltration hS hN hV t).map f ≤
      W.hermitianHNFiltration hS hN hW (t - c) := by
  let U := V.hermitianHNFiltration hS hN hV t
  let T := W.hermitianHNFiltration hS hN hW (t - c)
  let g := T.mkQ.comp (f.comp U.subtype)
  have hg : g = 0 := by
    by_contra hg
    have hm := minimalSlope_sub_mapHeight_le_maximalSlope_of_ne_zero
      (V.restrictOfMeasurableBase U hS) (W.quotientOfMeasurableBase T hS) hS hN g hg
    have hheight : (V.restrictOfMeasurableBase U hS).mapHeight
        (W.quotientOfMeasurableBase T hS) g ≤ (c : EReal) :=
      (V.mapHeight_restrict_postQuotient_le W hS f hf U T hg).trans hh
    have hlo := V.le_minimalSlope_restrict_hermitianHNFiltration hS hN hV t
    have hhi := W.maximalSlope_quotient_hermitianHNFiltration_lt hS hN hW (t - c)
    have hb : ((t - c : ℝ) : EReal) ≤
        (V.restrictOfMeasurableBase U hS).minimalSlope hS hN -
          (V.restrictOfMeasurableBase U hS).mapHeight (W.quotientOfMeasurableBase T hS) g := by
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
theorem map_hermitianHNFiltration_le (f : E →ₗ[K] F) (hf : f ≠ 0) (t : ℝ) :
    (V.hermitianHNFiltration hS hN hV t).map f ≤
      W.hermitianHNFiltration hS hN hW (t - (V.mapHeight W f).toReal) := by
  exact V.map_hermitianHNFiltration_le_of_mapHeight_le W hS hN hV hW f hf
    (V.mapHeight W f).toReal
    (V.mapHeight_eq_coe_toReal_of_isHermitian W hS hN hV hW f hf).le t

omit hW [FiniteDimensional K F] in
/-- The exceptional zero map has zero actual image at every real threshold. -/
theorem map_zero_hermitianHNFiltration (t : ℝ) :
    (V.hermitianHNFiltration hS hN hV t).map (0 : E →ₗ[K] F) = ⊥ := by
  simp

end AdelicVectorBundle

end

end ArakelovGeometry
