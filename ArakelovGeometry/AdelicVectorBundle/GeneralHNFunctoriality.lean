/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.GeneralHN

/-!
# Functoriality of the actual general Harder--Narasimhan filtration

The canonical surjection from an actual restricted subspace to its actual
image restriction has height bounded by the ambient map. The proved
surjective slope inequality and actual greatest-subspace characterization
give functoriality. Infinite height uses the negative-infinite endpoint;
the zero map is treated without shifting by its height.
-/

namespace ArakelovGeometry

noncomputable section

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace AdelicVectorBundle

variable [S.IsProper] (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)

/-- The actual image restriction retains the source restricted minimum
up to any actual real ambient-height bound. A zero image has minimum top;
its zero-map height is never added to that minimum. -/
theorem le_minimalSlope_restrict_map_of_mapHeight_le
    (f : E →ₗ[K] F) (hf : f ≠ 0) (U : Submodule K E)
    (c : ℝ) (hh : V.mapHeight W f ≤ (c : EReal)) (t : ℝ)
    (hU : (t : EReal) ≤ (V.restrictOfMeasurableBase U hS).minimalSlope hS hN) :
    ((t - c : ℝ) : EReal) ≤
      (W.restrictOfMeasurableBase (U.map f) hS).minimalSlope hS hN := by
  let A := V.restrictOfMeasurableBase U hS
  let B := W.restrictOfMeasurableBase (U.map f) hS
  let g := f.submoduleMap U
  by_cases hg : g = 0
  · rw [(A.minimalSlope_target_eq_top_of_zero_surjective B hS hN g
      (f.submoduleMap_surjective U) hg).1]
    exact le_top
  · have hc : (U.map f).subtype.comp g = f.comp U.subtype := by ext x; rfl
    have hheight := V.mapHeight_restriction_le W hS f hf U (U.map f) g hg hc
    have hslope := A.minimalSlope_le_minimalSlope_add_mapHeight_of_surjective B hS hN g
      (f.submoduleMap_surjective U) hg
    rw [EReal.coe_sub]
    apply (EReal.sub_le_iff_le_add
      (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))).mpr
    exact hU.trans (hslope.trans (add_le_add le_rfl (hheight.trans hh)))

/-- Any actual real upper bound for a nonzero map's height transports the
actual general filtration. No Hermitianity or minimum bound on its image
is supplied: the latter is proved through the canonical image surjection. -/
theorem map_generalHNFiltration_le_of_mapHeight_le
    (f : E →ₗ[K] F) (hf : f ≠ 0) (c : ℝ) (hh : V.mapHeight W f ≤ (c : EReal)) (t : ℝ) :
    (V.generalHNFiltration hS hN t).map f ≤ W.generalHNFiltration hS hN (t - c) := by
  apply W.le_generalHNFiltration_of_le_minimalSlope_restrict hS hN _ (t - c)
  exact V.le_minimalSlope_restrict_map_of_mapHeight_le W hS hN f hf _ c hh t
    (V.le_minimalSlope_restrict_generalHNFiltration hS hN t)

/-- Source Proposition 4.3.49 with the full actual extended-real height.
Infinite height gives the true negative-infinite target endpoint. Otherwise
both endpoints are excluded before producing a real height. -/
theorem map_generalHNFiltration_le (f : E →ₗ[K] F) (hf : f ≠ 0) (t : ℝ) :
    (V.generalHNFiltration hS hN t).map f ≤
      W.generalHNFiltrationExtended hS hN ((t : EReal) - V.mapHeight W f) := by
  by_cases ht : V.mapHeight W f = ⊤
  · rw [ht, EReal.sub_top, W.generalHNFiltrationExtended_bot hS hN]
    exact le_top
  · have hb : V.mapHeight W f ≠ ⊥ := (V.bot_lt_mapHeight W hf).ne'
    obtain ⟨c, hc⟩ : ∃ c : ℝ, V.mapHeight W f = (c : EReal) := by
      lift V.mapHeight W f to ℝ using ⟨ht, hb⟩ with c
      exact ⟨c, rfl⟩
    rw [hc, ← EReal.coe_sub, W.generalHNFiltrationExtended_coe hS hN]
    exact V.map_generalHNFiltration_le_of_mapHeight_le W hS hN f hf c hc.le t

omit [FiniteDimensional K F] in
/-- The exceptional zero map has zero actual image at every real level.
No subtraction of its negative-infinite height is evaluated. -/
theorem map_zero_generalHNFiltration (t : ℝ) :
    (V.generalHNFiltration hS hN t).map (0 : E →ₗ[K] F) = ⊥ := by simp

end AdelicVectorBundle

end

end ArakelovGeometry
