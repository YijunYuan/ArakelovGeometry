/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.GeometryOfNumbers.ConvexBodyPolar
import Mathlib.Analysis.Normed.Operator.Prod

/-! # Actual continuous-dual polars of sections and projections -/

noncomputable section
open Set Topology

namespace ArakelovGeometry.GeometryOfNumbers

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual polar of an actual continuous linear image is the composition pullback. -/
theorem polar_image_eq_preimage_comp (T : E →L[ℝ] F) (C : Set E) :
    StrongDual.polar ℝ (T '' C) =
      (fun f : StrongDual ℝ F => f.comp T) ⁻¹' StrongDual.polar ℝ C := by
  ext f
  constructor
  · intro hf x hx
    exact hf (T x) ⟨x, hx, rfl⟩
  · rintro hf y ⟨x, hx, rfl⟩
    exact hf x hx

/-- The actual second-coordinate projection has the actual pullback polar. -/
theorem polar_projection_snd (C : Set (E × F)) :
    StrongDual.polar ℝ (Prod.snd '' C) =
      (fun f : StrongDual ℝ F => f.comp (ContinuousLinearMap.snd ℝ E F)) ⁻¹'
        StrongDual.polar ℝ C :=
  polar_image_eq_preimage_comp (ContinuousLinearMap.snd ℝ E F) C

/-- Every functional on the actual finite-dimensional continuous dual is actual evaluation. -/
theorem continuousDual_functional_eq_eval [FiniteDimensional ℝ E]
    (G : StrongDual ℝ (StrongDual ℝ E)) : ∃ x : E, ∀ f : StrongDual ℝ E, G f = f x := by
  let q : Module.Dual ℝ (Module.Dual ℝ E) :=
    G.toLinearMap.comp LinearMap.toContinuousLinearMap.toLinearMap
  refine ⟨(Module.evalEquiv ℝ E).symm q, fun f => ?_⟩
  exact (Module.apply_evalEquiv_symm_apply ℝ E f.toLinearMap q).symm

/-- Restricting the actual polar gives precisely the polar of the actual coordinate section. -/
theorem polar_section_restriction_inl [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : Set (E × F)} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ z ∈ C, -z ∈ C) (hzero : (0 : E × F) ∈ interior C) :
    (fun g : StrongDual ℝ (E × F) => g.comp (ContinuousLinearMap.inl ℝ E F)) ''
        StrongDual.polar ℝ C =
      StrongDual.polar ℝ ((fun x : E => (x, (0 : F))) ⁻¹' C) := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩ x hx
    exact hg (x, 0) hx
  · intro hf
    let R : StrongDual ℝ (E × F) →L[ℝ] StrongDual ℝ E :=
      (ContinuousLinearMap.compL ℝ E (E × F) ℝ).flip (ContinuousLinearMap.inl ℝ E F)
    let P : Set (StrongDual ℝ E) := R '' StrongDual.polar ℝ C
    change f ∈ P
    by_contra hfP
    have hPcompact : IsCompact P :=
      (polar_isCompact (mem_interior_iff_mem_nhds.mp hzero)).image R.continuous
    have hPconvex : Convex ℝ P :=
      ((topDualPairing ℝ (E × F)).flip.polar_AbsConvex C).2.linear_image R.toLinearMap
    have hPzero : (0 : StrongDual ℝ E) ∈ P := by
      refine ⟨0, ?_, map_zero R⟩
      intro z hz
      simp
    obtain ⟨G, u, hGu, huf⟩ :=
      geometric_hahn_banach_closed_point hPconvex hPcompact.isClosed hfP
    have hu : 0 < u := by simpa only [map_zero] using hGu 0 hPzero
    obtain ⟨x, hG⟩ := continuousDual_functional_eq_eval G
    have hbound (g : StrongDual ℝ (E × F)) (hg : g ∈ StrongDual.polar ℝ C) :
        ‖g (x, 0)‖ ≤ u := by
      have hp := hGu (R g) ⟨g, hg, rfl⟩
      have hng : -g ∈ StrongDual.polar ℝ C := by
        intro z hz
        change ‖-(g z)‖ ≤ 1
        rw [norm_neg]
        exact hg z hz
      have hn := hGu (R (-g)) ⟨-g, hng, rfl⟩
      rw [hG] at hp hn
      change g (x, 0) < u at hp
      change -g (x, 0) < u at hn
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith, hp.le⟩
    have hxC : (u⁻¹ • x, (0 : F)) ∈ C := by
      rw [← bipolar_eq_of_closed_convex_symmetric hcompact.isClosed hconvex hsymm
        (interior_subset hzero)]
      intro g hg
      change ‖g (u⁻¹ • x, 0)‖ ≤ 1
      have hmap : g (u⁻¹ • x, (0 : F)) = u⁻¹ * g (x, 0) := by
        simpa only [Prod.smul_mk, smul_zero, smul_eq_mul] using g.map_smul u⁻¹ (x, (0 : F))
      rw [hmap, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hu)]
      calc
        u⁻¹ * |g (x, 0)| ≤ u⁻¹ * u :=
          mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hbound g hg)
            (inv_nonneg.mpr hu.le)
        _ = 1 := inv_mul_cancel₀ hu.ne'
    have hh : ‖f (u⁻¹ • x)‖ ≤ 1 := hf (u⁻¹ • x) hxC
    rw [hG] at huf
    have hval : 1 < f (u⁻¹ • x) := by
      rw [map_smul, smul_eq_mul]
      have hscale := mul_lt_mul_of_pos_left huf (inv_pos.mpr hu)
      rwa [inv_mul_cancel₀ hu.ne'] at hscale
    exact (not_le_of_gt hval) ((le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using hh))

end ArakelovGeometry.GeometryOfNumbers
