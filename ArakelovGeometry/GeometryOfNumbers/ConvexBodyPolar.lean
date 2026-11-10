/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Actual real polar bodies in the canonical continuous dual -/

noncomputable section
open Set Topology Bornology

namespace ArakelovGeometry.GeometryOfNumbers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {C : Set E}

/-- An actual bounded set has a polar containing an operator-norm neighbourhood of zero. -/
theorem polar_mem_nhds_zero (hC : IsBounded C) :
    StrongDual.polar ℝ C ∈ 𝓝 (0 : StrongDual ℝ E) := by
  obtain ⟨R, hR, hbound⟩ := hC.exists_pos_norm_le
  let δ : ℝ := (R + 1)⁻¹
  have hδ : 0 < δ := inv_pos.mpr (by linarith)
  have hδR : δ * R ≤ 1 := by
    have he : δ * (R + 1) = 1 := by
      dsimp only [δ]
      exact inv_mul_cancel₀ (by linarith)
    nlinarith
  apply Metric.mem_nhds_iff.mpr
  refine ⟨δ, hδ, ?_⟩
  intro f hf x hx
  have hfN : ‖f‖ ≤ δ := (mem_ball_zero_iff.mp hf).le
  calc
    ‖f x‖ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
    _ ≤ δ * R := mul_le_mul hfN (hbound x hx) (norm_nonneg _) hδ.le
    _ ≤ 1 := hδR

/-- The canonical evaluation bipolar of a closed symmetric convex set containing zero
is that very set in the original real normed space. -/
theorem bipolar_eq_of_closed_convex_symmetric
    (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) (hzero : (0 : E) ∈ C) :
    (topDualPairing ℝ E).polar (StrongDual.polar ℝ C) = C := by
  ext x
  constructor
  · intro hx
    by_contra hxc
    obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point hconvex hclosed hxc
    have hu : 0 < u := by simpa only [map_zero] using hfu 0 hzero
    let g : StrongDual ℝ E := u⁻¹ • f
    have hg : g ∈ StrongDual.polar ℝ C := by
      intro y hy
      change ‖u⁻¹ * f y‖ ≤ 1
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hu)]
      have hfy : |f y| ≤ u := by
        have hneg := hfu (-y) (hsymm y hy)
        rw [map_neg] at hneg
        exact abs_le.mpr ⟨by linarith, (hfu y hy).le⟩
      calc
        u⁻¹ * |f y| ≤ u⁻¹ * u := mul_le_mul_of_nonneg_left hfy (inv_nonneg.mpr hu.le)
        _ = 1 := inv_mul_cancel₀ hu.ne'
    have hxf : ‖g x‖ ≤ 1 := hx g hg
    have hval : 1 < g x := by
      change 1 < u⁻¹ * f x
      have hscale := mul_lt_mul_of_pos_left hux (inv_pos.mpr hu)
      rwa [inv_mul_cancel₀ hu.ne'] at hscale
    exact (not_le_of_gt hval) ((le_abs_self (g x)).trans (by
      simpa only [Real.norm_eq_abs] using hxf))
  · intro hx f hf
    exact hf x hx

/-- A polar of a neighbourhood of zero is compact in the actual finite-dimensional dual. -/
theorem polar_isCompact [FiniteDimensional ℝ E] (hC : C ∈ 𝓝 (0 : E)) :
    IsCompact (StrongDual.polar ℝ C) := by
  obtain ⟨R, _, hbound⟩ :=
    (NormedSpace.isBounded_polar_of_mem_nhds_zero ℝ hC).exists_pos_norm_le
  apply (isCompact_closedBall (0 : StrongDual ℝ E) R).of_isClosed_subset
    (NormedSpace.isClosed_polar ℝ C)
  intro f hf
  exact mem_closedBall_zero_iff.mpr (hbound f hf)

/-- The actual canonical polar is again a symmetric convex body, and its evaluation
bipolar returns the original body, including in dimension zero. -/
theorem polar_body_properties [FiniteDimensional ℝ E]
    (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) (hzero : (0 : E) ∈ interior C) :
    IsCompact (StrongDual.polar ℝ C) ∧
      Convex ℝ (StrongDual.polar ℝ C) ∧
        (∀ f ∈ StrongDual.polar ℝ C, -f ∈ StrongDual.polar ℝ C) ∧
          (0 : StrongDual ℝ E) ∈ interior (StrongDual.polar ℝ C) ∧
            (topDualPairing ℝ E).polar (StrongDual.polar ℝ C) = C := by
  refine ⟨polar_isCompact (mem_interior_iff_mem_nhds.mp hzero), ?_, ?_, ?_, ?_⟩
  · exact ((topDualPairing ℝ E).flip.polar_AbsConvex C).2
  · intro f hf x hx
    change ‖-(f x)‖ ≤ 1
    rw [norm_neg]
    exact hf x hx
  · exact mem_interior_iff_mem_nhds.mpr (polar_mem_nhds_zero hcompact.isBounded)
  · exact bipolar_eq_of_closed_convex_symmetric hcompact.isClosed hconvex hsymm
      (interior_subset hzero)

end ArakelovGeometry.GeometryOfNumbers
