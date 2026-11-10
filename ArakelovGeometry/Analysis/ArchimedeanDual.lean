/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.LinearMapBound
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Exact extension of functionals at normalized Archimedean places

Mathlib's Hahn–Banach theorem is transported to the algebraic operator norm
used by norm families. The `IsRCLikeNormedField` hypothesis specifies the
usual real or complex absolute value; an arbitrary power normalization is
not silently identified with it.
-/

@[expose] public section

namespace ArakelovGeometry

variable {L V : Type*} [NontriviallyNormedField L] [CompleteSpace L]
  [NormedAddCommGroup V] [NormedSpace L V] [FiniteDimensional L V]

/-- The algebraic operator seminorm agrees with Mathlib's continuous operator
norm on the underlying linear map. -/
theorem linearMapOperatorSeminorm_coe_continuousLinearMap (f : V →L[L] L) :
    linearMapOperatorSeminorm f.toLinearMap = ‖f‖ := by
  apply le_antisymm
  · exact linearMapOperatorSeminorm_le _ (norm_nonneg f) f.le_opNorm
  · exact f.opNorm_le_bound (apply_nonneg _ _) (norm_linearMap_apply_le f.toLinearMap)

/-- Every algebraic functional on a subspace has a norm-preserving algebraic
extension when the scalar field has its usual real or complex norm. -/
theorem exists_archimedean_extension_norm_eq [IsRCLikeNormedField L]
    (W : Submodule L V) (f : W →ₗ[L] L) :
    ∃ g : V →ₗ[L] L, g.comp W.subtype = f ∧
      linearMapOperatorSeminorm g = linearMapOperatorSeminorm f := by
  obtain ⟨g, hg, hn⟩ := exists_extension_norm_eq W (LinearMap.toContinuousLinearMap f)
  refine ⟨g.toLinearMap, ?_, ?_⟩
  · ext w
    exact hg w
  · rw [linearMapOperatorSeminorm_coe_continuousLinearMap, hn]
    exact (linearMapOperatorSeminorm_coe_continuousLinearMap
      (LinearMap.toContinuousLinearMap f)).symm

/-- A nonzero vector has a norming algebraic functional at a normalized
Archimedean place. -/
theorem exists_archimedean_norming_functional [IsRCLikeNormedField L]
    {x : V} (hx : x ≠ 0) :
    ∃ f : V →ₗ[L] L, f x = 1 ∧ linearMapOperatorSeminorm f = ‖x‖⁻¹ := by
  obtain ⟨f, hf, hn⟩ := exists_archimedean_extension_norm_eq (Submodule.span L {x})
    (ContinuousLinearEquiv.coord L x hx).toLinearMap
  refine ⟨f, ?_, ?_⟩
  · have he := LinearMap.congr_fun hf ⟨x, Submodule.mem_span_singleton_self x⟩
    change f x = ContinuousLinearEquiv.coord L x hx ⟨x, _⟩ at he
    simpa only [ContinuousLinearEquiv.coord_self] using he
  · rw [hn, linearMapOperatorSeminorm_coe_continuousLinearMap,
      ContinuousLinearEquiv.coord_norm]

/-- Over the usual real or complex norm, testing all algebraic functionals
detects the original norm. -/
theorem norm_le_of_forall_linearMap_apply_le_archimedean [IsRCLikeNormedField L]
    {x : V} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ f : V →ₗ[L] L, ‖f x‖ ≤ linearMapOperatorSeminorm f * C) : ‖x‖ ≤ C := by
  by_cases hx : x = 0
  · simpa [hx] using hC
  obtain ⟨f, hfx, hf⟩ := exists_archimedean_norming_functional (L := L) hx
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have he : 1 ≤ ‖x‖⁻¹ * C := by simpa only [hfx, norm_one, hf] using h f
  have hmul := mul_le_mul_of_nonneg_left he hn.le
  simpa [← mul_assoc, hn.ne'] using hmul

end ArakelovGeometry
