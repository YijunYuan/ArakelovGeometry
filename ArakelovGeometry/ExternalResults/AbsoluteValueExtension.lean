/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.ExternalResults.AbsoluteValue
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# Extensions of complete nonarchimedean absolute values

A nontrivial nonarchimedean absolute value on a complete field extends uniquely
to every algebraic field extension. The construction is the spectral norm.
This supplies the nonarchimedean complete-field input to the finite local-degree
decomposition in Chen–Moriwaki, §3.3.
-/

namespace AbsoluteValue

private theorem extension_le_of_finite {K L : Type*} [NontriviallyNormedField K]
    [CompleteSpace K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (u w : AbsoluteValue L ℝ)
    (hu : ∀ a : K, u (algebraMap K L a) = ‖a‖)
    (hw : ∀ a : K, w (algebraMap K L a) = ‖a‖) (x : L) : u x ≤ w x := by
  let : NormedSpace K (WithAbs u) := {
    norm_smul_le a y := by
      change u (a • y.ofAbs) ≤ ‖a‖ * u y.ofAbs
      rw [Algebra.smul_def, map_mul, hu] }
  let : NormedSpace K (WithAbs w) := {
    norm_smul_le a y := by
      change w (a • y.ofAbs) ≤ ‖a‖ * w y.ofAbs
      rw [Algebra.smul_def, map_mul, hw] }
  let f : WithAbs w →ₗ[K] WithAbs u :=
    ((WithAbs.linearEquiv K w).trans (WithAbs.linearEquiv K u).symm).toLinearMap
  let fc : WithAbs w →L[K] WithAbs u := ⟨f, f.continuous_of_finiteDimensional⟩
  let g : WithAbs w →+* WithAbs u := (WithAbs.congr w u (RingEquiv.refl L)).toRingHom
  have hg : g.IsBounded := fc.isBoundedLinearMap.bound
  exact contraction_of_isPowMul (fun y n _ ↦ norm_pow y n) hg (WithAbs.toAbs w x)

/-- Two absolute values extending the same complete nontrivial absolute value
to an algebraic field extension coincide. -/
theorem eq_of_restriction_eq_of_complete {K L : Type*} [Field K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] (v : AbsoluteValue K ℝ)
    [CompleteSpace (WithAbs v)] (hv : v.IsNontrivial) (u w : AbsoluteValue L ℝ)
    (hu : u.restriction K = v) (hw : w.restriction K = v) : u = w := by
  let : NontriviallyNormedField (WithAbs v) :=
    { (inferInstance : NormedField (WithAbs v)) with
      non_trivial := by
        obtain ⟨x, hx⟩ := hv.exists_abv_gt_one
        exact ⟨WithAbs.toAbs v x, hx⟩ }
  ext x
  let E := IntermediateField.adjoin K {x}
  let : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hu' (a : WithAbs v) :
      u.restriction E (algebraMap (WithAbs v) E a) = ‖a‖ :=
    congrArg (fun z : AbsoluteValue K ℝ ↦ z a.ofAbs) hu
  have hw' (a : WithAbs v) :
      w.restriction E (algebraMap (WithAbs v) E a) = ‖a‖ :=
    congrArg (fun z : AbsoluteValue K ℝ ↦ z a.ofAbs) hw
  let x' : E := ⟨x, IntermediateField.subset_adjoin K {x} (Set.mem_singleton x)⟩
  exact le_antisymm
    (extension_le_of_finite (u.restriction E) (w.restriction E) hu' hw' x')
    (extension_le_of_finite (w.restriction E) (u.restriction E) hw' hu' x')

/-- A complete nontrivial nonarchimedean absolute value has a unique extension to
an algebraic field extension. -/
theorem existsUnique_extension_of_complete_of_isNonarchimedean {K L : Type*}
    [Field K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] (v : AbsoluteValue K ℝ)
    [CompleteSpace (WithAbs v)] (hv : v.IsNontrivial) (hna : IsNonarchimedean v) :
    ∃! w : AbsoluteValue L ℝ, w.restriction K = v := by
  let : NontriviallyNormedField (WithAbs v) :=
    { (inferInstance : NormedField (WithAbs v)) with
      non_trivial := by
        obtain ⟨x, hx⟩ := hv.exists_abv_gt_one
        exact ⟨WithAbs.toAbs v x, hx⟩ }
  let : IsUltrametricDist (WithAbs v) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (fun x y ↦ hna x.ofAbs y.ofAbs)
  let : Algebra.IsAlgebraic (WithAbs v) L :=
    Algebra.IsAlgebraic.of_ringHom_of_comp_eq (WithAbs.equiv v).toRingHom
      (RingHom.id L) (WithAbs.equiv v).surjective Function.injective_id rfl
  let w : AbsoluteValue L ℝ := (spectralNorm.normedField (WithAbs v) L).toAbsoluteValue
  refine ⟨w, ?_, ?_⟩
  · ext x
    change spectralNorm (WithAbs v) L (algebraMap K L x) = v x
    exact spectralNorm_extends (K := WithAbs v) (L := L) (WithAbs.toAbs v x)
  · intro u hu
    ext x
    change u x = spectralNorm (WithAbs v) L x
    apply spectralNorm_unique_field_norm_ext
    intro a
    exact congrArg (fun z : AbsoluteValue K ℝ ↦ z a.ofAbs) hu

end AbsoluteValue
