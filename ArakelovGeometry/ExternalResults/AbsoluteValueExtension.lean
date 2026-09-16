/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.ExternalResults.AbsoluteValue
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Extensions of real absolute values

An absolute value on a complete field extends uniquely to every algebraic field
extension. The construction uses the spectral norm in the nonarchimedean case
and complex embeddings in the archimedean case. Uniqueness follows from bounded
comparison on finite simple subextensions. These results supply the complete-field
input to the finite local-degree decomposition in Chen–Moriwaki, §3.3. Completing
the base and passing to its algebraic closure also gives extension existence for
an arbitrary base, as used in Proposition 3.4.5.
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

/-- An absolute value on a complete field extends uniquely to every algebraic
field extension. -/
theorem existsUnique_extension_of_complete {K L : Type*} [Field K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] (v : AbsoluteValue K ℝ)
    [CompleteSpace (WithAbs v)] :
    ∃! w : AbsoluteValue L ℝ, w.restriction K = v := by
  classical
  by_cases hv : v.IsNontrivial
  · by_cases hna : IsNonarchimedean v
    · exact existsUnique_extension_of_complete_of_isNonarchimedean v hv hna
    · have hc : CauSeq.IsComplete (WithAbs v) norm := by
        refine ⟨fun f ↦ ?_⟩
        obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete f.cauchySeq
        refine ⟨x, ?_⟩
        rw [Metric.tendsto_atTop] at hx
        intro ε hε
        obtain ⟨N, hN⟩ := hx ε hε
        exact ⟨N, fun j hj ↦ by simpa [dist_eq_norm] using hN j hj⟩
      have hna' : ¬IsNonarchimedean (NormedField.toAbsoluteValue (WithAbs v)) := by
        intro h
        exact hna fun x y ↦ h (WithAbs.toAbs v x) (WithAbs.toAbs v y)
      have hemb : ∃ (σ : K →+* ℂ) (s : ℝ), s ∈ Set.Ioc 0 1 ∧
          ∀ a : K, v a = ‖σ a‖ ^ s := by
        rcases exists_ringEquiv_real_or_complex_of_complete
            (NormedField.toAbsoluteValue (WithAbs v)) hna' hc with
          ⟨σ, s, hs, hσ⟩ | ⟨σ, s, hs, hσ⟩
        · refine ⟨Complex.ofRealHom.comp (σ.toRingHom.comp (WithAbs.equiv v).symm.toRingHom),
            s, hs, fun a ↦ ?_⟩
          change v a = ‖(σ (WithAbs.toAbs v a) : ℂ)‖ ^ s
          rw [Complex.norm_real]
          exact hσ (WithAbs.toAbs v a)
        · exact ⟨σ.toRingHom.comp (WithAbs.equiv v).symm.toRingHom, s, hs,
            fun a ↦ hσ (WithAbs.toAbs v a)⟩
      obtain ⟨σ, s, hs, hσ⟩ := hemb
      let : Algebra K ℂ := σ.toAlgebra
      let i : L →ₐ[K] ℂ := IsAlgClosed.lift
      let w : AbsoluteValue L ℝ := {
        toFun x := ‖i x‖ ^ s
        map_mul' x y := by
          rw [map_mul, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
        nonneg' x := Real.rpow_nonneg (norm_nonneg _) _
        eq_zero' x := by
          rw [Real.rpow_eq_zero (norm_nonneg _) (ne_of_gt hs.1), norm_eq_zero]
          exact map_eq_zero_iff i i.injective
        add_le' x y := by
          rw [map_add]
          exact (Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) hs.1.le).trans
            (Real.rpow_add_le_add_rpow (norm_nonneg _) (norm_nonneg _) hs.1.le hs.2) }
      have hw : w.restriction K = v := by
        ext a
        change ‖i (algebraMap K L a)‖ ^ s = v a
        rw [i.commutes]
        exact (hσ a).symm
      exact ⟨w, hw, fun u hu ↦ eq_of_restriction_eq_of_complete v hv u w hu hw⟩
  · have hv' : v = AbsoluteValue.trivial := by
      simpa only [isNontrivial_iff_ne_trivial, not_not] using hv
    refine ⟨AbsoluteValue.trivial, ?_, ?_⟩
    · rw [hv']
      ext a
      by_cases ha : a = 0
      · simp [ha, restriction, pullback]
      · simp [restriction, pullback, trivial_apply, ha]
    · intro w hw
      have hw' : ¬w.IsNontrivial :=
        not_isNontrivial_of_isAlgebraic w K (by simpa only [hw] using hv)
      simpa only [isNontrivial_iff_ne_trivial, not_not] using hw'

/-- Every real absolute value extends to every algebraic field extension.
This is the absolute-value extension used in Chen–Moriwaki, Proposition 3.4.5. -/
theorem exists_extension {K L : Type*} [Field K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] (v : AbsoluteValue K ℝ) :
    ∃ w : AbsoluteValue L ℝ, w.restriction K = v := by
  let F := v.Completion
  let u : AbsoluteValue F ℝ := NormedField.toAbsoluteValue F
  let e : WithAbs u ≃ᵢ F := {
    (WithAbs.equiv u).toEquiv with
    isometry_toFun := AddMonoidHomClass.isometry_of_norm (WithAbs.equiv u)
      (fun _ ↦ rfl) }
  have : CompleteSpace (WithAbs u) := e.completeSpace
  obtain ⟨w, hw, -⟩ := existsUnique_extension_of_complete (L := AlgebraicClosure F) u
  let i : L →ₐ[K] AlgebraicClosure F := IsAlgClosed.lift
  refine ⟨w.pullback i.toRingHom, ?_⟩
  ext a
  change w (i (algebraMap K L a)) = v a
  rw [i.commutes]
  rw [IsScalarTower.algebraMap_apply K F (AlgebraicClosure F)]
  rw [show w (algebraMap F (AlgebraicClosure F) (algebraMap K F a)) =
      u (algebraMap K F a) from
    congrArg (fun z : AbsoluteValue F ℝ ↦ z (algebraMap K F a)) hw]
  exact UniformSpace.Completion.norm_coe (WithAbs.toAbs v a)

end AbsoluteValue
