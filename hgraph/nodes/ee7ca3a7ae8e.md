---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: AbsoluteValue.existsUnique_extension_of_complete
docstring: 'An absolute value on a complete field extends uniquely to every algebraic

  field extension.'
file: ArakelovGeometry/ExternalResults/AbsoluteValueExtension.lean
generated: lean
lean_status: lean_ok
title: AbsoluteValue.existsUnique_extension_of_complete
type: lean
updated: '2026-10-02T11:55:12'
---
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