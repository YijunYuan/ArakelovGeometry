---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.fibreIntegral_comp_restrict
docstring: 'Chen--Moriwaki, Proposition 3.3.2, formula (3.4): fibre integration is
  compatible with

  successive finite separable extensions `K ⊆ F ⊆ L`: integrating a function pulled
  back from

  the intermediate stage agrees with integrating the function at the intermediate
  stage.'
file: ArakelovGeometry/AdelicCurve/Extension/Separable/FibreIntegral.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.fibreIntegral_comp_restrict
type: lean
updated: '2026-10-02T11:55:12'
---
theorem fibreIntegral_comp_restrict (F : IntermediateField K L)
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (f : ParameterSpaceExtension AS F → ℝ) :
    fibreIntegral AS L (fun x ↦ f (restrict AS L x F)) = fibreIntegral AS F f := by
  classical
  funext ω
  let E := {w : AbsoluteValue L ℝ // w.restriction K = AS.ϕ ω}
  let D := {w : AbsoluteValue F ℝ // w.restriction K = AS.ϕ ω}
  let : Fintype E := (AbsoluteValue.finite_extensions (L := L) (AS.ϕ ω)).fintype
  let : Fintype D := (AbsoluteValue.finite_extensions (L := F) (AS.ϕ ω)).fintype
  let eL : ExtensionFiber AS L ω ≃ E := {
    toFun x := ⟨x.val.ϕ, x.val.restrict_eq.trans (congrArg AS.ϕ x.property)⟩
    invFun w := ⟨⟨ω, w.val, w.property⟩, rfl⟩
    left_inv x := by
      apply Subtype.ext
      exact ParameterSpaceExtension.ext AS L x.property.symm rfl
    right_inv _ := rfl }
  let eF : ExtensionFiber AS F ω ≃ D := {
    toFun x := ⟨x.val.ϕ, x.val.restrict_eq.trans (congrArg AS.ϕ x.property)⟩
    invFun w := ⟨⟨ω, w.val, w.property⟩, rfl⟩
    left_inv x := by
      apply Subtype.ext
      exact ParameterSpaceExtension.ext AS F x.property.symm rfl
    right_inv _ := rfl }
  let : Fintype (ExtensionFiber AS L ω) := Fintype.ofEquiv E eL.symm
  let : Fintype (ExtensionFiber AS F ω) := Fintype.ofEquiv D eF.symm
  let φ (w : D) : ℝ := f ⟨ω, w.val, w.property⟩
  have hs := AbsoluteValue.sum_localDegree_nsmul_restriction F (AS.ϕ ω) φ
  simp only [nsmul_eq_mul] at hs
  have hl :
      ∑ x : ExtensionFiber AS L ω, (x.val.ϕ.localDegree K : ℝ) * f (restrict AS L x.val F) =
        ∑ w : E, (w.val.localDegree K : ℝ) * φ ⟨w.val.restriction F, w.property⟩ := by
    rw [← eL.sum_comp (fun w ↦ (w.val.localDegree K : ℝ) *
      φ ⟨w.val.restriction F, w.property⟩)]
    apply Finset.sum_congr rfl
    intro x _
    apply congrArg ((x.val.ϕ.localDegree K : ℝ) * ·)
    apply congrArg f
    exact ParameterSpaceExtension.ext AS F x.property rfl
  have hr :
      ∑ x : ExtensionFiber AS F ω, (x.val.ϕ.localDegree K : ℝ) * f x.val =
        ∑ w : D, (w.val.localDegree K : ℝ) * φ w := by
    rw [← eF.sum_comp (fun w ↦ (w.val.localDegree K : ℝ) * φ w)]
    apply Finset.sum_congr rfl
    intro x _
    apply congrArg ((x.val.ϕ.localDegree K : ℝ) * ·)
    apply congrArg f
    exact ParameterSpaceExtension.ext AS F x.property rfl
  rw [fibreIntegral_eq_sum, fibreIntegral_eq_sum]
  simp only [fibreWeight, ENNReal.toReal_div, ENNReal.toReal_natCast,
    div_mul_eq_mul_div, ← Finset.sum_div]
  rw [hl, hr, hs]
  have hd : (Module.finrank K L : ℝ) =
      (Module.finrank K F : ℝ) * (Module.finrank F L : ℝ) := by
    exact_mod_cast (Module.finrank_mul_finrank K F L).symm
  rw [hd]
  have hn : (Module.finrank F L : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := F) (M := L)).ne'
  rw [mul_comm (Module.finrank K F : ℝ), mul_div_mul_left _ _ hn]