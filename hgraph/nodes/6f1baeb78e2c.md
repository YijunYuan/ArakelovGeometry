---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.fibreIntegral_log_eq_log_norm
docstring: 'Formula (3.10): the fibre integral of a logarithmic evaluation is the
  logarithm

  of its field norm divided by the extension degree.'
file: ArakelovGeometry/AdelicCurve/Extension/Separable/Construction.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.fibreIntegral_log_eq_log_norm
type: lean
updated: '2026-10-02T11:55:12'
---
theorem fibreIntegral_log_eq_log_norm (b : L) (hb : b ≠ 0) (ω : AS.Ω) :
    fibreIntegral AS L (fun x ↦ Real.log (ϕ x b)) ω =
      Real.log (AS.ϕ ω (Algebra.norm K b)) / (Module.finrank K L : ℝ) := by
  classical
  let E := {w : AbsoluteValue L ℝ // w.restriction K = AS.ϕ ω}
  let e : ExtensionFiber AS L ω ≃ E := {
    toFun x := ⟨x.val.ϕ, x.val.restrict_eq.trans (congrArg AS.ϕ x.property)⟩
    invFun w := ⟨⟨ω, w.val, w.property⟩, rfl⟩
    left_inv x := by
      apply Subtype.ext
      exact ParameterSpaceExtension.ext AS L x.property.symm rfl
    right_inv _ := rfl }
  let : Fintype E := (AbsoluteValue.finite_extensions (L := L) (AS.ϕ ω)).fintype
  let : Fintype (ExtensionFiber AS L ω) := Fintype.ofEquiv E e.symm
  rw [fibreIntegral_eq_sum]
  simp only [fibreWeight, ENNReal.toReal_div, ENNReal.toReal_natCast,
    div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  have hp : AS.ϕ ω (Algebra.norm K b) =
      ∏ x : ExtensionFiber AS L ω, x.val.ϕ b ^ x.val.ϕ.localDegree K :=
    (AbsoluteValue.apply_norm_eq_prod (AS.ϕ ω) b).trans
      (e.prod_comp (fun w ↦ w.val b ^ w.val.localDegree K)).symm
  rw [hp, Real.log_prod (fun x _ ↦ pow_ne_zero _ (x.val.ϕ.ne_zero hb))]
  simp only [Real.log_pow]