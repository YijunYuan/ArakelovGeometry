---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.tsum_fibreWeight
docstring: The concrete fibre weights from (3.2) have total mass one.
file: ArakelovGeometry/AdelicCurve/Extension/Separable/FibreIntegral.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.tsum_fibreWeight
type: lean
updated: '2026-10-02T11:55:12'
---
theorem tsum_fibreWeight (ω : AS.Ω) :
    ∑' x : ExtensionFiber AS L ω, fibreWeight AS L ω x = 1 := by
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
  rw [tsum_fintype]
  change (∑ x : ExtensionFiber AS L ω,
    (x.val.ϕ.localDegree K : ℝ≥0∞) / (Module.finrank K L : ℝ≥0∞)) = 1
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum]
  have hs : ∑ x : ExtensionFiber AS L ω, x.val.ϕ.localDegree K = Module.finrank K L :=
    (e.sum_comp (fun w ↦ w.val.localDegree K)).trans (AbsoluteValue.sum_localDegree (AS.ϕ ω))
  rw [hs, ← div_eq_mul_inv]
  exact ENNReal.div_self (by exact_mod_cast (ne_of_gt (Module.finrank_pos (R := K) (M := L))))
    (by simp)