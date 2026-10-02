---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.real_log_inftyAbv_algebraMap
docstring: 'The real logarithm of the absolute value at infinity of a nonzero polynomial
  is its

  degree.'
file: ArakelovGeometry/AdelicCurve/Examples/FunctionFields.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.real_log_inftyAbv_algebraMap
type: lean
updated: '2026-10-02T11:55:12'
---
theorem real_log_inftyAbv_algebraMap {p : Polynomial k} (hp : p ≠ 0) :
    Real.log (inftyAbv k (algebraMap (Polynomial k) (RatFunc k) p)) = p.natDegree := by
  classical
  have hne : RatFunc.inftyValuation k (algebraMap (Polynomial k) (RatFunc k) p) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact RatFunc.algebraMap_ne_zero hp
  rw [show inftyAbv k (algebraMap (Polynomial k) (RatFunc k) p)
      = (inftyAbvDef (algebraMap (Polynomial k) (RatFunc k) p) : ℝ) from rfl, inftyAbvDef,
    real_log_toNNReal_expBase hne, RatFunc.inftyValuation_apply,
    RatFunc.inftyValuation.polynomial k hp, log_exp, Int.cast_natCast]

end InftyPlace

/-! ### Closed points of `ℙ¹` and the product formula -/

section Points

variable {k : Type*} [Field k]