---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.valuation_algebraMap_C
docstring: The valuation of a nonzero constant at any finite point is `1`.
file: ArakelovGeometry/AdelicCurve/Examples/FunctionFields.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.valuation_algebraMap_C
type: lean
updated: '2026-10-02T11:55:12'
---
theorem valuation_algebraMap_C (v : HeightOneSpectrum (Polynomial k)) {c : k} (hc : c ≠ 0) :
    v.valuation (RatFunc k) (algebraMap (Polynomial k) (RatFunc k) (Polynomial.C c)) = 1 := by
  rw [valuation_of_algebraMap, intValuation_eq_one_iff]
  intro hmem
  exact v.isPrime.ne_top
    (Ideal.eq_top_of_isUnit_mem _ hmem (Polynomial.isUnit_C.mpr hc.isUnit))

end FinitePlaces

/-! ### The place at infinity -/

section InftyPlace

variable {k : Type*} [Field k]

open Classical in