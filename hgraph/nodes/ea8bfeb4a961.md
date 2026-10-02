---
author: sync
content_type: theorem
created: '2026-10-02T12:40:52'
decl: ArakelovGeometry.AdelicStructure.polynomialHeight_X_sub_C_mul_le
docstring: Multiplication by a linear factor costs at most `log 2` times the integrated
  exponent.
file: ArakelovGeometry/AdelicCurve/Height/Polynomial.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.polynomialHeight_X_sub_C_mul_le
type: lean
updated: '2026-10-02T12:40:52'
---
theorem polynomialHeight_X_sub_C_mul_le (a : K) {p : K[X]} (hp : p ≠ 0) :
    AS.polynomialHeight ((X - C a) * p) ≤ AS.affineHeight a + AS.polynomialHeight p +
      Real.log 2 * AS.heightArchimedeanConstant := by
  have h := AS.polynomialHeight_mul_le (X_sub_C_ne_zero a) hp
  rw [AS.polynomialHeight_X_sub_C, natDegree_X_sub_C] at h
  apply h.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ AS.heightArchimedeanConstant_nonneg
  apply Real.log_le_log
  · exact Nat.cast_pos.mpr (by omega)
  · exact_mod_cast min_le_left (1 + 1) (p.natDegree + 1)