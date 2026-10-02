---
author: sync
content_type: theorem
created: '2026-10-02T14:15:48'
decl: ArakelovGeometry.AdelicCurve.RationalFunction.horizontalAbv_apply
docstring: Away from zero the horizontal absolute value has the source valuation formula.
file: ArakelovGeometry/AdelicCurve/Examples/RationalFunction/FinitePlaces.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicCurve.RationalFunction.horizontalAbv_apply
type: lean
updated: '2026-10-02T14:15:48'
---
theorem horizontalAbv_apply (v : HorizontalPlace) {f : RatFunc ℚ} (hf : f ≠ 0) :
    horizontalAbv v f =
      (horizontalHeight v : ℝ) ^ WithZero.log (v.valuation (RatFunc ℚ) f) := by
  classical
  unfold horizontalAbv
  split_ifs with h
  · change (WithZeroMulInt.toNNReal (ne_zero_of_lt h)
      (v.valuation (RatFunc ℚ) f) : ℝ) = _
    rw [WithZeroMulInt.toNNReal_neg_apply _ ((Valuation.ne_zero_iff _).mpr hf),
      NNReal.coe_zpow, WithZero.toAdd_unzero_eq_log]
  · have hv : horizontalHeight v = 1 := le_antisymm (not_lt.mp h) (one_le_horizontalHeight v)
    simp [AbsoluteValue.trivial_apply hf, hv]