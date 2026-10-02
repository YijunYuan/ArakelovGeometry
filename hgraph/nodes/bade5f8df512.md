---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.measurable_fibreIntegral_via_bounded_generators
docstring: Truncation removes the bound from the bounded-generator proof of fibre
  measurability.
file: ArakelovGeometry/AdelicCurve/Extension/BoundedEvaluationGenerators.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.measurable_fibreIntegral_via_bounded_generators
type: lean
updated: '2026-10-02T11:55:12'
---
theorem measurable_fibreIntegral_via_bounded_generators {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Measurable f) : Measurable (fibreIntegral AS L f) := by
  let u (n : ℕ) (x : ParameterSpaceExtension AS L) := max (-(n : ℝ)) (min n (f x))
  have hu (n : ℕ) : Measurable (fibreIntegral AS L (u n)) :=
    measurable_fibreIntegral_of_bounded AS (measurable_const.max (measurable_const.min hf))
      ⟨n, fun x ↦ abs_le.mpr ⟨le_max_left _ _, max_le (by linarith [Nat.cast_nonneg (α := ℝ) n])
        (min_le_left _ _)⟩⟩
  apply measurable_of_tendsto_metrizable hu
  apply tendsto_pi_nhds.mpr
  intro ω
  apply tendsto_fibreIntegral AS L
  intro x
  apply tendsto_const_nhds.congr'
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop |f x|)] with n hn
  have hx := abs_le.mp hn
  simp only [u, min_eq_right hx.2, max_eq_right hx.1]