---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: AbsoluteValue.not_isNontrivial_of_finite
docstring: An absolute value on a finite field extension is trivial if its restriction
  is trivial.
file: ArakelovGeometry/ExternalResults/AbsoluteValue.lean
generated: lean
lean_status: lean_ok
title: AbsoluteValue.not_isNontrivial_of_finite
type: lean
updated: '2026-10-02T11:55:12'
---
theorem not_isNontrivial_of_finite {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (L : Type*) [Field L] [Algebra L K] [FiniteDimensional L K]
    (hv : ¬(v.restriction L).IsNontrivial) : ¬v.IsNontrivial := by
  classical
  let b := Module.Free.chooseBasis L K
  have hscalar (c : L) : v (algebraMap L K c) ≤ 1 := by
    by_cases hc : c = 0
    · simp [hc]
    · exact le_of_eq (not_isNontrivial_apply hv hc)
  have hbound (y : K) : v y ≤ ∑ i, v (b i) := by
    conv_lhs => rw [← b.sum_repr y]
    refine (v.sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [Algebra.smul_def, map_mul]
    exact mul_le_of_le_one_left (v.nonneg _) (hscalar _)
  intro hn
  obtain ⟨x, hx⟩ := hn.exists_abv_gt_one
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (∑ i, v (b i)) hx
  exact (not_lt_of_ge (by simpa only [map_pow] using hbound (x ^ n))) hn