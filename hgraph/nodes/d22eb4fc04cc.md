---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: NumberField.infinitePlace_not_isNonarchimedean
docstring: 'The underlying absolute value of an infinite place is *not* non-archimedean

  (witness: it sends `2` to `2 > 1`).'
file: ArakelovGeometry/ExternalResults/Ostrowski.lean
generated: lean
lean_status: lean_ok
title: NumberField.infinitePlace_not_isNonarchimedean
type: lean
updated: '2026-10-02T11:55:12'
---
theorem infinitePlace_not_isNonarchimedean {K : Type*} [Field K] [NumberField K]
    (w : InfinitePlace K) : ¬IsNonarchimedean (w.val : K → ℝ) := by
  intro h
  have h2 : (w.val : K → ℝ) ((2 : ℕ) : K) ≤ 1 := h.apply_natCast_le_one
  have key : (w.val : K → ℝ) ((2 : ℕ) : K) = 2 := by
    rw [← InfinitePlace.coe_apply, ← InfinitePlace.norm_embedding_eq, map_natCast]
    simp
  rw [key] at h2
  norm_num at h2

open Classical in