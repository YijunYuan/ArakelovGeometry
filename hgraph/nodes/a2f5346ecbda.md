---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: NumberField.isArchimedeanPlace_iff
docstring: 'A place of a number field is archimedean iff its representative is equivalent
  to an

  infinite place.'
file: ArakelovGeometry/ExternalResults/Ostrowski.lean
generated: lean
lean_status: lean_ok
title: NumberField.isArchimedeanPlace_iff
type: lean
updated: '2026-10-02T11:55:12'
---
theorem isArchimedeanPlace_iff {K : Type*} [Field K] [NumberField K]
    (p : AbsoluteValue.Place K) :
    IsArchimedeanPlace p ↔ ∃ v : InfinitePlace K, p.out ≈ v.val := by
  constructor
  · -- forward: archimedean ⟹ an infinite place exists
    intro harch
    change ¬IsNonarchimedean (p.out : K → ℝ) at harch
    -- `p.out` is nontrivial: the trivial value is non-archimedean
    have hnt : p.out.IsNontrivial := by
      rw [isNontrivial_iff_ne_trivial]
      intro hcontra
      apply harch
      rw [hcontra]
      exact isNonarchimedean_trivial
    rcases ostrowski p.out hnt with ⟨w, hw⟩ | ⟨v, hv⟩
    · exact ⟨w, hw⟩
    · -- the finite-place case is impossible: it would make `p.out` non-archimedean
      exfalso
      apply harch
      have hvna : IsNonarchimedean (v.val : K → ℝ) := finitePlace_isNonarchimedean v
      exact (isNonarchimedean_congr (hv : p.out.IsEquiv v.val)).mpr hvna
  · -- backward: an infinite place forces archimedean by transfer
    rintro ⟨w, hw⟩
    change ¬IsNonarchimedean (p.out : K → ℝ)
    intro hna
    have hwna : IsNonarchimedean (w.val : K → ℝ) :=
      (isNonarchimedean_congr (hw : p.out.IsEquiv w.val)).mp hna
    exact infinitePlace_not_isNonarchimedean w hwna

/-! ### Countability of places -/

open Classical in