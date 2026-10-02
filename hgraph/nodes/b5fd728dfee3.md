---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: AbsoluteValue.natCard_extensions_pos
docstring: Every absolute value has at least one extension to a finite field extension.
file: ArakelovGeometry/ExternalResults/AbsoluteValueFinite.lean
generated: lean
lean_status: lean_ok
title: AbsoluteValue.natCard_extensions_pos
type: lean
updated: '2026-10-02T11:55:12'
---
theorem natCard_extensions_pos {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (v : AbsoluteValue K ℝ) :
    0 < Nat.card {w : AbsoluteValue L ℝ // w.restriction K = v} := by
  have : Finite {w : AbsoluteValue L ℝ // w.restriction K = v} :=
    (finite_extensions (L := L) v).to_subtype
  obtain ⟨w, hw⟩ := exists_extension (L := L) v
  have : Nonempty {w : AbsoluteValue L ℝ // w.restriction K = v} := ⟨⟨w, hw⟩⟩
  exact Nat.card_pos