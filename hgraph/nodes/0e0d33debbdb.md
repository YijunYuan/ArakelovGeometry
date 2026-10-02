---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: NumberField.finite_out_ne_one
docstring: '**`lem:numberfield_finite_support`.** For `x ≠ 0`, the set of places whose
  chosen

  representative does not send `x` to `1` is finite. It is the union of the (finite)

  archimedean locus and the (finite) non-archimedean part bounded above.'
file: ArakelovGeometry/ExternalResults/Ostrowski.lean
generated: lean
lean_status: lean_ok
title: NumberField.finite_out_ne_one
type: lean
updated: '2026-10-02T11:55:12'
---
theorem finite_out_ne_one {K : Type*} [Field K] [NumberField K]
    {x : K} (hx : x ≠ 0) :
    {ω : AbsoluteValue.Place K | (Quotient.out ω : AbsoluteValue K ℝ) x ≠ 1}.Finite := by
  classical
  -- `T_x ⊆ (archimedean locus) ∪ (non-archimedean places with ω.out x ≠ 1)`
  apply Set.Finite.subset
    ((finite_isArchimedeanPlace K).union (finite_isNonarchimedean_ne_one (K := K) hx))
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  rcases isNonarchimedeanPlace_or_isArchimedeanPlace ω with hna | harch
  · exact Or.inr ⟨hna, hω⟩
  · exact Or.inl harch