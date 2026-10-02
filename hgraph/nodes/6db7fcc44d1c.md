---
author: sync
content_type: instance
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.Algebraic.instCompactSpaceBaseFiber
docstring: Algebraic fibres are compact in the evaluation topology.
file: ArakelovGeometry/AdelicCurve/Extension/Algebraic/Basic.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.Algebraic.instCompactSpaceBaseFiber
type: lean
updated: '2026-10-02T11:55:12'
---
instance instCompactSpaceBaseFiber (ω : AS.Ω) :
    CompactSpace (BaseFiber L ω) := by
  constructor
  apply (isEmbedding_fibreEval AS L ω).isCompact_iff.mpr
  rw [Set.image_univ]
  have hr : Set.range (fun x : BaseFiber L ω ↦ (x.val.abv : L → ℝ)) =
      Set.range (fun w : {w : AbsoluteValue L ℝ // w.restriction K = AS.ϕ ω} ↦
        (w.val : L → ℝ)) := by
    ext f
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x.val.abv, x.val.restrict_eq.trans (congrArg AS.ϕ x.property)⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨⟨⟨ω, w.val, w.property⟩, rfl⟩, rfl⟩
  rw [hr]
  exact AbsoluteValue.isCompact_range_extensions (AS.ϕ ω)

variable {AS L} in