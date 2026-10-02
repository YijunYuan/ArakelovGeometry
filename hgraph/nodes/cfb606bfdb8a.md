---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.Algebraic.isEmbedding_fibreEval
docstring: Absolute values on a fixed fibre are determined by all their evaluations.
file: ArakelovGeometry/AdelicCurve/Extension/Algebraic/Basic.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.Algebraic.isEmbedding_fibreEval
type: lean
updated: '2026-10-02T11:55:12'
---
theorem isEmbedding_fibreEval (ω : AS.Ω) :
    Topology.IsEmbedding (fun x : BaseFiber L ω ↦ (x.val.abv : L → ℝ)) := by
  refine ⟨⟨rfl⟩, ?_⟩
  intro x y hxy
  apply Subtype.ext
  exact ParameterSpaceExtension.ext AS L (x.property.trans y.property.symm)
    (DFunLike.coe_injective hxy)

omit [Algebra.IsAlgebraic K L] in