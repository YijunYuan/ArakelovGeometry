---
author: sync
content_type: theorem
created: '2026-10-02T12:19:19'
decl: ArakelovGeometry.AdelicStructure.logHeight_comp_aut
docstring: 'Chen–Moriwaki, Lemma 3.5.4, in the stronger form for any finite extension:

  conjugate tuples have the same height in an algebraic extension containing them.'
file: ArakelovGeometry/AdelicCurve/Height/Extension.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.logHeight_comp_aut
type: lean
updated: '2026-10-02T12:19:19'
---
theorem logHeight_comp_aut (i : E →ₐ[K] L) (σ : E ≃ₐ[K] E) (a : ι → E) :
    (AS.algebraicExtension L).logHeight (fun j ↦ i (σ (a j))) =
      (AS.algebraicExtension L).logHeight (fun j ↦ i (a j)) := by
  exact (AS.logHeight_comp_finiteEmbedding (i.comp σ.toAlgHom) a).trans
    (AS.logHeight_comp_finiteEmbedding i a).symm