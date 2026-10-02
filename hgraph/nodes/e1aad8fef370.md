---
author: sync
content_type: theorem
created: '2026-10-02T13:11:44'
decl: ArakelovGeometry.AdelicStructure.finite_affineHeight_le_degree_le
docstring: 'Chen–Moriwaki, Claim 3.5.6: bounded height and bounded degree give finitely
  many

  algebraic elements. This holds in any algebraic extension, with arbitrary real bounds.'
file: ArakelovGeometry/AdelicCurve/Height/Northcott.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.finite_affineHeight_le_degree_le
type: lean
updated: '2026-10-02T13:11:44'
---
theorem finite_affineHeight_le_degree_le (hS : AS.HasNorthcott) (C δ : ℝ) :
    Set.Finite {a : L | (AS.algebraicExtension L).affineHeight a ≤ C ∧
      (Module.finrank K (IntermediateField.adjoin K {a}) : ℝ) ≤ δ} := by
  apply (AS.finite_affineHeight_le_minpoly_natDegree_le (L := L) hS C ⌊δ⌋₊).subset
  rintro a ⟨ha, hd⟩
  refine ⟨ha, Nat.le_floor ?_⟩
  simpa only [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral a)] using hd