---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.Algebraic.fibreCylinderAddContent_isSigmaSubadditive
docstring: Compactness gives countable subadditivity of the cylinder content on cylinders.
file: ArakelovGeometry/AdelicCurve/Extension/Algebraic/CylinderContent.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.Algebraic.fibreCylinderAddContent_isSigmaSubadditive
type: lean
updated: '2026-10-02T11:55:12'
---
theorem fibreCylinderAddContent_isSigmaSubadditive (ω : AS.Ω) :
    (fibreCylinderAddContent AS L ω).IsSigmaSubadditive := by
  intro f hf huf
  have hc : IsCompact (⋃ i, f i) := by
    obtain ⟨F, B, hB⟩ := huf
    rw [← hB]
    exact isCompact_fibreCylinder AS L F ω B
  have ho (i : ℕ) : IsOpen (f i) := by
    obtain ⟨F, B, hB⟩ := hf i
    rw [← hB]
    exact (isClopen_fibreCylinder AS L F ω B).isOpen
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover f ho (by rfl)
  have heq : (⋃ i, f i) = ⋃ i ∈ t, f i :=
    le_antisymm ht (Set.iUnion₂_subset fun i _ ↦ Set.subset_iUnion f i)
  calc
    (fibreCylinderAddContent AS L ω) (⋃ i, f i) =
        (fibreCylinderAddContent AS L ω) (⋃ i ∈ t, f i) := congrArg _ heq
    _ ≤ ∑ i ∈ t, (fibreCylinderAddContent AS L ω) (f i) :=
      addContent_biUnion_le (isSetAlgebra_fibreCylinders AS L ω).isSetRing (fun i _ ↦ hf i)
    _ ≤ ∑' i, (fibreCylinderAddContent AS L ω) (f i) := ENNReal.sum_le_tsum t