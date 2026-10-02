---
author: sync
content_type: theorem
created: '2026-10-02T13:11:44'
decl: Projectivization.coordinateField_eq_adjoin
docstring: A single nonzero coordinate suffices to generate the field of coordinate
  ratios.
file: ArakelovGeometry/AdelicCurve/Height/Projective.lean
generated: lean
lean_status: lean_ok
title: Projectivization.coordinateField_eq_adjoin
type: lean
updated: '2026-10-02T13:11:44'
---
theorem coordinateField_eq_adjoin (a : ι → L) {j : ι} (hj : a j ≠ 0) :
    coordinateField K a = IntermediateField.adjoin K (Set.range fun i ↦ a i / a j) := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨⟨i, k⟩, rfl⟩
    change a i / a k ∈ IntermediateField.adjoin K (Set.range fun i ↦ a i / a j)
    rw [← div_div_div_cancel_right₀ hj (a i) (a k)]
    apply IntermediateField.div_mem
    · exact IntermediateField.subset_adjoin K _ ⟨i, rfl⟩
    · exact IntermediateField.subset_adjoin K _ ⟨k, rfl⟩
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact div_mem_coordinateField K a i j