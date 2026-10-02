---
author: sync
content_type: instance
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.instCoeFiniteIntermediateFieldIntermediateField
file: ArakelovGeometry/AdelicCurve/Extension/FiniteIntermediateField.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.instCoeFiniteIntermediateFieldIntermediateField
type: lean
updated: '2026-10-02T11:55:12'
---
instance instCoeFiniteIntermediateFieldIntermediateField :
    Coe (FiniteIntermediateField K L) (IntermediateField K L) := ⟨fun F ↦ F.1⟩
attribute [coe] FiniteIntermediateField.toIntermediateField