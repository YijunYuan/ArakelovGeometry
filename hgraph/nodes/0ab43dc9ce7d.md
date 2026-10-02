---
author: sync
content_type: theorem
created: '2026-10-02T14:02:34'
decl: ArakelovGeometry.AdelicCurve.Hom.fRestriction_fieldMap
file: ArakelovGeometry/AdelicCurve/Morphism/Restriction.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicCurve.Hom.fRestriction_fieldMap
type: lean
updated: '2026-10-02T14:02:34'
---
theorem fRestriction_fieldMap (C : AdelicCurve) (F : Subfield C.K) :
    (fRestriction C F).fieldMap = F.subtype := rfl

@[simp]