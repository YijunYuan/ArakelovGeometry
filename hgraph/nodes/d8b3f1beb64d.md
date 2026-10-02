---
author: sync
content_type: definition
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.proj
docstring: The projection `Ω_L → Ω_K`.
file: ArakelovGeometry/AdelicCurve/Extension/ParameterSpace.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.proj
type: lean
updated: '2026-10-02T11:55:12'
---
def proj {AS : AdelicStructure.{u, v} K} {L : Type w} [Field L] [Algebra K L]
    (x : ParameterSpaceExtension AS L) : AS.Ω :=
  x.base