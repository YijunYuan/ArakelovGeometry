---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.Algebraic.isClosed_compatibleFibreFamilies
docstring: Compatibility is a closed condition in the product of finite discrete fibres.
file: ArakelovGeometry/AdelicCurve/Extension/Algebraic/InverseLimit.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.Algebraic.isClosed_compatibleFibreFamilies
type: lean
updated: '2026-10-02T11:55:12'
---
theorem isClosed_compatibleFibreFamilies : IsClosed (compatibleFibreFamilies (L := L) AS ω) := by
  unfold compatibleFibreFamilies
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro F
  apply isClosed_iInter
  intro G
  apply isClosed_iInter
  intro hFG
  let := ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K G.1) ω
  exact isClosed_eq ((continuous_of_discreteTopology :
    Continuous (projFiniteFiberOfLE hFG ω)).comp (continuous_apply G)) (continuous_apply F)