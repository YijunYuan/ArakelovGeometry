---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.Algebraic.injective_fibreToInverseLimit
docstring: All finite restrictions together determine an extending absolute value.
file: ArakelovGeometry/AdelicCurve/Extension/Algebraic/InverseLimit.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.Algebraic.injective_fibreToInverseLimit
type: lean
updated: '2026-10-02T11:55:12'
---
theorem injective_fibreToInverseLimit : Function.Injective (fibreToInverseLimit (L := L) AS ω) := by
  intro x y hxy
  apply Subtype.ext
  apply ParameterSpaceExtension.ext AS L (x.property.trans y.property.symm)
  ext a
  let F := ofElement (K := K) L a
  let b : F := ⟨a, mem_ofElement L a⟩
  have hF : projFiniteFiber F ω x = projFiniteFiber F ω y :=
    congrFun (congrArg Subtype.val hxy) F
  have h := congrArg (fun z : FiniteBaseFiber L F ω ↦
    ParameterSpaceFinExtension.ϕ AS F z.val b) hF
  change ParameterSpaceFinExtension.extendAbsoluteValue
    ((x.val.abv.restriction F).restriction (separableClosure K F)) b =
      ParameterSpaceFinExtension.extendAbsoluteValue
        ((y.val.abv.restriction F).restriction (separableClosure K F)) b at h
  rw [ParameterSpaceFinExtension.extendAbsoluteValue_restriction,
    ParameterSpaceFinExtension.extendAbsoluteValue_restriction] at h
  exact h