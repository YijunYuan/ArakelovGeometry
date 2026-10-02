---
author: sync
content_type: theorem
created: '2026-10-02T12:19:19'
decl: ArakelovGeometry.AdelicStructure.localHeight_algebraicExtension
file: ArakelovGeometry/AdelicCurve/Height/Extension.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.localHeight_algebraicExtension
type: lean
updated: '2026-10-02T12:19:19'
---
theorem localHeight_algebraicExtension (a : ι → K) (x : ParameterSpaceExtension AS L) :
    (AS.algebraicExtension L).localHeight (fun i ↦ algebraMap K L (a i)) x =
      AS.localHeight a x.base := by
  unfold localHeight
  apply Finset.sup'_congr _ rfl
  intro i _
  change x.abv (algebraMap K L (a i)) = AS.ϕ x.base (a i)
  exact congrArg (fun w : AbsoluteValue K ℝ ↦ w (a i)) x.restrict_eq