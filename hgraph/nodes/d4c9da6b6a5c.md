---
author: sync
content_type: definition
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension.baseChangeFiber
docstring: Restrict a finite extension place along a change of its base field.
file: ArakelovGeometry/AdelicCurve/Extension/Finite/BaseChange.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension.baseChangeFiber
type: lean
updated: '2026-10-02T11:55:12'
---
noncomputable def baseChangeFiber :
    BaseFiber (AS := T) N y → BaseFiber (AS := S) E x :=
  fun w ↦ (fibreEquivAbsoluteValues S E x).symm
    ⟨((fibreEquivAbsoluteValues T N y) w).val.restriction E, by
      ext a
      change ((fibreEquivAbsoluteValues T N y) w).val (algebraMap A N a) = S.ϕ x a
      rw [IsScalarTower.algebraMap_apply A B N]
      exact (congrArg (fun v : AbsoluteValue B ℝ ↦ v (algebraMap A B a))
        ((fibreEquivAbsoluteValues T N y) w).property).trans
          (congrArg (fun v : AbsoluteValue A ℝ ↦ v a) hxy)⟩

@[simp]