---
author: sync
content_type: definition
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension.measurableEquivFull
docstring: 'The finite parameter space is measurably equivalent to the full space
  of

  extending absolute values.'
file: ArakelovGeometry/AdelicCurve/Extension/Finite/Tower.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension.measurableEquivFull
type: lean
updated: '2026-10-02T11:55:12'
---
noncomputable def measurableEquivFull :
    ParameterSpaceFinExtension AS L ≃ᵐ ParameterSpaceExtension AS L where
  toFun x := {
    base := x.base
    abv := ϕ AS L x
    restrict_eq := by
      ext a
      change extendAbsoluteValue x.abv (algebraMap K L a) = AS.ϕ x.base a
      rw [IsScalarTower.algebraMap_apply K (separableClosure K L) L]
      exact (extendAbsoluteValue_coe x.abv (algebraMap K (separableClosure K L) a)).trans
        (congrArg (fun v : AbsoluteValue K ℝ ↦ v a) x.restrict_eq) }
  invFun y := ParameterSpaceExtension.restrict AS L y (separableClosure K L)
  left_inv x := by
    refine ParameterSpaceExtension.ext AS (separableClosure K L) ?_ ?_
    · rfl
    · exact restriction_extendAbsoluteValue x.abv
  right_inv y := by
    refine ParameterSpaceExtension.ext AS L ?_ ?_
    · rfl
    · exact extendAbsoluteValue_restriction L y.abv
  measurable_toFun := by
    apply Measurable.of_comap_le
    change MeasurableSpace.comap _ (_ ⊔ ⨆ a : L, _) ≤ _
    rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
    refine sup_le ?_ (iSup_le fun a ↦ ?_)
    · rw [MeasurableSpace.comap_comp]
      exact (ParameterSpaceExtension.measurable_proj AS (separableClosure K L)).comap_le
    · rw [MeasurableSpace.comap_comp]
      apply Measurable.comap_le
      change Measurable fun x : ParameterSpaceFinExtension AS L ↦ ϕ AS L x a
      simp_rw [ϕ, extendAbsoluteValue_apply]
      exact (ParameterSpaceExtension.measurable_eval AS (separableClosure K L) _).pow_const _
  measurable_invFun := ParameterSpaceExtension.measurable_restrict AS L (separableClosure K L)

end ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension


namespace ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension
open MeasureTheory
variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]