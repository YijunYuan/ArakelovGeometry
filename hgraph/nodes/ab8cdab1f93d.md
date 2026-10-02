---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.Algebraic.fibreLIntegral_tower
docstring: Nonnegative measurable fibre integration is transitive in every algebraic
  tower.
file: ArakelovGeometry/AdelicCurve/Extension/Algebraic/Tower.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.Algebraic.fibreLIntegral_tower
type: lean
updated: '2026-10-02T11:55:12'
---
theorem fibreLIntegral_tower
    {g : ((AS.algebraicExtension F).algebraicExtension L).Ω → ℝ≥0∞}
    (hg : Measurable g) :
    fibreLIntegral AS F (fibreLIntegral (AS.algebraicExtension F) L g) =
      fibreLIntegral AS L (fun y ↦ g ((towerMeasurableEquiv AS F).symm y)) := by
  funext ω
  let f : (AS.algebraicExtension L).Ω → ℝ≥0∞ :=
    fun y ↦ g ((towerMeasurableEquiv AS F).symm y)
  have hf : Measurable f := hg.comp (towerMeasurableEquiv AS F).symm.measurable
  have hi := lintegral_towerFibreMeasure AS F hf ω
  rw [towerFibreMeasure_eq AS F ω, lintegral_fibreMeasure AS L hf] at hi
  have hcomp : (fun z : ((AS.algebraicExtension F).algebraicExtension L).Ω ↦
      f (towerMeasurableEquiv AS F z)) = g := by
    funext z
    exact congrArg g ((towerMeasurableEquiv AS F).symm_apply_apply z)
  have hh := congrArg
    (fun h : ((AS.algebraicExtension F).algebraicExtension L).Ω → ℝ≥0∞ ↦
      fibreLIntegral AS F (fibreLIntegral (AS.algebraicExtension F) L h) ω) hcomp
  exact hh.symm.trans hi.symm