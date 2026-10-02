---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.Algebraic.fibreIntegral_tower_of_measurable
docstring: Signed tower integration holds almost everywhere for measurable integrable
  functions.
file: ArakelovGeometry/AdelicCurve/Extension/Algebraic/Tower.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.Algebraic.fibreIntegral_tower_of_measurable
type: lean
updated: '2026-10-02T11:55:12'
---
theorem fibreIntegral_tower_of_measurable
    {g : ((AS.algebraicExtension F).algebraicExtension L).Ω → ℝ}
    (hg : Measurable g)
    (hi : Integrable g ((AS.algebraicExtension F).algebraicExtension L).v) :
    fibreIntegral AS F (fibreIntegral (AS.algebraicExtension F) L g) =ᵐ[AS.v]
      fibreIntegral AS L (fun y ↦ g ((towerMeasurableEquiv AS F).symm y)) := by
  let e := towerMeasurableEquiv AS F
  let f : (AS.algebraicExtension L).Ω → ℝ := fun y ↦ g (e.symm y)
  have hf : Measurable f := hg.comp e.symm.measurable
  have he : MeasurePreserving e ((AS.algebraicExtension F).algebraicExtension L).v
      (AS.algebraicExtension L).v := ⟨e.measurable, map_measure_towerMeasurableEquiv AS F⟩
  have heinv := MeasurePreserving.symm e he
  have hfi : Integrable f (AS.algebraicExtension L).v :=
    (heinv.integrable_comp hg.aestronglyMeasurable).mpr hi
  filter_upwards [integrable_fibreMeasure_ae AS L hf hfi] with ω hω
  have hQ : Integrable f (towerFibreMeasure AS F ω) := by
    rw [towerFibreMeasure_eq AS F ω]
    exact hω
  have hs := integral_towerFibreMeasure AS F hf ω hQ
  have hd := integral_fibreMeasure AS L hf ω
  have hm := congrArg (fun μ : Measure (AS.algebraicExtension L).Ω ↦ ∫ x, f x ∂μ)
    (towerFibreMeasure_eq AS F ω)
  have hcomp : (fun z : ((AS.algebraicExtension F).algebraicExtension L).Ω ↦
      f (towerMeasurableEquiv AS F z)) = g := by
    funext z
    exact congrArg g (e.symm_apply_apply z)
  have hh := congrArg
    (fun h : ((AS.algebraicExtension F).algebraicExtension L).Ω → ℝ ↦
      fibreIntegral AS F (fibreIntegral (AS.algebraicExtension F) L h) ω) hcomp
  exact hh.symm.trans (hs.symm.trans (hm.trans hd))