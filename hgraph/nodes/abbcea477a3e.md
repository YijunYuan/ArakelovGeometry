---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.Algebraic.measurable_map_fibreProbabilityMeasure
docstring: 'The fibre probabilities, pushed into the total parameter space, form a
  measurable

  family of probability measures.'
file: ArakelovGeometry/AdelicCurve/Extension/Algebraic/Measure.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.Algebraic.measurable_map_fibreProbabilityMeasure
type: lean
updated: '2026-10-02T11:55:12'
---
theorem measurable_map_fibreProbabilityMeasure :
    @Measurable AS.Ω
      (@Measure (ParameterSpaceExtension AS L) (projectiveMeasurableSpace AS L)) AS.A
      (@Measure.instMeasurableSpace (ParameterSpaceExtension AS L) (projectiveMeasurableSpace AS L))
      (fun ω ↦ @Measure.map (BaseFiber L ω) (ParameterSpaceExtension AS L)
        (fibreMeasurableSpace L ω) (projectiveMeasurableSpace AS L)
        Subtype.val (fibreProbabilityMeasure AS L ω)) := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  let μ (ω : AS.Ω) : Measure (ParameterSpaceExtension AS L) :=
    @Measure.map (BaseFiber L ω) (ParameterSpaceExtension AS L)
      (fibreMeasurableSpace L ω) (projectiveMeasurableSpace AS L)
      Subtype.val (fibreProbabilityMeasure AS L ω)
  let (ω : AS.Ω) : @IsProbabilityMeasure (BaseFiber L ω) (fibreMeasurableSpace L ω)
      (fibreProbabilityMeasure AS L ω) := fibreProbabilityMeasure_isProbability AS L ω
  let (ω : AS.Ω) : IsProbabilityMeasure (μ ω) :=
    Measure.isProbabilityMeasure_map (measurable_subtype_val_baseFiber AS L ω).aemeasurable
  let m (F : FiniteIntermediateField K L) :=
    MeasurableSpace.comap (projFinite AS F) inferInstance
  have hmono {F G : FiniteIntermediateField K L} (hFG : F.1 ≤ G.1) : m F ≤ m G := by
    intro A hA
    obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
    apply MeasurableSpace.measurableSet_comap.mpr
    refine ⟨projFiniteOfLE AS hFG ⁻¹' B,
      hB.preimage (measurable_projFiniteOfLE AS hFG), ?_⟩
    ext x
    exact (congrArg (fun z ↦ z ∈ B) (projFiniteOfLE_projFinite AS hFG x)).to_iff
  have hgen : (inferInstance : MeasurableSpace (ParameterSpaceExtension AS L)) =
      MeasurableSpace.generateFrom (⋃ F, {A | @MeasurableSet _ (m F) A}) :=
    (MeasurableSpace.generateFrom_iUnion_measurableSet m).symm
  have hpi : IsPiSystem (⋃ F, {A | @MeasurableSet _ (m F) A}) := by
    apply isPiSystem_iUnion_of_directed_le
    · intro F A hA B hB _
      exact @MeasurableSet.inter _ (m F) _ _ hA hB
    · intro F G
      refine ⟨FiniteIntermediateField.sup F G, ?_, ?_⟩
      · exact hmono (FiniteIntermediateField.left_le_sup F G)
      · exact hmono (FiniteIntermediateField.right_le_sup F G)
  change Measurable μ
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure hgen hpi
  intro A hA
  obtain ⟨F, hA⟩ := Set.mem_iUnion.mp hA
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
  have heq (ω : AS.Ω) :
      μ ω (projFinite AS F ⁻¹' B) =
        ParameterSpaceExtension.fibreLIntegral AS (separableClosure K F.1)
          (B.indicator fun _ ↦ (1 : ℝ≥0∞)) ω := by
    have hp : @Measurable (BaseFiber L ω) (FiniteBaseFiber L F ω)
        (fibreMeasurableSpace L ω) inferInstance (projFiniteFiber F ω) :=
      Measurable.of_comap_le (le_iSup
        (fun G : FiniteIntermediateField K L ↦
          MeasurableSpace.comap (projFiniteFiber G ω) inferInstance) F)
    have hmarg : Measure.map (projFinite AS F) (μ ω) =
        Measure.map Subtype.val (ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω) := by
      rw [Measure.map_map (measurable_projFinite_projective AS L F)
        (measurable_subtype_val_baseFiber AS L ω)]
      have hcomp :
          (projFinite AS F ∘ (Subtype.val : BaseFiber L ω → ParameterSpaceExtension AS L)) =
          (Subtype.val : FiniteBaseFiber L F ω → ParameterSpaceFinExtension AS F) ∘
            projFiniteFiber F ω := rfl
      rw [hcomp, ← Measure.map_map measurable_subtype_coe hp,
        map_fibreProbabilityMeasure_projFiniteFiber]
    rw [← Measure.map_apply (measurable_projFinite_projective AS L F) hB, hmarg,
      Measure.map_apply measurable_subtype_coe hB]
    symm
    change (∫⁻ x : FiniteBaseFiber L F ω, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x.val
      ∂ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω) = _
    have hind : (fun x : FiniteBaseFiber L F ω ↦ B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x.val) =
        (Subtype.val ⁻¹' B).indicator (fun _ : FiniteBaseFiber L F ω ↦ (1 : ℝ≥0∞)) := rfl
    rw [hind, lintegral_indicator_const (hB.preimage measurable_subtype_coe), one_mul]
  simp_rw [heq]
  exact ParameterSpaceExtension.measurable_fibreLIntegral AS (separableClosure K F.1)
    (measurable_const.indicator hB)