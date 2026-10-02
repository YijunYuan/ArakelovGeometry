/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction

/-!
# Compatibility of algebraic extensions

Canonical identifications of places and projective fibre integration in
algebraic towers, following Chen–Moriwaki, Theorem 3.4.12.
-/

namespace ArakelovGeometry.AdelicStructure.Algebraic
open MeasureTheory
variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
/-- Finite measures on the projective parameter space are determined by all
finite-stage pushforwards. -/
theorem totalMeasure_ext
    {μ ν : @Measure (ParameterSpaceExtension AS L) (projectiveMeasurableSpace AS L)}
    [@IsFiniteMeasure (ParameterSpaceExtension AS L) (projectiveMeasurableSpace AS L) μ]
    (h : ∀ F : FiniteIntermediateField K L,
      @Measure.map _ _ (projectiveMeasurableSpace AS L) inferInstance (projFinite AS F) μ =
      @Measure.map _ _ (projectiveMeasurableSpace AS L) inferInstance (projFinite AS F) ν) :
    μ = ν := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
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
  have hcyl : ∀ A ∈ ⋃ F, {A | @MeasurableSet _ (m F) A}, μ A = ν A := by
    intro A hA
    obtain ⟨F, hA⟩ := Set.mem_iUnion.mp hA
    obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
    rw [← Measure.map_apply (measurable_projFinite_projective AS L F) hB,
      ← Measure.map_apply (measurable_projFinite_projective AS L F) hB, h F]
  exact ext_of_generate_finite _ hgen hpi hcyl
    (hcyl Set.univ (Set.mem_iUnion.mpr ⟨ofElement L 0,
      (show @MeasurableSet _ (m (ofElement L 0)) Set.univ from MeasurableSet.univ)⟩))
end ArakelovGeometry.AdelicStructure.Algebraic

namespace ArakelovGeometry.AdelicStructure.Algebraic
open MeasureTheory
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (AS : AdelicStructure K) [Algebra.IsAlgebraic K L]

/-- The iterated and direct algebraic parameter spaces have the same generated
σ-algebra under the canonical identification of places. -/
noncomputable def towerMeasurableEquiv (F : IntermediateField K L) :
    ((AS.algebraicExtension F).algebraicExtension L).Ω ≃ᵐ (AS.algebraicExtension L).Ω := by
  letI : MeasurableSpace (ParameterSpaceExtension (AS.algebraicExtension F) L) :=
    projectiveMeasurableSpace (AS.algebraicExtension F) L
  letI : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  change ParameterSpaceExtension (AS.algebraicExtension F) L ≃ᵐ ParameterSpaceExtension AS L
  exact {
    toFun x := {
      base := x.base.base
      abv := x.abv
      restrict_eq := by
        change (x.abv.restriction F).restriction K = _
        rw [x.restrict_eq]
        exact x.base.restrict_eq }
    invFun y := {
      base := ParameterSpaceExtension.restrict AS L y F
      abv := y.abv
      restrict_eq := rfl }
    left_inv x := by
      refine ParameterSpaceExtension.ext (AS.algebraicExtension F) L ?_ rfl
      exact ParameterSpaceExtension.ext AS F rfl x.restrict_eq
    right_inv y := ParameterSpaceExtension.ext AS L rfl rfl
    measurable_toFun := by
      apply Measurable.of_comap_le
      change MeasurableSpace.comap _ (projectiveMeasurableSpace AS L) ≤
        projectiveMeasurableSpace (AS.algebraicExtension F) L
      rw [projectiveMeasurableSpace_eq, projectiveMeasurableSpace_eq]
      change MeasurableSpace.comap _ (_ ⊔ ⨆ a : L, _) ≤ _
      rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
      refine sup_le ?_ (iSup_le fun a ↦ ?_)
      · rw [MeasurableSpace.comap_comp]
        exact ((measurable_proj_projective AS F).comp
          (ParameterSpaceExtension.measurable_proj (AS.algebraicExtension F) L)).comap_le
      · rw [MeasurableSpace.comap_comp]
        exact (ParameterSpaceExtension.measurable_eval (AS.algebraicExtension F) L a).comap_le
    measurable_invFun := by
      apply Measurable.of_comap_le
      change MeasurableSpace.comap _ (projectiveMeasurableSpace (AS.algebraicExtension F) L) ≤
        projectiveMeasurableSpace AS L
      rw [projectiveMeasurableSpace_eq, projectiveMeasurableSpace_eq]
      change MeasurableSpace.comap _ (_ ⊔ ⨆ a : L, _) ≤ _
      rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
      refine sup_le ?_ (iSup_le fun a ↦ ?_)
      · rw [MeasurableSpace.comap_comp]
        change MeasurableSpace.comap (fun y : ParameterSpaceExtension AS L ↦
          ParameterSpaceExtension.restrict AS L y F) (projectiveMeasurableSpace AS F) ≤ _
        rw [projectiveMeasurableSpace_eq]
        exact (ParameterSpaceExtension.measurable_restrict AS L F).comap_le
      · rw [MeasurableSpace.comap_comp]
        exact (ParameterSpaceExtension.measurable_eval AS L a).comap_le
  
  }

/-- The canonical identification commutes with the projection to the base. -/
@[simp] theorem towerMeasurableEquiv_proj (F : IntermediateField K L)
    (x : ParameterSpaceExtension (AS.algebraicExtension F) L) :
    ParameterSpaceExtension.proj (towerMeasurableEquiv AS F x) =
      ParameterSpaceExtension.proj (ParameterSpaceExtension.proj x) := rfl

/-- The canonical identification preserves the extending absolute value. -/
@[simp] theorem towerMeasurableEquiv_ϕ (F : IntermediateField K L)
    (x : ParameterSpaceExtension (AS.algebraicExtension F) L) :
    ParameterSpaceExtension.ϕ (towerMeasurableEquiv AS F x) =
      ParameterSpaceExtension.ϕ x := rfl

/-- The intermediate place of the inverse identification is restriction. -/
@[simp] theorem towerMeasurableEquiv_symm_proj (F : IntermediateField K L)
    (x : ParameterSpaceExtension AS L) :
    ParameterSpaceExtension.proj ((towerMeasurableEquiv AS F).symm x) =
      ParameterSpaceExtension.restrict AS L x F := rfl

end ArakelovGeometry.AdelicStructure.Algebraic

namespace ArakelovGeometry.AdelicStructure.Algebraic
open MeasureTheory
open scoped ENNReal
variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The fibre probability viewed as a measure on the total parameter space. -/
noncomputable def fibreMeasure (ω : AS.Ω) : Measure (AS.algebraicExtension L).Ω :=
  @Measure.map (BaseFiber L ω) (ParameterSpaceExtension AS L)
    (fibreMeasurableSpace L ω) (projectiveMeasurableSpace AS L)
    Subtype.val (fibreProbabilityMeasure AS L ω)

/-- Pushing the fibre probability into the total space preserves its mass. -/
instance isProbabilityMeasure_fibreMeasure (ω : AS.Ω) :
    IsProbabilityMeasure (fibreMeasure AS L ω) := by
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  exact @Measure.isProbabilityMeasure_map (BaseFiber L ω) (ParameterSpaceExtension AS L)
    (fibreMeasurableSpace L ω) (projectiveMeasurableSpace AS L)
    (fibreProbabilityMeasure AS L ω) _ Subtype.val
    (measurable_subtype_val_baseFiber AS L ω).aemeasurable

/-- The fibre probabilities on the total space form a measurable family. -/
theorem measurable_fibreMeasure :
    Measurable (fibreMeasure AS L) :=
  measurable_map_fibreProbabilityMeasure AS L

/-- Integration against the pushed-forward probability is fibre integration. -/
theorem lintegral_fibreMeasure {f : (AS.algebraicExtension L).Ω → ℝ≥0∞}
    (hf : Measurable f) (ω : AS.Ω) :
    ∫⁻ x, f x ∂fibreMeasure AS L ω = fibreLIntegral AS L f ω := by
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  exact lintegral_map hf (measurable_subtype_val_baseFiber AS L ω)

end ArakelovGeometry.AdelicStructure.Algebraic

namespace ArakelovGeometry.AdelicStructure.Algebraic
open MeasureTheory
open scoped ENNReal
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (AS : AdelicStructure K) [Algebra.IsAlgebraic K L]

/-- The measure obtained by integrating the upper fibre probabilities over a lower fibre. -/
noncomputable def towerFibreMeasure (F : IntermediateField K L) (ω : AS.Ω) :
    Measure (AS.algebraicExtension L).Ω :=
  (fibreMeasure AS F ω).bind (fun x ↦
    Measure.map (towerMeasurableEquiv AS F) (fibreMeasure (AS.algebraicExtension F) L x))

/-- The upper fibre probabilities, after identifying parameter spaces, depend measurably
on the intermediate parameter. -/
theorem measurable_towerFibreKernel (F : IntermediateField K L) :
    Measurable (fun x ↦ Measure.map (towerMeasurableEquiv AS F)
      (fibreMeasure (AS.algebraicExtension F) L x)) :=
  (Measure.measurable_map _ (towerMeasurableEquiv AS F).measurable).comp
    (measurable_fibreMeasure (AS.algebraicExtension F) L)

/-- Iterating probability measures along the measurable fibre family gives a probability. -/
instance isProbabilityMeasure_towerFibreMeasure (F : IntermediateField K L) (ω : AS.Ω) :
    IsProbabilityMeasure (towerFibreMeasure AS F ω) := by
  have hp (x : (AS.algebraicExtension F).Ω) :
      IsProbabilityMeasure (Measure.map (towerMeasurableEquiv AS F)
        (fibreMeasure (AS.algebraicExtension F) L x)) :=
    Measure.isProbabilityMeasure_map (towerMeasurableEquiv AS F).measurable.aemeasurable
  constructor
  rw [towerFibreMeasure, Measure.bind_apply MeasurableSet.univ
    (measurable_towerFibreKernel AS F).aemeasurable]
  simp

/-- Integration against the iterated probability is iterated nonnegative fibre integration. -/
theorem lintegral_towerFibreMeasure (F : IntermediateField K L)
    {f : (AS.algebraicExtension L).Ω → ℝ≥0∞} (hf : Measurable f) (ω : AS.Ω) :
    ∫⁻ x, f x ∂towerFibreMeasure AS F ω =
      fibreLIntegral AS F
        (fibreLIntegral (AS.algebraicExtension F) L
          (fun z ↦ f (towerMeasurableEquiv AS F z))) ω := by
  rw [towerFibreMeasure, Measure.lintegral_bind
    (measurable_towerFibreKernel AS F).aemeasurable hf.aemeasurable]
  let g : ((AS.algebraicExtension F).algebraicExtension L).Ω → ℝ≥0∞ :=
    fun z ↦ f (towerMeasurableEquiv AS F z)
  have hg : Measurable g := hf.comp (towerMeasurableEquiv AS F).measurable
  calc
    _ = ∫⁻ x, fibreLIntegral (AS.algebraicExtension F) L g x ∂fibreMeasure AS F ω := by
      apply lintegral_congr
      intro x
      have hi := lintegral_map (μ := fibreMeasure (AS.algebraicExtension F) L x)
        hf (towerMeasurableEquiv AS F).measurable
      exact hi.trans (lintegral_fibreMeasure (AS.algebraicExtension F) L hg x)
    _ = _ := lintegral_fibreMeasure AS F
      (measurable_fibreLIntegral (AS.algebraicExtension F) L hg) ω

end ArakelovGeometry.AdelicStructure.Algebraic
