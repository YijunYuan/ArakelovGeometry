/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Probability
import ArakelovGeometry.AdelicCurve.Extension.Separable.Measurability
import Mathlib.CategoryTheory.Category.Init

/-!
# Fibre integration and the algebraic extension measure

Measurability of the fibre integration operators and construction of the
projective-limit measure in Chen–Moriwaki, Proposition 3.4.8.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure.Algebraic

open MeasureTheory AbsoluteValue
open scoped ENNReal

universe u v w

variable {K : Type u} [Field K] (AS : AdelicStructure.{u, v} K)
variable (L : Type w) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The fibre integral `I_{L/K}` for nonnegative functions, defined using the projective-limit
probability measures `P_{L,ω}`. -/
noncomputable def fibreLIntegral
    (f : ParameterSpaceExtension AS L → ℝ≥0∞) : AS.Ω → ℝ≥0∞ :=
  fun ω ↦
    ∫⁻ x : BaseFiber L ω, f x.1
      ∂fibreProbabilityMeasure AS L ω

/-- The fibre integration operator `I_{L/K}` on real-valued functions, defined using the
projective-limit fibre probability measures (Remark 3.4.7 and the discussion after
Proposition 3.4.8). -/
noncomputable def fibreIntegral (f : ParameterSpaceExtension AS L → ℝ) : AS.Ω → ℝ :=
  fun ω ↦
    ∫ x : BaseFiber L ω, f x.1
      ∂fibreProbabilityMeasure AS L ω

/-- Remark 3.4.7: fibre integration retracts the pullback along the base projection:
`I_{L/K}(g ∘ π_{L/K}) = g`. -/
theorem fibreIntegral_comp_proj (g : AS.Ω → ℝ) :
    fibreIntegral AS L (fun x ↦ g (ParameterSpaceExtension.proj x)) = g := by
  funext ω
  calc
    _ = ∫ _ : BaseFiber L ω, g ω ∂fibreProbabilityMeasure AS L ω :=
      integral_congr_ae (Filter.Eventually.of_forall fun x ↦ congrArg g x.property)
    _ = g ω := by simp

/-- Formula (3.19): on a function pulled back from a finite stage, the fibre integration
operator computes the finite-stage fibre integral: `I_{L/K}(g ∘ π_{L/K''}) = I_{K''/K}(g)`. -/
theorem fibreIntegral_comp_projFinite (F : FiniteIntermediateField K L)
    (g : ParameterSpaceFinExtension AS F → ℝ) :
    fibreIntegral AS L (fun x ↦ g (projFinite AS F x)) =
      ParameterSpaceFinExtension.fibreIntegral AS F g := by
  funext ω
  exact integral_fibreProbabilityMeasure_descend AS L
    ⟨F, fun y ↦ g y.val, rfl⟩

/-- Nonnegative pullbacks from the base are constant on probability fibres. -/
theorem fibreLIntegral_comp_proj (g : AS.Ω → ℝ≥0∞) :
    fibreLIntegral AS L (fun x ↦ g (ParameterSpaceExtension.proj x)) = g := by
  funext ω
  calc
    _ = ∫⁻ _ : BaseFiber L ω, g ω ∂fibreProbabilityMeasure AS L ω :=
      lintegral_congr fun x ↦ congrArg g x.property
    _ = g ω := by simp

/-- Nonnegative finite-stage pullbacks integrate through the prescribed finite marginal. -/
theorem fibreLIntegral_comp_projFinite (F : FiniteIntermediateField K L)
    (g : ParameterSpaceFinExtension AS F → ℝ≥0∞) :
    fibreLIntegral AS L (fun x ↦ g (projFinite AS F x)) =
      ParameterSpaceExtension.fibreLIntegral AS (separableClosure K F.1) g := by
  funext ω
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  let := ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K F.1) ω
  have h := lintegral_map (μ := fibreProbabilityMeasure AS L ω)
    (measurable_of_countable (fun y : FiniteBaseFiber L F ω ↦ g y.val))
    (measurable_projFiniteFiber AS L ω F)
  rw [map_fibreProbabilityMeasure_projFiniteFiber AS L ω F] at h
  exact h.symm

omit [Algebra.IsAlgebraic K L] in
/-- The inclusion of a fibre into the projective parameter space is measurable. -/
theorem measurable_subtype_val_baseFiber (ω : AS.Ω) :
    @Measurable (BaseFiber L ω) (ParameterSpaceExtension AS L)
      (fibreMeasurableSpace L ω) (projectiveMeasurableSpace AS L) Subtype.val := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap _ (⨆ F : FiniteIntermediateField K L, _) ≤ _
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun F ↦ ?_
  rw [MeasurableSpace.comap_comp]
  have h := le_iSup
    (fun F : FiniteIntermediateField K L ↦
      MeasurableSpace.comap (projFiniteFiber F ω) inferInstance) F
  change MeasurableSpace.comap _ (MeasurableSpace.comap Subtype.val _) ≤ _ at h
  rw [MeasurableSpace.comap_comp] at h
  exact h

omit [Algebra.IsAlgebraic K L] in
/-- Chen--Moriwaki, Proposition 3.4.8: a projectively measurable function restricts to a
measurable function on every fibre, for any measurable codomain. -/
theorem measurable_restrict_baseFiber {Y : Type*} [MeasurableSpace Y]
    {f : ParameterSpaceExtension AS L → Y}
    (hf : Measurable[projectiveMeasurableSpace AS L] f) (ω : AS.Ω) :
    Measurable[fibreMeasurableSpace L ω] fun x : BaseFiber L ω ↦ f x.1 :=
  hf.comp (measurable_subtype_val_baseFiber AS L ω)

variable {L} in
omit [Algebra.IsAlgebraic K L] in
theorem measurable_projFiniteOfLE {F G : FiniteIntermediateField K L} (hFG : F.1 ≤ G.1) :
    Measurable (projFiniteOfLE AS hFG) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap _ (_ ⊔ ⨆ a : separableClosure K F.1, _) ≤ _
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
  refine sup_le ?_ (iSup_le fun a ↦ ?_)
  · rw [MeasurableSpace.comap_comp]
    exact (ParameterSpaceExtension.measurable_proj AS (separableClosure K G.1)).comap_le
  · rw [MeasurableSpace.comap_comp]
    exact (ParameterSpaceExtension.measurable_eval AS (separableClosure K G.1)
      (finiteSeparableInclusion hFG a)).comap_le

/-- The fibre probabilities, pushed into the total parameter space, form a measurable
family of probability measures. -/
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
  let (ω : AS.Ω) : IsProbabilityMeasure (μ ω) := inferInstance
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

/-- Proposition 3.4.8: fibre integration of a nonnegative projectively measurable function is
measurable on the base. -/
theorem measurable_fibreLIntegral {f : ParameterSpaceExtension AS L → ℝ≥0∞}
    (hf : Measurable[projectiveMeasurableSpace AS L] f) :
    Measurable (fibreLIntegral AS L f) := by
  have hm := (Measure.measurable_lintegral hf).comp
    (measurable_map_fibreProbabilityMeasure AS L)
  convert hm using 1
  funext ω
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  exact (lintegral_map hf (measurable_subtype_val_baseFiber AS L ω)).symm

/-- The measure `ν_L` on the projective-limit parameter space `Ω_L`, defined by the formula
following Proposition 3.4.8:
`ν_L(A) = ∫_{Ω_K} ∫_{M_{L,ω}} 1_A(x) dP_{L,ω} dν_K`. -/
noncomputable def measure :
    @Measure (ParameterSpaceExtension AS L) (projectiveMeasurableSpace AS L) :=
  letI : MeasurableSpace (ParameterSpaceExtension AS L) :=
    projectiveMeasurableSpace AS L
  Measure.ofMeasurable
      (fun A _hA ↦
        ∫⁻ ω, fibreLIntegral (AS := AS) (L := L)
          (Set.indicator A fun _ ↦ (1 : ℝ≥0∞)) ω ∂AS.v)
      (by simp [fibreLIntegral])
      (by
        intro A hA hdisj
        let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
        have hind (s : Set (ParameterSpaceExtension AS L)) (hs : MeasurableSet s) (ω : AS.Ω) :
            fibreLIntegral AS L (s.indicator fun _ ↦ 1) ω =
              fibreProbabilityMeasure AS L ω (Subtype.val ⁻¹' s) := by
          simp only [fibreLIntegral, ← Set.indicator_comp_right, Function.comp_def]
          rw [lintegral_indicator_const (hs.preimage (measurable_subtype_val_baseFiber AS L ω))]
          simp
        have hpoint (ω : AS.Ω) :
            fibreLIntegral AS L ((⋃ n, A n).indicator fun _ ↦ 1) ω =
              ∑' n, fibreLIntegral AS L ((A n).indicator fun _ ↦ 1) ω := by
          rw [hind _ (MeasurableSet.iUnion hA), Set.preimage_iUnion,
            measure_iUnion (fun i j hij ↦ (hdisj hij).preimage Subtype.val)
              (fun n ↦ (hA n).preimage (measurable_subtype_val_baseFiber AS L ω))]
          congr 1
          funext n
          exact (hind _ (hA n) ω).symm
        simp_rw [hpoint]
        exact lintegral_tsum (fun n ↦
          (measurable_fibreLIntegral AS L (measurable_const.indicator (hA n))).aemeasurable))

/-- The defining formula for `ν_L`. -/
theorem measure_apply {A : Set (ParameterSpaceExtension AS L)}
    (hA : @MeasurableSet (ParameterSpaceExtension AS L)
      (projectiveMeasurableSpace AS L) A) :
    measure AS L A =
      ∫⁻ ω, fibreLIntegral (AS := AS) (L := L)
        (Set.indicator A fun _ ↦ (1 : ℝ≥0∞)) ω ∂AS.v :=
  by
    let : MeasurableSpace (ParameterSpaceExtension AS L) :=
      projectiveMeasurableSpace AS L
    exact Measure.ofMeasurable_apply A hA

/-- Formula (3.18): the projective-limit measure `ν_L` integrates nonnegative projectively
measurable functions through the fibre integration operator. -/
theorem lintegral_measure {f : ParameterSpaceExtension AS L → ℝ≥0∞}
    (hf : Measurable[projectiveMeasurableSpace AS L] f) :
    ∫⁻ x, f x ∂measure AS L = ∫⁻ ω, fibreLIntegral AS L f ω ∂AS.v := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  refine Measurable.ennreal_induction
    (motive := fun f ↦ (∫⁻ x, f x ∂measure AS L) =
      ∫⁻ ω, fibreLIntegral AS L f ω ∂AS.v) ?_ ?_ ?_ hf
  · intro c s hs
    rw [lintegral_indicator_const hs, measure_apply AS L hs,
      ← lintegral_const_mul c (measurable_fibreLIntegral AS L (measurable_const.indicator hs))]
    apply lintegral_congr
    intro ω
    simp only [fibreLIntegral, ← Set.indicator_comp_right, Function.comp_def]
    rw [lintegral_indicator_const (hs.preimage (measurable_subtype_val_baseFiber AS L ω)),
      lintegral_indicator_const (hs.preimage (measurable_subtype_val_baseFiber AS L ω)), one_mul]
  · intro f g _ hf hg ihf ihg
    simp only [Pi.add_apply]
    rw [lintegral_add_left hf, ihf, ihg,
      ← lintegral_add_left (measurable_fibreLIntegral AS L hf)]
    apply lintegral_congr
    intro ω
    exact (lintegral_add_left (measurable_restrict_baseFiber AS L hf ω) _).symm
  · intro f hf hmono ih
    rw [lintegral_iSup hf hmono]
    simp_rw [ih]
    rw [← lintegral_iSup (fun n ↦ measurable_fibreLIntegral AS L (hf n))
      (fun n m h ω ↦ lintegral_mono fun x ↦ hmono h x.val)]
    apply lintegral_congr
    intro ω
    exact (lintegral_iSup (fun n ↦ measurable_restrict_baseFiber AS L (hf n) ω)
      (fun n m h x ↦ hmono h x.val)).symm

end ArakelovGeometry.AdelicStructure.Algebraic
