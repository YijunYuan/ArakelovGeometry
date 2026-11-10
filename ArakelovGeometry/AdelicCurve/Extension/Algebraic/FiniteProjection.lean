/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Measure
public import ArakelovGeometry.AdelicCurve.Extension.Finite.BaseChange

/-!
# Finite projections along embeddings

The projective fibre probabilities have the expected marginals along arbitrary
embeddings of finite extensions, by factoring through their finite image.
This extends the finite-stage projections of Chen–Moriwaki, §3.4.2.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure.Algebraic
open MeasureTheory
open scoped ENNReal
variable {K E L : Type*} [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra K L] [FiniteDimensional K E]
  (AS : AdelicStructure K) (i : E →ₐ[K] L)

/-- Projection to a finite extension along a ground-field embedding. -/
noncomputable def projFiniteAlong :
    ParameterSpaceExtension AS L → ParameterSpaceFinExtension AS E :=
  fun x ↦ (ParameterSpaceFinExtension.measurableEquivFull AS E).symm {
    base := x.base
    abv := x.abv.pullback i.toRingHom
    restrict_eq := by
      ext a
      change x.abv (i (algebraMap K E a)) = AS.ϕ x.base a
      rw [i.commutes]
      exact congrArg (fun v : AbsoluteValue K ℝ ↦ v a) x.restrict_eq }

/-- Pullback along a field embedding preserves the base parameter. -/
@[simp]
theorem projFiniteAlong_base (x : ParameterSpaceExtension AS L) :
    (projFiniteAlong AS i x).base = x.base := rfl

/-- The projected absolute value is the pullback along the chosen embedding. -/
@[simp]
theorem projFiniteAlong_ϕ (x : ParameterSpaceExtension AS L) :
    ParameterSpaceFinExtension.ϕ AS E (projFiniteAlong AS i x) =
      x.abv.pullback i.toRingHom := by
  exact ParameterSpaceFinExtension.extendAbsoluteValue_restriction E
    (x.abv.pullback i.toRingHom)

/-- Finite projections along embeddings are measurable for the projective sigma algebra. -/
theorem measurable_projFiniteAlong [Algebra.IsAlgebraic K L] :
    Measurable[projectiveMeasurableSpace AS L] (projFiniteAlong AS i) := by
  rw [projectiveMeasurableSpace_eq]
  apply (ParameterSpaceFinExtension.measurableEquivFull AS E).symm.measurable.comp
  apply Measurable.of_comap_le
  change MeasurableSpace.comap _ (_ ⊔ ⨆ a : E, _) ≤ _
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
  refine sup_le ?_ (iSup_le fun a ↦ ?_)
  · rw [MeasurableSpace.comap_comp]
    exact (ParameterSpaceExtension.measurable_proj AS L).comap_le
  · rw [MeasurableSpace.comap_comp]
    exact (ParameterSpaceExtension.measurable_eval AS L (i a)).comap_le

/-- The restriction of a finite embedding projection to a base fibre. -/
noncomputable def projFiniteFiberAlong (ω : AS.Ω) :
    BaseFiber L ω → ParameterSpaceFinExtension.BaseFiber (AS := AS) E ω :=
  fun x ↦ ⟨projFiniteAlong AS i x.val, x.property⟩

/-- A projection along an embedding factors through its finite image. -/
theorem projFiniteFiberAlong_eq_homFiber (ω : AS.Ω) :
    let : FiniteDimensional K i.fieldRange := i.equivFieldRange.toLinearEquiv.finiteDimensional
    let F : FiniteIntermediateField K L :=
      ⟨i.fieldRange, i.equivFieldRange.toLinearEquiv.finiteDimensional⟩
    projFiniteFiberAlong AS i ω = ParameterSpaceFinExtension.homFiber AS
      i.equivFieldRange.toAlgHom ω ∘ projFiniteFiber F ω := by
  let : FiniteDimensional K i.fieldRange := i.equivFieldRange.toLinearEquiv.finiteDimensional
  dsimp only
  funext x
  apply (ParameterSpaceFinExtension.fibreEquivAbsoluteValues AS E ω).injective
  apply Subtype.ext
  change ParameterSpaceFinExtension.ϕ AS E (projFiniteAlong AS i x.val) =
    ParameterSpaceFinExtension.ϕ AS E
      (ParameterSpaceFinExtension.homFiber AS i.equivFieldRange.toAlgHom ω
        (projFiniteFiber ⟨i.fieldRange, inferInstance⟩ ω x)).val
  rw [projFiniteAlong_ϕ, ParameterSpaceFinExtension.homFiber_ϕ]
  have hval : ParameterSpaceFinExtension.ϕ AS i.fieldRange
      (projFinite AS ⟨i.fieldRange, i.equivFieldRange.toLinearEquiv.finiteDimensional⟩ x.val) =
      x.val.abv.restriction i.fieldRange :=
    ParameterSpaceFinExtension.extendAbsoluteValue_restriction i.fieldRange
      (x.val.abv.restriction i.fieldRange)
  change _ = (ParameterSpaceFinExtension.ϕ AS i.fieldRange
    (projFinite AS ⟨i.fieldRange, inferInstance⟩ x.val)).pullback
      i.equivFieldRange.toAlgHom.toRingHom
  rw [hval]
  rfl

variable [Algebra.IsAlgebraic K L]

omit [Algebra.IsAlgebraic K L] in
/-- Projection along an embedding is measurable on each algebraic fibre. -/
theorem measurable_projFiniteFiberAlong (ω : AS.Ω) :
    @Measurable (BaseFiber L ω) (ParameterSpaceFinExtension.BaseFiber (AS := AS) E ω)
      (fibreMeasurableSpace L ω) inferInstance (projFiniteFiberAlong AS i ω) := by
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  let : FiniteDimensional K i.fieldRange := i.equivFieldRange.toLinearEquiv.finiteDimensional
  let F : FiniteIntermediateField K L := ⟨i.fieldRange, inferInstance⟩
  let : Finite (FiniteBaseFiber L F ω) :=
    ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K F.1) ω
  rw [projFiniteFiberAlong_eq_homFiber]
  exact (measurable_of_countable _).comp (measurable_projFiniteFiber AS L ω F)

/-- Every finite embedded extension has the prescribed marginal probability. -/
theorem map_fibreProbabilityMeasure_projFiniteFiberAlong (ω : AS.Ω) :
    let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
    Measure.map (projFiniteFiberAlong AS i ω) (fibreProbabilityMeasure AS L ω) =
      ParameterSpaceFinExtension.fibreProbabilityMeasure AS E ω := by
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  let : FiniteDimensional K i.fieldRange := i.equivFieldRange.toLinearEquiv.finiteDimensional
  let F : FiniteIntermediateField K L := ⟨i.fieldRange, inferInstance⟩
  let : Finite (FiniteBaseFiber L F ω) :=
    ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K F.1) ω
  rw [projFiniteFiberAlong_eq_homFiber, ← Measure.map_map (measurable_of_countable _)
    (measurable_projFiniteFiber AS L ω F),
    map_fibreProbabilityMeasure_projFiniteFiber AS L ω F,
    ParameterSpaceFinExtension.map_fibreProbabilityMeasure_homFiber]

/-- Change of variables for arbitrary nonnegative functions on a finite target fibre. -/
theorem lintegral_projFiniteFiberAlong (ω : AS.Ω)
    (f : ParameterSpaceFinExtension.BaseFiber (AS := AS) E ω → ℝ≥0∞) :
    (∫⁻ x, f (projFiniteFiberAlong AS i ω x) ∂fibreProbabilityMeasure AS L ω) =
      ∫⁻ y, f y ∂ParameterSpaceFinExtension.fibreProbabilityMeasure AS E ω := by
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  let : Finite (ParameterSpaceFinExtension.BaseFiber (AS := AS) E ω) :=
    ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K E) ω
  rw [← lintegral_map (measurable_of_countable f) (measurable_projFiniteFiberAlong AS i ω),
    map_fibreProbabilityMeasure_projFiniteFiberAlong]

/-- Nonnegative fibre integration commutes with a finite embedding projection. -/
theorem fibreLIntegral_comp_projFiniteAlong (g : ParameterSpaceFinExtension AS E → ℝ≥0∞) :
    fibreLIntegral AS L (fun x ↦ g (projFiniteAlong AS i x)) =
      ParameterSpaceFinExtension.fibreLIntegral AS E g := by
  funext ω
  exact lintegral_projFiniteFiberAlong AS i ω (fun y ↦ g y.val)

/-- A finite embedding projection sends the algebraic extension measure to the finite one. -/
theorem map_measure_projFiniteAlong :
    let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
    Measure.map (projFiniteAlong AS i) (measure AS L) =
      ParameterSpaceFinExtension.measure AS E := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_projFiniteAlong AS i)]
  have h := lintegral_measure AS L (hf.comp (measurable_projFiniteAlong AS i))
  simp only [Function.comp_def] at h
  rw [h, fibreLIntegral_comp_projFiniteAlong]
  exact (ParameterSpaceFinExtension.lintegral_measure AS E hf).symm

end ArakelovGeometry.AdelicStructure.Algebraic
