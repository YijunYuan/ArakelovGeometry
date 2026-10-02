/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Integrable
import ArakelovGeometry.AdelicCurve.Morphism.Basic

/-!
# The morphism associated with an algebraic extension

Chen–Moriwaki, Example 3.7.2 (1): the field inclusion, projection of places,
and the existing algebraic fibre-integration operator define a morphism from
the algebraic extension adelic curve to the original curve.
-/

open MeasureTheory

namespace ArakelovGeometry.AdelicStructure.Algebraic

variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The algebraic extension projection preserves the prescribed measures. -/
theorem measurePreserving_proj :
    (letI : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
    MeasurePreserving ParameterSpaceExtension.proj (measure AS L) AS.v) := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  exact ⟨measurable_proj_projective AS L, map_measure_proj AS L⟩

/-- The operator induced by algebraic fibre integration preserves total integrals. -/
theorem integral_fibreIntegralL1 (f : Lp ℝ 1 (measure AS L)) :
    ∫ ω, fibreIntegralL1ContinuousLinearMap AS L f ω ∂AS.v =
      ∫ x, f x ∂measure AS L :=
  (integral_congr_ae (coeFn_fibreIntegralL1 AS L f)).trans
    (integral_measure AS L (L1.integrable_coeFn f)).symm

/-- Algebraic fibre integration retracts pullback of `L¹` classes from the base. -/
theorem fibreIntegralL1_compMeasurePreserving (f : Lp ℝ 1 AS.v) :
    fibreIntegralL1ContinuousLinearMap AS L
      (Lp.compMeasurePreserving ParameterSpaceExtension.proj
        (measurePreserving_proj AS L) f) = f := by
  apply Lp.ext
  exact (coeFn_fibreIntegralL1 AS L _).trans
    ((fibreIntegral_congr_ae AS L
      (Lp.coeFn_compMeasurePreserving f (measurePreserving_proj AS L))).trans
      (Filter.Eventually.of_forall (congrFun (fibreIntegral_comp_proj AS L f))))

end ArakelovGeometry.AdelicStructure.Algebraic

namespace ArakelovGeometry.AdelicCurve.Hom

open AdelicStructure

variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- Chen–Moriwaki, Example 3.7.2 (1): an algebraic extension gives a morphism
back to the original adelic curve, with its prescribed fibre-integration operator. -/
noncomputable def algebraicExtension :
    Hom (AS.algebraicExtension L).toAdelicCurve AS.toAdelicCurve where
  fieldMap := algebraMap K L
  baseMap := ParameterSpaceExtension.proj
  measurePreserving := Algebraic.measurePreserving_proj AS L
  absoluteValue_comp x a :=
    congrArg (fun v : AbsoluteValue K ℝ ↦ v a) x.restrict_eq
  fibreIntegral := (Algebraic.fibreIntegralL1ContinuousLinearMap AS L).toLinearMap
  integral_fibreIntegral := Algebraic.integral_fibreIntegralL1 AS L
  fibreIntegral_pullback := Algebraic.fibreIntegralL1_compMeasurePreserving AS L

/-- The field map of the algebraic-extension morphism is the field inclusion. -/
@[simp]
theorem algebraicExtension_fieldMap :
    (algebraicExtension AS L).fieldMap = algebraMap K L := rfl

/-- The base map of the algebraic-extension morphism is the projection of places. -/
@[simp]
theorem algebraicExtension_baseMap :
    (algebraicExtension AS L).baseMap = ParameterSpaceExtension.proj := rfl

/-- Its disintegration is the established algebraic fibre-integration operator on `L¹`. -/
@[simp]
theorem algebraicExtension_fibreIntegral :
    (algebraicExtension AS L).fibreIntegral =
      (Algebraic.fibreIntegralL1ContinuousLinearMap AS L).toLinearMap := rfl

/-- The image of an `L¹` class is represented by the integral over each algebraic fibre. -/
theorem coeFn_algebraicExtension_fibreIntegral (f : Lp ℝ 1 (Algebraic.measure AS L)) :
    (algebraicExtension AS L).fibreIntegral f =ᵐ[AS.v]
      Algebraic.fibreIntegral AS L f :=
  Algebraic.coeFn_fibreIntegralL1 AS L f

/-- On every integrable function, the morphism induces precisely the source fibre integral. -/
theorem algebraicExtension_fibreIntegral_toL1 {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Integrable[Algebraic.projectiveMeasurableSpace AS L] f (Algebraic.measure AS L)) :
    (algebraicExtension AS L).fibreIntegral (hf.toL1 f) =
      (Algebraic.integrable_fibreIntegral AS L hf).toL1 (Algebraic.fibreIntegral AS L f) :=
  Algebraic.fibreIntegralL1_toL1 AS L hf

end ArakelovGeometry.AdelicCurve.Hom
