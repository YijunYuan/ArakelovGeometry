/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Examples.NumberFields
public import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.ExtensionMeasure
public import Mathlib.RingTheory.Flat.TorsionFree
import ArakelovGeometry.AdelicCurve.Extension.Separable.Construction
import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.InfinitePlaceLocalDegree

/-!
# The actual completion-degree weighted normalized number-field curve

Transport the degree-scaled rational extension measure along the produced
measurable bijection. Properness is proved before any ramification formula.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace ArakelovGeometry.AdelicStructure

open NormalizedNumberFieldPlaces

variable {K : Type*} [Field K] [NumberField K]

/-- The unique actual normalized value in a nontrivial number-field place class. -/
def normalizedPlaceValue
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) :
    AbsoluteValue K ℝ := (parameterMeasurableEquivNontrivialPlace.symm ω).abv

/-- The produced normalized value belongs to the original actual place class. -/
theorem normalizedPlaceValue_class
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) :
    (Quotient.mk' (normalizedPlaceValue ω) : AbsoluteValue.Place K) = ω.val :=
  congrArg Subtype.val (parameterMeasurableEquivNontrivialPlace.apply_symm_apply ω)

/-- The source rational restriction is a produced equality, not an assumed normalization. -/
theorem normalizedPlaceValue_restriction_rat
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) :
    (normalizedPlaceValue ω).under ℚ =
      rationalAdelicStructure.ϕ (parameterMeasurableEquivNontrivialPlace.symm ω).base :=
  (parameterMeasurableEquivNontrivialPlace.symm ω).restrict_eq

/-- The actual normalized curve on all nontrivial place classes with completed-degree masses. -/
def normalizedNumberFieldAdelicStructure (K : Type*) [Field K] [NumberField K] :
    AdelicStructure K where
  Ω := {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}
  A := inferInstance
  v := Measure.map parameterMeasurableEquivNontrivialPlace normalizedExtensionMeasure
  ϕ := normalizedPlaceValue
  measurable_log _ _ := Measurable.of_discrete
  integrable_log a ha := by
    apply (integrable_map_equiv parameterMeasurableEquivNontrivialPlace _).mpr
    have hi := (ParameterSpaceExtension.integrable_log_inducedMeasure
      rationalAdelicStructure K a ha).smul_measure
      (c := (Module.finrank ℚ K : ENNReal)) (by simp)
    simpa only [normalizedPlaceValue, Function.comp_def,
      MeasurableEquiv.symm_apply_apply, normalizedExtensionMeasure,
      ParameterSpaceExtension.ϕ] using hi

/-- The normalized nontrivial place space of a number field is countable. -/
instance normalizedNumberFieldAdelicStructure_countable :
    Countable (normalizedNumberFieldAdelicStructure K).Ω :=
  inferInstanceAs (Countable {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})

/-- The normalized number-field curve carries the discrete measurable structure. -/
instance normalizedNumberFieldAdelicStructure_discreteMeasurableSpace :
    DiscreteMeasurableSpace (normalizedNumberFieldAdelicStructure K).Ω :=
  inferInstanceAs
    (DiscreteMeasurableSpace {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})

/-- Actual class singletons have the actual completion dimension as their measure. -/
theorem normalizedNumberFieldAdelicStructure_v_singleton
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) :
    (normalizedNumberFieldAdelicStructure K).v {ω} =
      ((normalizedPlaceValue ω).localDegree ℚ : ENNReal) := by
  change (Measure.map parameterMeasurableEquivNontrivialPlace
    normalizedExtensionMeasure) {ω} = _
  rw [Measure.map_apply parameterMeasurableEquivNontrivialPlace.measurable
    (measurableSet_singleton _)]
  have hp : parameterMeasurableEquivNontrivialPlace ⁻¹' {ω} =
      {parameterMeasurableEquivNontrivialPlace.symm ω} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact parameterMeasurableEquivNontrivialPlace.toEquiv.eq_symm_apply.symm
  rw [hp, normalizedExtensionMeasure_singleton]
  rfl

/-- The normalized actual class curve satisfies the product formula independently of ef. -/
instance normalizedNumberFieldAdelicStructure_isProper :
    (normalizedNumberFieldAdelicStructure K).IsProper := by
  constructor
  intro a ha
  change (∫ ω, Real.log (normalizedPlaceValue ω a)
    ∂Measure.map parameterMeasurableEquivNontrivialPlace normalizedExtensionMeasure) = 0
  rw [parameterMeasurableEquivNontrivialPlace.measurableEmbedding.integral_map]
  have he : (fun x : ParameterSpaceExtension rationalAdelicStructure K =>
      Real.log (normalizedPlaceValue (parameterMeasurableEquivNontrivialPlace x) a)) =
      (fun x => Real.log (x.abv a)) := by
    funext x
    simp only [normalizedPlaceValue, MeasurableEquiv.symm_apply_apply]
  rw [he, normalizedExtensionMeasure, integral_smul_measure]
  have h := ParameterSpaceExtension.isProper_finiteSeparableExtension rationalAdelicStructure K
  have hz : (∫ x : ParameterSpaceExtension rationalAdelicStructure K,
      Real.log (x.abv a) ∂ParameterSpaceExtension.inducedMeasure rationalAdelicStructure K) =
      0 := h.product_formula a ha
  rw [hz, smul_zero]

/-- At an actual infinite place the normalized value is its usual modulus. -/
theorem normalizedPlaceValue_eq_infinitePlace (w : NumberField.InfinitePlace K) :
    normalizedPlaceValue ⟨Quotient.mk' w.val, mk_infinitePlace_ne_trivialPlace w⟩ = w.val := by
  let y : ParameterSpaceExtension rationalAdelicStructure K :=
    ⟨Sum.inr (), w.val, w.restriction_rat⟩
  have hc := normalizedPlaceValue_class
    (⟨Quotient.mk' w.val, mk_infinitePlace_ne_trivialPlace w⟩ :
      {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
  exact congrArg ParameterSpaceExtension.abv (parameter_eq_of_isEquiv
    (x := parameterMeasurableEquivNontrivialPlace.symm
      ⟨Quotient.mk' w.val, mk_infinitePlace_ne_trivialPlace w⟩) (y := y)
    (Quotient.eq'.mp hc))

/-- The actual normalized infinite-place singleton measure is its real/complex multiplicity. -/
theorem normalizedNumberFieldAdelicStructure_v_infinitePlace (w : NumberField.InfinitePlace K) :
    (normalizedNumberFieldAdelicStructure K).v
      {⟨Quotient.mk' w.val, mk_infinitePlace_ne_trivialPlace w⟩} = (w.mult : ENNReal) := by
  calc
    _ = ((normalizedPlaceValue
        ⟨Quotient.mk' w.val, mk_infinitePlace_ne_trivialPlace w⟩).localDegree ℚ : ENNReal) :=
      normalizedNumberFieldAdelicStructure_v_singleton _
    _ = (w.val.localDegree ℚ : ENNReal) :=
      congrArg (fun v : AbsoluteValue K ℝ => (v.localDegree ℚ : ENNReal))
        (normalizedPlaceValue_eq_infinitePlace w)
    _ = _ := congrArg (fun n : ℕ => (n : ENNReal)) w.localDegree_rat

/-- Exact rational restriction gives the source value of the rational prime itself. -/
theorem normalizedPlaceValue_apply_base_prime
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) (p : Nat.Primes)
    (hp : (parameterMeasurableEquivNontrivialPlace.symm ω).base = Sum.inl p) :
    normalizedPlaceValue ω (p.val : K) = (p.val : ℝ)⁻¹ := by
  have h := congrArg (fun v : AbsoluteValue ℚ ℝ => v (p.val : ℚ))
    (normalizedPlaceValue_restriction_rat ω)
  rw [hp, rationalAdelicStructure_prime_apply_prime] at h
  change normalizedPlaceValue ω (algebraMap ℚ K (p.val : ℚ)) = (p.val : ℝ)⁻¹ at h
  simpa using h

end ArakelovGeometry.AdelicStructure
