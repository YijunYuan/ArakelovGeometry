/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Separable.Measure
public import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.ExtensionPlace
import ArakelovGeometry.AdelicCurve.Extension.Finite.Probability
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Discrete.Basic

/-!
# Actual singleton masses of normalized number-field extension parameters

The canonical rational curve's actual separable extension has point mass
`localDegree / [K : ℚ]`; its degree-scaled measure has mass `localDegree`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace ArakelovGeometry.AdelicStructure

namespace ParameterSpaceExtension

variable {F : Type*} [Field F] (S : AdelicStructure F) (L : Type*)
  [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
  [MeasurableSingletonClass S.Ω] [MeasurableSingletonClass (S.ParameterSpaceExtension L)]

/-- An actual finite separable extension atom is its actual completed degree weight. -/
theorem inducedMeasure_singleton_of_measurableSingleton
    (x : S.ParameterSpaceExtension L) :
    inducedMeasure S L {x} =
      (x.abv.localDegree F : ENNReal) / (Module.finrank F L : ENNReal) * S.v {x.base} := by
  classical
  rw [inducedMeasure_apply S L (measurableSet_singleton x)]
  have he : fibreLIntegral S L
      (({x} : Set (S.ParameterSpaceExtension L)).indicator fun _ => (1 : ENNReal)) =
      ({x.base} : Set S.Ω).indicator (fun _ =>
        (x.abv.localDegree F : ENNReal) / (Module.finrank F L : ENNReal)) := by
    funext ω
    change (∫⁻ y : ExtensionFiber S L ω,
      (Subtype.val ⁻¹' ({x} : Set (S.ParameterSpaceExtension L))).indicator
        (fun _ => (1 : ENNReal)) y ∂fibreProbabilityMeasure S L ω) = _
    rw [lintegral_indicator_const
      ((measurableSet_singleton x).preimage measurable_subtype_coe), one_mul]
    by_cases h : x.base = ω
    · subst ω
      have hp : Subtype.val ⁻¹' ({x} : Set (S.ParameterSpaceExtension L)) =
          ({⟨x, rfl⟩} : Set (ExtensionFiber S L x.base)) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff]
      rw [hp, fibreProbabilityMeasure_singleton]
      simp [fibreWeight, ϕ]
    · have hp : Subtype.val ⁻¹' ({x} : Set (S.ParameterSpaceExtension L)) =
          (∅ : Set (ExtensionFiber S L ω)) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false]
        intro hy
        exact h (hy ▸ y.property)
      rw [hp, measure_empty]
      simp [Set.indicator, Ne.symm h]
  rw [he, lintegral_indicator_const (measurableSet_singleton _)]

end ParameterSpaceExtension

/-- Every atom of the actual canonical rational curve has mass one. -/
theorem rationalAdelicStructure_v_singleton (ω : rationalAdelicStructure.Ω) :
    rationalAdelicStructure.v {ω} = 1 := by
  cases ω with
  | inl p => exact rationalAdelicStructure_v_prime p
  | inr u =>
    cases u
    rw [← rationalAdelicStructure_Ωinf]
    exact rationalAdelicStructure_v_Ωinf

namespace NormalizedNumberFieldPlaces

variable {K : Type*} [Field K] [NumberField K]

/-- The actual normalized extension sigma algebra is discrete. -/
instance normalizedParameterDiscrete :
    DiscreteMeasurableSpace (ParameterSpaceExtension rationalAdelicStructure K) :=
  ParameterSpaceExtension.discreteMeasurableSpace_of_finiteDimensional
    (S := rationalAdelicStructure) (L := K)

/-- The source place class space carries its actual power set sigma algebra. -/
instance nontrivialPlaceMeasurableSpace :
    MeasurableSpace {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K} := ⊤

instance nontrivialPlaceDiscrete :
    DiscreteMeasurableSpace {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K} :=
  ⟨fun _ => trivial⟩

/-- The produced parameter bijection is measurable in both directions. -/
def parameterMeasurableEquivNontrivialPlace :
    ParameterSpaceExtension rationalAdelicStructure K ≃ᵐ
      {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K} where
  toEquiv := parameterEquivNontrivialPlace
  measurable_toFun := Measurable.of_discrete
  measurable_invFun := measurable_from_top

/-- Scale the actual rational finite extension measure by the true extension degree. -/
def normalizedExtensionMeasure :
    Measure (ParameterSpaceExtension rationalAdelicStructure K) :=
  (Module.finrank ℚ K : ENNReal) • ParameterSpaceExtension.inducedMeasure rationalAdelicStructure K

/-- The scaled actual measure has precisely the actual completion-degree atoms. -/
theorem normalizedExtensionMeasure_singleton
    (x : ParameterSpaceExtension rationalAdelicStructure K) :
    normalizedExtensionMeasure {x} = (x.abv.localDegree ℚ : ENNReal) := by
  rw [normalizedExtensionMeasure, Measure.smul_apply,
    ParameterSpaceExtension.inducedMeasure_singleton_of_measurableSingleton,
    rationalAdelicStructure_v_singleton, mul_one]
  exact ENNReal.mul_div_cancel
    (by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne') (by simp)

end NormalizedNumberFieldPlaces

end ArakelovGeometry.AdelicStructure
