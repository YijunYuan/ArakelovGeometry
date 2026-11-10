/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.ExternalResults.Measure
public import ArakelovGeometry.NumberTheory.NormalizedNumberFieldInfiniteMass
public import ArakelovGeometry.NumberTheory.NumberFieldHermitianLatticeCovolume

/-!
# The actual Archimedean determinant integral in the covolume formula
-/

@[expose] public section

noncomputable section

open NumberField MeasureTheory
open scoped TensorProduct ENNReal

namespace ArakelovGeometry.AdelicStructure

variable {K : Type*} [Field K] [NumberField K]

/-- Every real function is integrable on the actual finite Archimedean locus. -/
theorem normalized_infinite_integrableOn
    (f : (normalizedNumberFieldAdelicStructure K).Ω → ℝ) :
    IntegrableOn f (normalizedNumberFieldAdelicStructure K).Ωinf
      (normalizedNumberFieldAdelicStructure K).v := by
  classical
  let S := normalizedNumberFieldAdelicStructure K
  let : MeasurableSingletonClass S.Ω := inferInstanceAs
    (MeasurableSingletonClass {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
  let s := Finset.univ.image (normalizedInfinitePlacePoint (K := K))
  have hs : (s : Set S.Ω) = S.Ωinf := by
    simpa only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ] using
      (normalizedNumberFieldAdelicStructure_Ωinf_eq_range (K := K)).symm
  have hsupport : Function.support (S.Ωinf.indicator f) ⊆ s := by
    intro ω hω
    exact hs.symm ▸ Set.support_indicator_subset hω
  have hmass (ω : S.Ω) (hω : ω ∈ s) : S.v {ω} ≠ ⊤ := by
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hω
    have hm : S.v {normalizedInfinitePlacePoint w} = (w.mult : ℝ≥0∞) :=
      normalizedNumberFieldAdelicStructure_v_infinitePlace w
    rw [hm]
    exact ENNReal.natCast_ne_top _
  exact (integrable_indicator_iff S.measurableSet_Ωinf).mp
    (integrable_of_support_subset_finset hsupport hmass)

/-- The integral on the literal infinite locus uses the actual infinite-place masses. -/
theorem normalized_infinite_integral_eq_sum
    (f : (normalizedNumberFieldAdelicStructure K).Ω → ℝ) :
    (∫ ω in (normalizedNumberFieldAdelicStructure K).Ωinf,
      f ω ∂(normalizedNumberFieldAdelicStructure K).v) =
      ∑ w : InfinitePlace K, (w.mult : ℝ) * f (normalizedInfinitePlacePoint w) := by
  classical
  let S := normalizedNumberFieldAdelicStructure K
  let : MeasurableSingletonClass S.Ω := inferInstanceAs
    (MeasurableSingletonClass {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
  let s := Finset.univ.image (normalizedInfinitePlacePoint (K := K))
  have hs : (s : Set S.Ω) = S.Ωinf := by
    simpa only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ] using
      (normalizedNumberFieldAdelicStructure_Ωinf_eq_range (K := K)).symm
  rw [← hs, setIntegral_finset s (hs.symm ▸ normalized_infinite_integrableOn f),
    Finset.sum_image (fun _ _ _ _ h => normalizedInfinitePlacePoint_injective h)]
  apply Finset.sum_congr rfl
  intro w _
  have hm : S.v {normalizedInfinitePlacePoint w} = (w.mult : ℝ≥0∞) :=
    normalizedNumberFieldAdelicStructure_v_infinitePlace w
  rw [Measure.real, hm, ENNReal.toReal_natCast, smul_eq_mul]

end ArakelovGeometry.AdelicStructure


namespace ArakelovGeometry.NumberFieldHermitianLatticeCovolume

open AdelicStructure NumberFieldHermitianBasisCovolume NumberFieldArchimedeanCovolume

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E]
  [Module K E] [FiniteDimensional K E]

/-- The actual Archimedean part of the determinant logarithmic norm is the metric Jacobian. -/
theorem log_basisDeterminantFactor_eq_integral
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (b : Module.Basis (Fin (Module.finrank K E)) K E) :
    Real.log (basisDeterminantFactor ξ b) =
      ∫ ω in (normalizedNumberFieldAdelicStructure K).Ωinf,
        ξ.determinant.logNorm (exteriorPower.ιMulti K _ b) ω
          ∂(normalizedNumberFieldAdelicStructure K).v := by
  rw [log_basisDeterminantFactor ξ hξ b, normalized_infinite_integral_eq_sum]
  rfl

/-- The actual covolume logarithm expressed using the original determinant norm integral. -/
theorem log_euclideanCovolume_eq_integral
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (b : Module.Basis (Fin (Module.finrank K E)) K E)
    (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) (hbM : principalModule b ≤ M) :
    Real.log (euclideanCovolume ξ hξ M) =
      (∫ ω in (normalizedNumberFieldAdelicStructure K).Ωinf,
        ξ.determinant.logNorm (exteriorPower.ιMulti K _ b) ω
          ∂(normalizedNumberFieldAdelicStructure K).v) +
      (Module.finrank K E : ℝ) * Real.log
        ((2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
          Real.sqrt |(NumberField.discr K : ℝ)|) -
      Real.log ((principalModule b).toAddSubgroup.relIndex M.toAddSubgroup : ℝ) := by
  rw [log_euclideanCovolume ξ hξ b M hfg hspan hbM,
    ← log_basisDeterminantFactor_eq_integral ξ hξ b, log_basisDeterminantFactor ξ hξ b]

end ArakelovGeometry.NumberFieldHermitianLatticeCovolume
