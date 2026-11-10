/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic
public import ArakelovGeometry.NumberTheory.NumberField.Model.Sections
public import ArakelovGeometry.NumberTheory.NumberField.Model.TraceDual.Basic
public import ArakelovGeometry.NumberTheory.NumberField.Model.TraceDual.Projective.Generic
public import ArakelovGeometry.NumberTheory.NumberField.RiemannRoch.ComparisonConstants
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.NumberTheory.NumberField.Model.TraceDual.Slope
import ArakelovGeometry.NumberTheory.NumberField.RiemannRoch.ArithmeticDuality
import ArakelovGeometry.NumberTheory.NumberField.RiemannRoch.PositiveTwist
import ArakelovGeometry.NumberTheory.NumberField.RiemannRoch.SectionVanishing
import ArakelovGeometry.NumberTheory.NumberField.RiemannRoch.WeakDiscriminant
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init

/-! # Actual nonnegative-slope arithmetic section comparison -/

@[expose] public section

noncomputable section
open NumberField
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldClassicalNonnegativeSlopeCount

open AdelicStructure NumberFieldProjectiveGeneric NumberFieldFullLattice
  NumberFieldCodifferentDual NumberFieldProjectiveTraceDualGeneric NumberFieldClassicalTraceDual
  NumberFieldClassicalArithmeticDuality NumberFieldClassicalComparisonConstants
  NumberFieldClassicalTraceDualMetric NumberFieldClassicalPositiveTwist
open NumberFieldInvertibleGeneric (genericImage genericImage_fullSpan)

attribute [local instance] traceTensor_finite traceTensor_projective

universe u
variable {K : Type u} [Field K] [NumberField K]
  (M : Type u) [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- The actual determinant degree minus original h0 has the exact source bound,
without a minimal-slope hypothesis. -/
theorem degree_sub_logSectionCount_le
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    let V := fullLatticeAdelicBundle (genericImage (K := K) M)
      (genericImage_fg M) (genericImage_fullSpan M) η
    V.degree (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions -
      logSectionCount M η ≤ comparisonConstant K (Module.finrank K (K ⊗[𝓞 K] M)) := by
  let L := genericImage (K := K) M
  let ξ := fullLatticeGaugeFamily L (genericImage_fg M) (genericImage_fullSpan M) η
  let hξ := fullLatticeGaugeFamily_isHermitian L (genericImage_fg M) (genericImage_fullSpan M) η hη
  have h := (abs_le.mp (abs_logSectionCount_sub_traceDual_sub_degree_le M η hη)).1
  have hT := logSectionCount_nonneg
    (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)
    (originalPrescribedTraceDualFamily M hξ)
  dsimp only at h ⊢
  unfold comparisonConstant
  linarith

/-- Actual negative maximal slope of the actual original trace-dual bundle
removes its h0 term from the sharp one-sided comparison. -/
theorem logSectionCount_sub_degree_le_of_traceDual_maximalSlope_neg
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    let L := genericImage (K := K) M
    let ξ := fullLatticeGaugeFamily L (genericImage_fg M) (genericImage_fullSpan M) η
    let hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions :=
      fullLatticeGaugeFamily_isHermitian L (genericImage_fg M) (genericImage_fullSpan M) η hη
    let T := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M
    let δ := originalPrescribedTraceDualFamily M hξ
    let V := fullLatticeAdelicBundle L (genericImage_fg M) (genericImage_fullSpan M) η
    (fullLatticeAdelicBundle (genericImage (K := K) T)
      (genericImage_fg T) (genericImage_fullSpan T) δ).maximalSlope
        (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions < 0 →
    logSectionCount M η -
        V.degree (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions ≤
      correctedDualityConstant K (Module.finrank K (K ⊗[𝓞 K] M)) +
        (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) *
          ((InfinitePlace.nrComplexPlaces K : ℝ) * Real.log 2 -
            Real.log |(NumberField.discr K : ℝ)| / 2) := by
  let L := genericImage (K := K) M
  let ξ := fullLatticeGaugeFamily L (genericImage_fg M) (genericImage_fullSpan M) η
  let hξ := fullLatticeGaugeFamily_isHermitian L (genericImage_fg M) (genericImage_fullSpan M) η hη
  let T := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M
  let δ := originalPrescribedTraceDualFamily M hξ
  dsimp only
  intro hneg
  have hz := NumberFieldClassicalSectionVanishing.logSectionCount_eq_zero_of_maximalSlope_neg
    T δ hneg
  have h := (abs_le.mp (abs_logSectionCount_sub_traceDual_sub_degree_le M η hη)).2
  change logSectionCount M η - logSectionCount T δ - _ - _ ≤ _ at h
  rw [hz] at h
  linarith

/-- The sharp count/degree comparison for nonnegative minimal slope, with the
signed trace-line correction retained. The actual trace slope theorem and
positive twists discharge the negative-dual-slope premise, including rank zero. -/
theorem abs_logSectionCount_sub_degree_le_of_minimalSlope_nonneg
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    let V := fullLatticeAdelicBundle (genericImage (K := K) M)
      (genericImage_fg M) (genericImage_fullSpan M) η
    0 ≤ V.minimalSlope (Or.inl inferInstance)
      normalizedNumberFieldArchimedeanCompletions →
    |logSectionCount M η - V.degree (Or.inl inferInstance)
      normalizedNumberFieldArchimedeanCompletions| ≤
        comparisonConstant K (Module.finrank K (K ⊗[𝓞 K] M)) +
          (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) *
            max 0 (-(Real.log |(NumberField.discr K : ℝ)| -
              2 * (InfinitePlace.nrComplexPlaces K : ℝ) * Real.log 2)) := by
  let Vof (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)) :=
    fullLatticeAdelicBundle (genericImage (K := K) M)
      (genericImage_fg M) (genericImage_fullSpan M) η
  let Tof (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
      (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :=
    let ξ := fullLatticeGaugeFamily (genericImage (K := K) M)
      (genericImage_fg M) (genericImage_fullSpan M) η
    let hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions :=
      fullLatticeGaugeFamily_isHermitian _ _ _ η hη
    let T := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M
    fullLatticeAdelicBundle (genericImage (K := K) T)
      (genericImage_fg T) (genericImage_fullSpan T) (originalPrescribedTraceDualFamily M hξ)
  change 0 ≤ (Vof η).minimalSlope (Or.inl inferInstance)
    normalizedNumberFieldArchimedeanCompletions → _
  intro hmin
  let n := Module.finrank K (K ⊗[𝓞 K] M)
  let D := (Vof η).degree (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions
  let a := Real.log |(NumberField.discr K : ℝ)| -
    2 * (InfinitePlace.nrComplexPlaces K : ℝ) * Real.log 2
  let χ := (InfinitePlace.nrComplexPlaces K : ℝ) * Real.log 2 -
    Real.log |(NumberField.discr K : ℝ)| / 2
  have haχ : a = -2 * χ := by dsimp only [a, χ]; ring
  have hlower := degree_sub_logSectionCount_le M η hη
  change D - logSectionCount M η ≤ comparisonConstant K n at hlower
  have hupper : logSectionCount M η - D ≤ comparisonConstant K n +
      (n : ℝ) * max 0 (-a) := by
    by_cases ha : 0 ≤ a
    · rw [max_eq_left (neg_nonpos.mpr ha), mul_zero, add_zero]
      have htwist (ε : ℝ) (hε : 0 < ε) : logSectionCount M η - D ≤
          comparisonConstant K n + (n : ℝ) * ε := by
        let t := a + ε
        have ht : 0 ≤ t := by dsimp only [t]; linarith
        let θ := twistFamily η t
        have hθ := twistFamily_isHermitian hη t
        have hμ : (a : EReal) < (Vof θ).minimalSlope (Or.inl inferInstance)
            normalizedNumberFieldArchimedeanCompletions := by
          change _ < (fullLatticeAdelicBundle _ _ _ (twistFamily η t)).minimalSlope _ _
          rw [minimalSlope_twistFamily]
          have hat : (a : EReal) < (t : EReal) := by
            exact_mod_cast (show a < t by dsimp only [t]; linarith)
          exact hat.trans_le (by
            simpa only [Vof, add_zero, zero_add, add_comm] using add_le_add_right hmin (t : EReal))
        have hneg : (Tof θ hθ).maximalSlope (Or.inl inferInstance)
            normalizedNumberFieldArchimedeanCompletions < 0 := by
          erw [NumberFieldClassicalTraceDualSlope.originalPrescribedTraceDual_maximalSlope M θ hθ]
          exact (EReal.sub_neg (Or.inl (EReal.coe_ne_top _))
            (Or.inl (EReal.coe_ne_bot _))).mpr hμ
        have hu := logSectionCount_sub_degree_le_of_traceDual_maximalSlope_neg M θ hθ hneg
        have hm := logSectionCount_le_twistFamily M η ht
        change logSectionCount M θ -
          (fullLatticeAdelicBundle _ _ _ (twistFamily η t)).degree _ _ ≤ _ at hu
        rw [degree_twistFamily] at hu
        change logSectionCount M θ - (D + (n : ℝ) * t) ≤
          correctedDualityConstant K n + (n : ℝ) * χ at hu
        change logSectionCount M η - D ≤
          correctedDualityConstant K n - (n : ℝ) * χ + (n : ℝ) * ε
        dsimp only [t] at hu
        nlinarith [congrArg (fun x : ℝ => (n : ℝ) * x) haχ]
      apply le_of_forall_pos_le_add
      intro ε hε
      have h := htwist (ε / ((n : ℝ) + 1)) (by positivity)
      have hc : (n : ℝ) * (ε / ((n : ℝ) + 1)) ≤ ε := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
        nlinarith
      linarith
    · have hμ : (a : EReal) < (Vof η).minimalSlope (Or.inl inferInstance)
          normalizedNumberFieldArchimedeanCompletions := by
        exact (show (a : EReal) < 0 by exact_mod_cast (lt_of_not_ge ha)).trans_le hmin
      have hneg : (Tof η hη).maximalSlope (Or.inl inferInstance)
          normalizedNumberFieldArchimedeanCompletions < 0 := by
        erw [NumberFieldClassicalTraceDualSlope.originalPrescribedTraceDual_maximalSlope M η hη]
        exact (EReal.sub_neg (Or.inl (EReal.coe_ne_top _))
          (Or.inl (EReal.coe_ne_bot _))).mpr hμ
      have hu := logSectionCount_sub_degree_le_of_traceDual_maximalSlope_neg M η hη hneg
      change logSectionCount M η - D ≤ correctedDualityConstant K n + (n : ℝ) * χ at hu
      rw [max_eq_right (by linarith : 0 ≤ -a)]
      change logSectionCount M η - D ≤ correctedDualityConstant K n - (n : ℝ) * χ + (n : ℝ) * (-a)
      nlinarith [congrArg (fun x : ℝ => (n : ℝ) * x) haχ]
  change |logSectionCount M η - D| ≤ _
  apply abs_le.mpr
  refine ⟨?_, hupper⟩
  have hc : 0 ≤ (n : ℝ) * max 0 (-a) := mul_nonneg (by positivity) (le_max_left _ _)
  linarith

/-- The source discriminant bound for nonnegative minimal slope, with the
exact printed factorial constant and the actual determinant degree. -/
theorem abs_logSectionCount_sub_degree_le_rank_log_discr
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    let V := fullLatticeAdelicBundle (genericImage (K := K) M)
      (genericImage_fg M) (genericImage_fullSpan M) η
    0 ≤ V.minimalSlope (Or.inl inferInstance)
      normalizedNumberFieldArchimedeanCompletions →
    |logSectionCount M η - V.degree (Or.inl inferInstance)
      normalizedNumberFieldArchimedeanCompletions| ≤
        (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) * Real.log |(NumberField.discr K : ℝ)| +
          comparisonConstant K (Module.finrank K (K ⊗[𝓞 K] M)) := by
  dsimp only
  intro hmin
  have h := abs_logSectionCount_sub_degree_le_of_minimalSlope_nonneg M η hη hmin
  have hc := mul_le_mul_of_nonneg_left
    (NumberFieldClassicalWeakDiscriminant.traceDegree_correction_le_log_discr K)
      (show 0 ≤ (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) by positivity)
  exact h.trans (by linarith)

end ArakelovGeometry.NumberFieldClassicalNonnegativeSlopeCount
