/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.GeneralHNOrdered
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integrals and the signed jump measure of the actual general HN filtration

The accepted rank-count formula for the actual general HN filtration gives
its genuine Lebesgue integrals and finite signed jump measure, without a
Hermitian hypothesis. Compactly supported C¹ tests identify the measure
as its weak derivative. The degree inequalities are separate results.
-/

open scoped BigOperators
open MeasureTheory

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S E)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)

private theorem generalHN_integrableOn_indicator_Iic_Ici (a b : ℝ) :
    IntegrableOn ((Set.Iic b).indicator (fun _ : ℝ ↦ (1 : ℝ))) (Set.Ici a) volume := by
  apply (integrable_indicator_iff measurableSet_Ici).mp
  rw [Set.indicator_indicator, Set.Ici_inter_Iic]
  exact (integrable_indicator_iff measurableSet_Icc).mpr
    (integrableOn_const (measure_Icc_lt_top.ne))

private theorem generalHN_integral_indicator_Iic_Ici (a b : ℝ) :
    (∫ t in Set.Ici a, (Set.Iic b).indicator (fun _ : ℝ ↦ (1 : ℝ)) t) =
      max (b - a) 0 := by
  rw [← integral_indicator measurableSet_Ici, Set.indicator_indicator,
    Set.Ici_inter_Iic, integral_indicator_const 1 measurableSet_Icc,
    Real.volume_real_Icc, smul_eq_mul, mul_one]

/-- The actual filtration rank, as a real function, is the sum of the
half-line indicators of all actual ordered slots. -/
theorem generalHNFiltration_finrank_eq_sum_indicator (t : ℝ) :
    (Module.finrank K (V.generalHNFiltration hS hN t) : ℝ) =
      ∑ j : Fin (Module.finrank K E),
        (Set.Iic (V.generalHNOrderedSlope hS hN j)).indicator
          (fun _ : ℝ ↦ (1 : ℝ)) t := by
  classical
  rw [V.generalHNFiltration_finrank_eq_card hS hN t]
  simpa only [Set.indicator_apply, Set.mem_Iic] using
    (Finset.sum_boole (fun j ↦ t ≤ V.generalHNOrderedSlope hS hN j)
      Finset.univ).symm

/-- Actual filtration rank is integrable above every real threshold. -/
theorem integrableOn_generalHNFiltration_finrank (a : ℝ) :
    IntegrableOn (fun t ↦
      (Module.finrank K (V.generalHNFiltration hS hN t) : ℝ)) (Set.Ici a) volume := by
  classical
  simp_rw [V.generalHNFiltration_finrank_eq_sum_indicator hS hN]
  exact integrable_finsetSum Finset.univ
    (fun j _ ↦ generalHN_integrableOn_indicator_Iic_Ici a
      (V.generalHNOrderedSlope hS hN j))

/-- The genuine Lebesgue integral of actual rank above a threshold is the
finite sum of the positive parts of the shifted actual ordered slopes. -/
theorem integral_generalHNFiltration_finrank_Ici (a : ℝ) :
    (∫ t in Set.Ici a,
      (Module.finrank K (V.generalHNFiltration hS hN t) : ℝ)) =
        ∑ j : Fin (Module.finrank K E),
          max (V.generalHNOrderedSlope hS hN j - a) 0 := by
  classical
  simp_rw [V.generalHNFiltration_finrank_eq_sum_indicator hS hN]
  rw [integral_finsetSum Finset.univ
    (fun j _ ↦ generalHN_integrableOn_indicator_Iic_Ici a
      (V.generalHNOrderedSlope hS hN j))]
  exact Finset.sum_congr rfl
    (fun j _ ↦ generalHN_integral_indicator_Iic_Ici a (V.generalHNOrderedSlope hS hN j))

/-- The source rank integral on the nonnegative half-line is the sum of
positive parts of the actual general ordered slopes. -/
theorem integral_generalHNFiltration_finrank_Ici_zero :
    (∫ t in Set.Ici (0 : ℝ),
      (Module.finrank K (V.generalHNFiltration hS hN t) : ℝ)) =
        ∑ j : Fin (Module.finrank K E), max (V.generalHNOrderedSlope hS hN j) 0 := by
  rw [V.integral_generalHNFiltration_finrank_Ici hS hN 0]
  simp only [sub_zero]

/-- The positive atomic jump measure has one atom for each actual ordered
slot, retaining the actual rank multiplicities when slopes repeat. -/
def generalHNJumpMeasure : Measure ℝ :=
  ∑ j : Fin (Module.finrank K E), Measure.dirac (V.generalHNOrderedSlope hS hN j)

instance isFiniteMeasure_generalHNJumpMeasure :
    IsFiniteMeasure (V.generalHNJumpMeasure hS hN) := by
  unfold generalHNJumpMeasure
  infer_instance

/-- Every real function is integrable for the actual finite atomic jump
measure; no behavior between the finitely many genuine slopes is required. -/
theorem integrable_generalHNJumpMeasure (f : ℝ → ℝ) :
    Integrable f (V.generalHNJumpMeasure hS hN) := by
  unfold generalHNJumpMeasure
  exact integrable_finsetSum_measure.mpr
    (fun j _ ↦ integrable_dirac (by finiteness))

/-- Genuine integration against the jump measure sums the values at all
actual ordered slopes, with their actual multiplicities. -/
theorem integral_generalHNJumpMeasure (f : ℝ → ℝ) :
    (∫ t, f t ∂V.generalHNJumpMeasure hS hN) =
      ∑ j : Fin (Module.finrank K E), f (V.generalHNOrderedSlope hS hN j) := by
  unfold generalHNJumpMeasure
  rw [integral_finsetSum_measure (fun j _ ↦ integrable_dirac (by finiteness))]
  simp only [integral_dirac]

/-- The actual atoms measure the actual rank drop on every half-open
interval. The `[a,b)` endpoints reflect left continuity of the rank function. -/
theorem generalHNJumpMeasure_real_Ico (a b : ℝ) (hab : a ≤ b) :
    (V.generalHNJumpMeasure hS hN).real (Set.Ico a b) =
      (Module.finrank K (V.generalHNFiltration hS hN a) : ℝ) -
        Module.finrank K (V.generalHNFiltration hS hN b) := by
  classical
  rw [← integral_indicator_one measurableSet_Ico,
    V.integral_generalHNJumpMeasure hS hN,
    V.generalHNFiltration_finrank_eq_sum_indicator hS hN a,
    V.generalHNFiltration_finrank_eq_sum_indicator hS hN b,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Set.indicator_apply, Pi.one_apply, Set.mem_Ico, Set.mem_Iic]
  split_ifs <;> simp_all <;> linarith

/-- The signed jump measure of the actual decreasing left-continuous rank
function is the negative of its positive atomic jump measure. -/
def generalHNSignedJumpMeasure : SignedMeasure ℝ :=
  -(V.generalHNJumpMeasure hS hN).toSignedMeasure

/-- The signed jump measure equals the actual rank increment on `[a,b)`. -/
theorem generalHNSignedJumpMeasure_Ico (a b : ℝ) (hab : a ≤ b) :
    V.generalHNSignedJumpMeasure hS hN (Set.Ico a b) =
      (Module.finrank K (V.generalHNFiltration hS hN b) : ℝ) -
        Module.finrank K (V.generalHNFiltration hS hN a) := by
  unfold generalHNSignedJumpMeasure
  rw [_root_.neg_apply, Measure.toSignedMeasure_apply_measurable measurableSet_Ico,
    V.generalHNJumpMeasure_real_Ico hS hN a b hab, neg_sub]

/-- Actual signed integration gives the negative sum over genuine ordered
slots, by the canonical Bochner-to-signed-measure integration bridge. -/
theorem integral_generalHNSignedJumpMeasure (f : ℝ → ℝ) :
    (∫ᵛ t, f t ∂<•V.generalHNSignedJumpMeasure hS hN) =
      -∑ j : Fin (Module.finrank K E), f (V.generalHNOrderedSlope hS hN j) := by
  unfold generalHNSignedJumpMeasure
  rw [VectorMeasure.integral_neg_vectorMeasure, VectorMeasure.integral_toSignedMeasure,
    V.integral_generalHNJumpMeasure hS hN]

/-- The genuine signed first moment of the actual rank-jump measure is
minus the sum of all actual general ordered slopes, including rank zero. -/
theorem integral_id_generalHNSignedJumpMeasure :
    (∫ᵛ t, t ∂<•V.generalHNSignedJumpMeasure hS hN) =
      -∑ j : Fin (Module.finrank K E), V.generalHNOrderedSlope hS hN j :=
  V.integral_generalHNSignedJumpMeasure hS hN (fun t ↦ t)

private theorem generalHN_rank_mul_eq_sum_indicator (g : ℝ → ℝ) :
    (fun t ↦ (Module.finrank K (V.generalHNFiltration hS hN t) : ℝ) * g t) =
      fun t ↦ ∑ j : Fin (Module.finrank K E),
        (Set.Iic (V.generalHNOrderedSlope hS hN j)).indicator g t := by
  classical
  funext t
  rw [V.generalHNFiltration_finrank_eq_sum_indicator hS hN, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Set.indicator_apply]
  split_ifs <;> simp

/-- The actual rank times a compactly supported test derivative is genuinely
Lebesgue integrable; the integral does not use a default value. -/
theorem integrable_generalHNFiltration_finrank_mul_deriv
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun t ↦
      (Module.finrank K (V.generalHNFiltration hS hN t) : ℝ) * deriv φ t) volume := by
  classical
  rw [V.generalHN_rank_mul_eq_sum_indicator hS hN]
  have hd : Integrable (deriv φ) volume :=
    (hφ.continuous_deriv le_rfl).integrable_of_hasCompactSupport hc.deriv
  exact integrable_finsetSum Finset.univ (fun j _ ↦
    (integrable_indicator_iff measurableSet_Iic).mpr hd.integrableOn)

/-- Fundamental calculus evaluates the actual rank against every compactly
supported continuously differentiable test derivative. -/
theorem integral_generalHNFiltration_finrank_mul_deriv
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (∫ t : ℝ, (Module.finrank K (V.generalHNFiltration hS hN t) : ℝ) * deriv φ t) =
      ∑ j : Fin (Module.finrank K E), φ (V.generalHNOrderedSlope hS hN j) := by
  classical
  rw [V.generalHN_rank_mul_eq_sum_indicator hS hN]
  have hd : Integrable (deriv φ) volume :=
    (hφ.continuous_deriv le_rfl).integrable_of_hasCompactSupport hc.deriv
  rw [integral_finsetSum Finset.univ (fun j _ ↦
    (integrable_indicator_iff measurableSet_Iic).mpr hd.integrableOn)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_indicator measurableSet_Iic]
  exact HasCompactSupport.integral_Iic_deriv_eq hφ hc _

/-- The actual canonical signed rank-jump measure is the distributional
derivative of the actual rank function, on all compactly supported C¹ tests. -/
theorem generalHNSignedJumpMeasure_weakDerivative
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    -(∫ t : ℝ, (Module.finrank K (V.generalHNFiltration hS hN t) : ℝ) * deriv φ t) =
      ∫ᵛ t, φ t ∂<•V.generalHNSignedJumpMeasure hS hN := by
  rw [V.integral_generalHNFiltration_finrank_mul_deriv hS hN φ hφ hc,
    V.integral_generalHNSignedJumpMeasure hS hN]

end

end ArakelovGeometry.AdelicVectorBundle
