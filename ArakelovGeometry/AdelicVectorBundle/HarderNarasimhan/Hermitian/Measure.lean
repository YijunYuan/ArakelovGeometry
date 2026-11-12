/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.Basic
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.VectorMeasure.Integral

import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.OrderedDegree
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Integrals of the actual Hermitian HN rank function

The actual rank function is a finite sum of half-line indicators.
Its integral on the nonnegative half-line gives positive degree, and
its actual atomic jump measure records the ordered-slope multiplicities.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S E)
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]
  [hV : V.toNormFamily.IsHermitian]

private theorem integrableOn_indicator_Iic_Ici (a b : ℝ) :
    IntegrableOn ((Set.Iic b).indicator (fun _ : ℝ ↦ (1 : ℝ))) (Set.Ici a) volume := by
  apply (integrable_indicator_iff measurableSet_Ici).mp
  rw [Set.indicator_indicator, Set.Ici_inter_Iic]
  exact (integrable_indicator_iff measurableSet_Icc).mpr
    (integrableOn_const (measure_Icc_lt_top.ne))

private theorem integral_indicator_Iic_Ici (a b : ℝ) :
    (∫ t in Set.Ici a, (Set.Iic b).indicator (fun _ : ℝ ↦ (1 : ℝ)) t) =
      max (b - a) 0 := by
  rw [← integral_indicator measurableSet_Ici, Set.indicator_indicator,
    Set.Ici_inter_Iic, integral_indicator_const 1 measurableSet_Icc,
    Real.volume_real_Icc, smul_eq_mul, mul_one]

/-- The actual filtration rank, as a real function, is the sum of the
half-line indicators of all actual ordered slots. -/
theorem hermitianHNFiltration_finrank_eq_sum_indicator (t : ℝ) :
    (Module.finrank K (V.hermitianHNFiltration t) : ℝ) =
      ∑ j : Fin (Module.finrank K E),
        (Set.Iic (V.hermitianHNOrderedSlope j)).indicator
          (fun _ : ℝ ↦ (1 : ℝ)) t := by
  classical
  rw [V.hermitianHNFiltration_finrank_eq_card t, Fintype.card_subtype]
  simpa only [Set.indicator_apply, Set.mem_Iic] using
    (Finset.sum_boole (fun j ↦ t ≤ V.hermitianHNOrderedSlope j)
      Finset.univ).symm

/-- Actual filtration rank is integrable above every real threshold. -/
theorem integrableOn_hermitianHNFiltration_finrank (a : ℝ) :
    IntegrableOn (fun t ↦
      (Module.finrank K (V.hermitianHNFiltration t) : ℝ)) (Set.Ici a) volume := by
  classical
  simp_rw [V.hermitianHNFiltration_finrank_eq_sum_indicator]
  exact integrable_finsetSum Finset.univ
    (fun j _ ↦ integrableOn_indicator_Iic_Ici a
      (V.hermitianHNOrderedSlope j))

/-- The genuine Lebesgue integral of actual rank above a threshold is the
finite sum of the positive parts of the shifted actual ordered slopes. -/
theorem integral_hermitianHNFiltration_finrank_Ici (a : ℝ) :
    (∫ t in Set.Ici a,
      (Module.finrank K (V.hermitianHNFiltration t) : ℝ)) =
        ∑ j : Fin (Module.finrank K E),
          max (V.hermitianHNOrderedSlope j - a) 0 := by
  classical
  simp_rw [V.hermitianHNFiltration_finrank_eq_sum_indicator]
  rw [integral_finsetSum Finset.univ
    (fun j _ ↦ integrableOn_indicator_Iic_Ici a
      (V.hermitianHNOrderedSlope j))]
  exact Finset.sum_congr rfl
    (fun j _ ↦ integral_indicator_Iic_Ici a (V.hermitianHNOrderedSlope j))

/-- Positive degree is the genuine rank-function integral on `[0,∞)`. -/
theorem positiveDegree_eq_integral_hermitianHNFiltration_finrank :
    V.positiveDegree =
      (((∫ t in Set.Ici (0 : ℝ),
        (Module.finrank K (V.hermitianHNFiltration t) : ℝ)) : ℝ) : EReal) := by
  rw [V.positiveDegree_eq_sum_max_hermitianHNOrderedSlope,
    V.integral_hermitianHNFiltration_finrank_Ici 0]
  simp only [sub_zero]

/-- The positive atomic jump measure has one atom for each actual ordered
slot, retaining the actual rank multiplicities when slopes repeat. -/
def hermitianHNJumpMeasure : Measure ℝ :=
  ∑ j : Fin (Module.finrank K E), Measure.dirac (V.hermitianHNOrderedSlope j)

instance isFiniteMeasure_hermitianHNJumpMeasure :
    IsFiniteMeasure (V.hermitianHNJumpMeasure) := by
  unfold hermitianHNJumpMeasure
  infer_instance

/-- Every real function is integrable for the actual finite atomic jump
measure; no behavior between the finitely many genuine slopes is required. -/
theorem integrable_hermitianHNJumpMeasure (f : ℝ → ℝ) :
    Integrable f (V.hermitianHNJumpMeasure) := by
  unfold hermitianHNJumpMeasure
  exact integrable_finsetSum_measure.mpr
    (fun j _ ↦ integrable_dirac (by finiteness))

/-- Genuine integration against the jump measure sums the values at all
actual ordered slopes, with their actual multiplicities. -/
theorem integral_hermitianHNJumpMeasure (f : ℝ → ℝ) :
    (∫ t, f t ∂V.hermitianHNJumpMeasure) =
      ∑ j : Fin (Module.finrank K E), f (V.hermitianHNOrderedSlope j) := by
  unfold hermitianHNJumpMeasure
  rw [integral_finsetSum_measure (fun j _ ↦ integrable_dirac (by finiteness))]
  simp only [integral_dirac]

/-- The actual atoms measure the actual rank drop on every half-open
interval. The `[a,b)` endpoints reflect left continuity of the rank function. -/
theorem hermitianHNJumpMeasure_real_Ico (a b : ℝ) (hab : a ≤ b) :
    (V.hermitianHNJumpMeasure).real (Set.Ico a b) =
      (Module.finrank K (V.hermitianHNFiltration a) : ℝ) -
        Module.finrank K (V.hermitianHNFiltration b) := by
  classical
  rw [← integral_indicator_one measurableSet_Ico,
    V.integral_hermitianHNJumpMeasure,
    V.hermitianHNFiltration_finrank_eq_sum_indicator a,
    V.hermitianHNFiltration_finrank_eq_sum_indicator b,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Set.indicator_apply, Pi.one_apply, Set.mem_Ico, Set.mem_Iic]
  split_ifs <;> simp_all <;> linarith

/-- The signed jump measure of the actual decreasing left-continuous rank
function is the negative of its positive atomic jump measure. -/
def hermitianHNSignedJumpMeasure : SignedMeasure ℝ :=
  -(V.hermitianHNJumpMeasure).toSignedMeasure

/-- The signed jump measure equals the actual rank increment on `[a,b)`. -/
theorem hermitianHNSignedJumpMeasure_Ico (a b : ℝ) (hab : a ≤ b) :
    V.hermitianHNSignedJumpMeasure (Set.Ico a b) =
      (Module.finrank K (V.hermitianHNFiltration b) : ℝ) -
        Module.finrank K (V.hermitianHNFiltration a) := by
  unfold hermitianHNSignedJumpMeasure
  rw [_root_.neg_apply, Measure.toSignedMeasure_apply_measurable measurableSet_Ico,
    V.hermitianHNJumpMeasure_real_Ico a b hab, neg_sub]

/-- Actual signed integration gives the negative sum over genuine ordered
slots, by the canonical Bochner-to-signed-measure integration bridge. -/
theorem integral_hermitianHNSignedJumpMeasure (f : ℝ → ℝ) :
    (∫ᵛ t, f t ∂<•V.hermitianHNSignedJumpMeasure) =
      -∑ j : Fin (Module.finrank K E), f (V.hermitianHNOrderedSlope j) := by
  unfold hermitianHNSignedJumpMeasure
  rw [VectorMeasure.integral_neg_vectorMeasure, VectorMeasure.integral_toSignedMeasure,
    V.integral_hermitianHNJumpMeasure]

/-- Ordinary degree is the negative first moment of the actual signed jump
measure of the rank function, including the zero measure in rank zero. -/
theorem degree_eq_neg_integral_hermitianHNSignedJumpMeasure :
    V.degree =
      -(∫ᵛ t, t ∂<•V.hermitianHNSignedJumpMeasure) := by
  rw [V.integral_hermitianHNSignedJumpMeasure, neg_neg]
  exact (V.sum_hermitianHNOrderedSlope_eq_degree).symm

end

end ArakelovGeometry.AdelicVectorBundle
