/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.Algebraic.RestrictionDegree

import Mathlib.CategoryTheory.Category.Init

/-!
# Actual positive-atomic geometric absolute invariants

Suprema range over every actual closure-native subspace and its canonical
measurable-determinant degree. Produced uniform native degree bounds establish
finiteness. Exact bridges identify these with the existing common-density and
countable-discrete invariants on their common domains.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section
namespace ArakelovGeometry

variable {K E : Type*} [Field K] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [MeasurableSingletonClass S.Ω]

namespace NormFamily

/-- The supremum of the actual degrees of all native closure subspaces. -/
def absolutePositiveDegreeOfPositiveSingletons (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces] : EReal :=
  ⨆ A : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E),
    (ξ.nativeAlgebraicRestrictionDegreeOfPositiveSingletons A : EReal)

/-- The actual positive-rank native means, with empty supremum `⊥` in rank zero. -/
def absoluteMaximalSlopeOfPositiveSingletons (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces] : EReal :=
  ⨆ A : {A : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E) //
      0 < Module.finrank (AlgebraicClosure K) A},
    (ξ.nativeAlgebraicRestrictionDegreeOfPositiveSingletons A.val /
      (Module.finrank (AlgebraicClosure K) A.val : ℝ) : EReal)

/-- Every actual native degree occurs in the absolute positive supremum. -/
theorem nativeRestrictionDegree_le_absolutePositiveDegreeOfPositiveSingletons
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces]
    (A : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E)) :
    (ξ.nativeAlgebraicRestrictionDegreeOfPositiveSingletons A : EReal) ≤
      ξ.absolutePositiveDegreeOfPositiveSingletons :=
  le_iSup (fun B : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E) =>
    (ξ.nativeAlgebraicRestrictionDegreeOfPositiveSingletons B : EReal)) A

/-- The actual zero native subspace supplies nonnegativity. -/
theorem absolutePositiveDegreeOfPositiveSingletons_nonneg
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces] :
    0 ≤ ξ.absolutePositiveDegreeOfPositiveSingletons := by
  have h := ξ.nativeRestrictionDegree_le_absolutePositiveDegreeOfPositiveSingletons ⊥
  rw [ξ.nativeAlgebraicRestrictionDegreeOfPositiveSingletons_eq_zero_of_finrank_eq_zero
      ⊥ (finrank_bot _ _), EReal.coe_zero] at h
  exact h

/-- Every actual native subspace has degree zero in ambient rank zero. -/
theorem absolutePositiveDegreeOfPositiveSingletons_eq_zero_of_finrank_eq_zero
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces]
    (hr : Module.finrank K E = 0) :
    ξ.absolutePositiveDegreeOfPositiveSingletons = 0 := by
  apply le_antisymm _ (ξ.absolutePositiveDegreeOfPositiveSingletons_nonneg)
  apply iSup_le
  intro A
  have hA : Module.finrank (AlgebraicClosure K) A = 0 := by
    have h := A.finrank_le
    rw [Module.finrank_baseChange, hr] at h
    omega
  rw [ξ.nativeAlgebraicRestrictionDegreeOfPositiveSingletons_eq_zero_of_finrank_eq_zero
      A hA, EReal.coe_zero]

/-- There are no positive-rank native subspaces in ambient rank zero. -/
theorem absoluteMaximalSlopeOfPositiveSingletons_eq_bot_of_finrank_eq_zero
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces]
    (hr : Module.finrank K E = 0) :
    ξ.absoluteMaximalSlopeOfPositiveSingletons = ⊥ := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro A
  have h := A.val.finrank_le
  have hA := A.property
  rw [Module.finrank_baseChange, hr] at h
  omega

/-- The produced rank-degree bound excludes positive infinity. -/
theorem absolutePositiveDegreeOfPositiveSingletons_lt_top
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces] :
    ξ.absolutePositiveDegreeOfPositiveSingletons < ⊤ := by
  obtain ⟨C, hC⟩ := ξ.exists_nativeAlgebraicRestrictionDegreeOfPositiveSingletons_le_rank_mul
    (L := AlgebraicClosure K)
  have hb : ξ.absolutePositiveDegreeOfPositiveSingletons ≤
      ((Module.finrank K E : ℝ) * max C 0 : ℝ) := by
    apply iSup_le
    intro A
    apply EReal.coe_le_coe_iff.mpr
    have hr : Module.finrank (AlgebraicClosure K) A ≤ Module.finrank K E := by
      simpa only [Module.finrank_baseChange] using A.finrank_le
    exact (hC A).trans ((mul_le_mul_of_nonneg_left (le_max_left C 0)
      (Nat.cast_nonneg _)).trans (mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr hr) (le_max_right C 0)))
  exact hb.trans_lt (EReal.coe_lt_top _)

/-- Every actual positive-rank native mean contributes its own term. -/
theorem nativeMean_le_absoluteMaximalSlopeOfPositiveSingletons
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces]
    (A : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E))
    (hr : 0 < Module.finrank (AlgebraicClosure K) A) :
    (ξ.nativeAlgebraicRestrictionDegreeOfPositiveSingletons A /
      (Module.finrank (AlgebraicClosure K) A : ℝ) : EReal) ≤
      ξ.absoluteMaximalSlopeOfPositiveSingletons :=
  le_iSup (fun B : {B : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E) //
      0 < Module.finrank (AlgebraicClosure K) B} =>
    (ξ.nativeAlgebraicRestrictionDegreeOfPositiveSingletons B.val /
      (Module.finrank (AlgebraicClosure K) B.val : ℝ) : EReal)) ⟨A, hr⟩

/-- All actual positive-rank native means have a produced finite upper bound. -/
theorem absoluteMaximalSlopeOfPositiveSingletons_lt_top
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces] :
    ξ.absoluteMaximalSlopeOfPositiveSingletons < ⊤ := by
  obtain ⟨C, hC⟩ := ξ.exists_nativeAlgebraicRestrictionDegreeOfPositiveSingletons_le_rank_mul
    (L := AlgebraicClosure K)
  have hb : ξ.absoluteMaximalSlopeOfPositiveSingletons ≤ (C : EReal) := by
    apply iSup_le
    intro A
    apply EReal.coe_le_coe_iff.mpr
    exact (div_le_iff₀ (Nat.cast_pos.mpr A.property)).mpr (by
      simpa only [mul_comm] using hC A.val)
  exact hb.trans_lt (EReal.coe_lt_top C)

/-- Both extended endpoints are excluded before representing positive degree as real. -/
theorem exists_absolutePositiveDegreeOfPositiveSingletons_eq_coe
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces] :
    ∃ c : ℝ, ξ.absolutePositiveDegreeOfPositiveSingletons = (c : EReal) := by
  lift ξ.absolutePositiveDegreeOfPositiveSingletons to ℝ using
    ⟨(ξ.absolutePositiveDegreeOfPositiveSingletons_lt_top).ne,
      ((EReal.bot_lt_coe 0).trans_le
        (ξ.absolutePositiveDegreeOfPositiveSingletons_nonneg)).ne'⟩ with c
  exact ⟨c, rfl⟩

/-- The actual whole native space makes the absolute maximal slope real in positive rank. -/
theorem exists_absoluteMaximalSlopeOfPositiveSingletons_eq_coe
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces]
    (hr : 0 < Module.finrank K E) :
    ∃ c : ℝ, ξ.absoluteMaximalSlopeOfPositiveSingletons = (c : EReal) := by
  have hA : 0 < Module.finrank (AlgebraicClosure K)
      (⊤ : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E)) := by
    simpa only [finrank_top, Module.finrank_baseChange] using hr
  have hbot : ⊥ < ξ.absoluteMaximalSlopeOfPositiveSingletons :=
    (EReal.bot_lt_coe _).trans_le
      (ξ.nativeMean_le_absoluteMaximalSlopeOfPositiveSingletons ⊤ hA)
  lift ξ.absoluteMaximalSlopeOfPositiveSingletons to ℝ using
    ⟨(ξ.absoluteMaximalSlopeOfPositiveSingletons_lt_top).ne, hbot.ne'⟩ with c
  exact ⟨c, rfl⟩

end NormFamily
namespace AdelicVectorBundle

/-- The entire geometric positive-degree supremum is the existing common-density value. -/
theorem absolutePositiveDegreeOfPositiveSingletons_eq_common
    (V : AdelicVectorBundle S)
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces]
    [S.HasCommonCountableDenseSubfield]
    [S.IsArchimedeanNormalized] :
    V.toNormFamily.absolutePositiveDegreeOfPositiveSingletons =
      V.absolutePositiveDegree := rfl

/-- Actual terms, ranks and index sets also identify the common-density maximal slope. -/
theorem absoluteMaximalSlopeOfPositiveSingletons_eq_common
    (V : AdelicVectorBundle S)
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces]
    [S.HasCommonCountableDenseSubfield]
    [S.IsArchimedeanNormalized] :
    V.toNormFamily.absoluteMaximalSlopeOfPositiveSingletons =
      V.absoluteMaximalSlope := rfl

/-- The geometric positive-degree supremum equals the countable-discrete value on overlap. -/
theorem absolutePositiveDegreeOfPositiveSingletons_eq_countable_discrete
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]
    (V : AdelicVectorBundle S)
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces]
    [S.IsArchimedeanNormalized] :
    V.toNormFamily.absolutePositiveDegreeOfPositiveSingletons =
      V.absolutePositiveDegreeOfCountableDiscreteBase := rfl

/-- The geometric maximal-slope supremum equals the countable-discrete value on overlap. -/
theorem absoluteMaximalSlopeOfPositiveSingletons_eq_countable_discrete
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]
    (V : AdelicVectorBundle S)
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces]
    [S.IsArchimedeanNormalized] :
    V.toNormFamily.absoluteMaximalSlopeOfPositiveSingletons =
      V.absoluteMaximalSlopeOfCountableDiscreteBase := rfl

end AdelicVectorBundle
end ArakelovGeometry
