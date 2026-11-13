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
def absolutePositiveDegreeOfPositiveAtoms (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces] : EReal :=
  ⨆ A : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E),
    (ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms A : EReal)

/-- The actual positive-rank native means, with empty supremum `⊥` in rank zero. -/
def absoluteMaximalSlopeOfPositiveAtoms (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces] : EReal :=
  ⨆ A : {A : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E) //
      0 < Module.finrank (AlgebraicClosure K) A},
    (ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms A.val /
      (Module.finrank (AlgebraicClosure K) A.val : ℝ) : EReal)

/-- Every actual native degree occurs in the absolute positive supremum. -/
theorem nativeRestrictionDegree_le_absolutePositiveDegreeOfPositiveAtoms
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces]
    (A : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E)) :
    (ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms A : EReal) ≤
      ξ.absolutePositiveDegreeOfPositiveAtoms :=
  le_iSup (fun B : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E) =>
    (ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms B : EReal)) A

/-- The actual zero native subspace supplies nonnegativity. -/
theorem absolutePositiveDegreeOfPositiveAtoms_nonneg
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces] :
    0 ≤ ξ.absolutePositiveDegreeOfPositiveAtoms := by
  have h := ξ.nativeRestrictionDegree_le_absolutePositiveDegreeOfPositiveAtoms ⊥
  rw [ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms_eq_zero_of_finrank_eq_zero
      ⊥ (finrank_bot _ _), EReal.coe_zero] at h
  exact h

/-- Every actual native subspace has degree zero in ambient rank zero. -/
theorem absolutePositiveDegreeOfPositiveAtoms_eq_zero_of_finrank_eq_zero
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces]
    (hr : Module.finrank K E = 0) :
    ξ.absolutePositiveDegreeOfPositiveAtoms = 0 := by
  apply le_antisymm _ (ξ.absolutePositiveDegreeOfPositiveAtoms_nonneg)
  apply iSup_le
  intro A
  have hA : Module.finrank (AlgebraicClosure K) A = 0 := by
    have h := A.finrank_le
    rw [Module.finrank_baseChange, hr] at h
    omega
  rw [ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms_eq_zero_of_finrank_eq_zero
      A hA, EReal.coe_zero]

/-- There are no positive-rank native subspaces in ambient rank zero. -/
theorem absoluteMaximalSlopeOfPositiveAtoms_eq_bot_of_finrank_eq_zero
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces]
    (hr : Module.finrank K E = 0) :
    ξ.absoluteMaximalSlopeOfPositiveAtoms = ⊥ := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro A
  have h := A.val.finrank_le
  have hA := A.property
  rw [Module.finrank_baseChange, hr] at h
  omega

/-- The produced rank-degree bound excludes positive infinity. -/
theorem absolutePositiveDegreeOfPositiveAtoms_lt_top
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces] :
    ξ.absolutePositiveDegreeOfPositiveAtoms < ⊤ := by
  obtain ⟨C, hC⟩ := ξ.exists_nativeAlgebraicRestrictionDegreeOfPositiveAtoms_le_rank_mul
    (L := AlgebraicClosure K)
  have hb : ξ.absolutePositiveDegreeOfPositiveAtoms ≤
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
theorem nativeMean_le_absoluteMaximalSlopeOfPositiveAtoms
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces]
    (A : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E))
    (hr : 0 < Module.finrank (AlgebraicClosure K) A) :
    (ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms A /
      (Module.finrank (AlgebraicClosure K) A : ℝ) : EReal) ≤
      ξ.absoluteMaximalSlopeOfPositiveAtoms :=
  le_iSup (fun B : {B : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E) //
      0 < Module.finrank (AlgebraicClosure K) B} =>
    (ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms B.val /
      (Module.finrank (AlgebraicClosure K) B.val : ℝ) : EReal)) ⟨A, hr⟩

/-- All actual positive-rank native means have a produced finite upper bound. -/
theorem absoluteMaximalSlopeOfPositiveAtoms_lt_top
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces] :
    ξ.absoluteMaximalSlopeOfPositiveAtoms < ⊤ := by
  obtain ⟨C, hC⟩ := ξ.exists_nativeAlgebraicRestrictionDegreeOfPositiveAtoms_le_rank_mul
    (L := AlgebraicClosure K)
  have hb : ξ.absoluteMaximalSlopeOfPositiveAtoms ≤ (C : EReal) := by
    apply iSup_le
    intro A
    apply EReal.coe_le_coe_iff.mpr
    exact (div_le_iff₀ (Nat.cast_pos.mpr A.property)).mpr (by
      simpa only [mul_comm] using hC A.val)
  exact hb.trans_lt (EReal.coe_lt_top C)

/-- Both extended endpoints are excluded before representing positive degree as real. -/
theorem exists_absolutePositiveDegreeOfPositiveAtoms_eq_coe
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces] :
    ∃ c : ℝ, ξ.absolutePositiveDegreeOfPositiveAtoms = (c : EReal) := by
  lift ξ.absolutePositiveDegreeOfPositiveAtoms to ℝ using
    ⟨(ξ.absolutePositiveDegreeOfPositiveAtoms_lt_top).ne,
      ((EReal.bot_lt_coe 0).trans_le
        (ξ.absolutePositiveDegreeOfPositiveAtoms_nonneg)).ne'⟩ with c
  exact ⟨c, rfl⟩

/-- The actual whole native space makes the absolute maximal slope real in positive rank. -/
theorem exists_absoluteMaximalSlopeOfPositiveAtoms_eq_coe
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces]
    (hr : 0 < Module.finrank K E) :
    ∃ c : ℝ, ξ.absoluteMaximalSlopeOfPositiveAtoms = (c : EReal) := by
  have hA : 0 < Module.finrank (AlgebraicClosure K)
      (⊤ : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E)) := by
    simpa only [finrank_top, Module.finrank_baseChange] using hr
  have hbot : ⊥ < ξ.absoluteMaximalSlopeOfPositiveAtoms :=
    (EReal.bot_lt_coe _).trans_le
      (ξ.nativeMean_le_absoluteMaximalSlopeOfPositiveAtoms ⊤ hA)
  lift ξ.absoluteMaximalSlopeOfPositiveAtoms to ℝ using
    ⟨(ξ.absoluteMaximalSlopeOfPositiveAtoms_lt_top).ne, hbot.ne'⟩ with c
  exact ⟨c, rfl⟩

end NormFamily
namespace AdelicVectorBundle

/-- The entire geometric positive-degree supremum is the existing common-density value. -/
theorem absolutePositiveDegreeOfPositiveAtoms_eq_common
    (V : AdelicVectorBundle S)
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces]
    [S.HasCommonCountableDenseSubfield]
    [S.IsArchimedeanNormalized] :
    V.toNormFamily.absolutePositiveDegreeOfPositiveAtoms =
      V.absolutePositiveDegree := rfl

/-- Actual terms, ranks and index sets also identify the common-density maximal slope. -/
theorem absoluteMaximalSlopeOfPositiveAtoms_eq_common
    (V : AdelicVectorBundle S)
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces]
    [S.HasCommonCountableDenseSubfield]
    [S.IsArchimedeanNormalized] :
    V.toNormFamily.absoluteMaximalSlopeOfPositiveAtoms =
      V.absoluteMaximalSlope := rfl

/-- The geometric positive-degree supremum equals the countable-discrete value on overlap. -/
theorem absolutePositiveDegreeOfPositiveAtoms_eq_countable_discrete
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]
    (V : AdelicVectorBundle S)
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces]
    [S.IsArchimedeanNormalized] :
    V.toNormFamily.absolutePositiveDegreeOfPositiveAtoms =
      V.absolutePositiveDegreeOfCountableDiscreteBase := rfl

/-- The geometric maximal-slope supremum equals the countable-discrete value on overlap. -/
theorem absoluteMaximalSlopeOfPositiveAtoms_eq_countable_discrete
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]
    (V : AdelicVectorBundle S)
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces]
    [S.IsArchimedeanNormalized] :
    V.toNormFamily.absoluteMaximalSlopeOfPositiveAtoms =
      V.absoluteMaximalSlopeOfCountableDiscreteBase := rfl

end AdelicVectorBundle
end ArakelovGeometry
