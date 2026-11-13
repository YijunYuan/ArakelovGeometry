/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic

import ArakelovGeometry.AdelicVectorBundle.Slope.Finite
import ArakelovGeometry.AdelicVectorBundle.Subquotient.Restriction.Functor
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Positive degree of actual adelic vector bundles

The supremum ranges over every actual rational restriction, including zero.
The proved common rank-degree bound gives finiteness; attainment is not assumed.
-/

@[expose] public section

namespace ArakelovGeometry

noncomputable section

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace AdelicVectorBundle

/-- Source positive degree, initially as the extended supremum over all
actual subspace degrees. Its finiteness is proved below. -/
def positiveDegree (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] : EReal :=
  ⨆ U : Submodule K V, ((V.restrictOfNormMeasurability U).degree : EReal)

/-- Every actual restricted degree is among the terms of positive degree. -/
theorem degree_restrict_le_positiveDegree (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (U : Submodule K V) :
    ((V.restrictOfNormMeasurability U).degree : EReal) ≤
      V.positiveDegree := le_iSup
        (fun T : Submodule K V ↦ ((V.restrictOfNormMeasurability T).degree : EReal)) U

/-- The zero subspace supplies nonnegativity, even in rank zero. -/
theorem positiveDegree_nonneg (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    0 ≤ V.positiveDegree := by
  have h := V.degree_restrict_le_positiveDegree ⊥
  rw [degree_eq_zero_of_finrank_eq_zero _ (finrank_bot K V), EReal.coe_zero] at h
  exact h

/-- The total actual restriction shows degree is at most positive degree. -/
theorem degree_le_positiveDegree (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    (V.degree : EReal) ≤ V.positiveDegree := by
  simpa only [V.degree_restrict_top] using
    V.degree_restrict_le_positiveDegree ⊤

/-- Any bound on all actual restricted degrees bounds their supremum. -/
theorem positiveDegree_le (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] {a : EReal}
    (ha : ∀ U : Submodule K V,
      ((V.restrictOfNormMeasurability U).degree : EReal) ≤ a) :
    V.positiveDegree ≤ a := iSup_le ha

/-- The zero bundle's positive degree is zero, rather than an empty supremum. -/
theorem positiveDegree_eq_zero_of_finrank_eq_zero (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (hr : Module.finrank K V = 0) : V.positiveDegree = 0 := by
  apply le_antisymm _ (V.positiveDegree_nonneg)
  apply V.positiveDegree_le
  intro U
  have hU : Module.finrank K U = 0 := by
    have h := U.finrank_le
    omega
  rw [degree_eq_zero_of_finrank_eq_zero _ hU, EReal.coe_zero]

/-- Increasing the actual norms decreases every restricted degree and hence
positive degree. -/
theorem positiveDegree_antitone (V : AdelicVectorBundle S) (W : NormFamily S V) [W.IsAdelic]
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (h : V.toNormFamily ≤ W) :
    W.toAdelicVectorBundle.positiveDegree ≤ V.positiveDegree := by
  apply W.toAdelicVectorBundle.positiveDegree_le
  intro U
  have hU : (V.restrictOfNormMeasurability U).toNormFamily ≤
      (W.toAdelicVectorBundle.restrictOfNormMeasurability U).toNormFamily := fun ω z ↦ h ω _
  exact (EReal.coe_le_coe_iff.mpr (degree_antitone (V.restrictOfNormMeasurability U)
    (W.toAdelicVectorBundle.restrictOfNormMeasurability U).toNormFamily
    (hW := (W.toAdelicVectorBundle.restrictOfNormMeasurability U).toIsAdelic) hU)).trans
    (V.degree_restrict_le_positiveDegree U)

/-- Positive degree of an actual restriction is bounded by ambient positive
degree, using the canonical nested restriction degree isometry. -/
theorem positiveDegree_restrict_le (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (W : Submodule K V) :
    (V.restrictOfNormMeasurability W).positiveDegree ≤ V.positiveDegree := by
  apply positiveDegree_le _
  intro U
  let T := U.map W.subtype
  have hTW : T ≤ W := by
    rintro x ⟨u, _, rfl⟩
    exact u.property
  have hcomap : T.comap W.subtype = U :=
    Submodule.comap_map_eq_of_injective W.subtype_injective U
  have hd := V.degree_restrict_restrict T W hTW
  rw [hcomap] at hd
  rw [hd]
  exact V.degree_restrict_le_positiveDegree T

/-- The produced uniform rank-degree bound makes positive degree finite.
No maximizing subspace, caller-supplied bound or HN object is required. -/
theorem positiveDegree_lt_top (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    V.positiveDegree < ⊤ := by
  obtain ⟨C, hC⟩ := V.exists_degree_restrict_le_rank_mul
  have hb : V.positiveDegree ≤
      ((Module.finrank K V : ℝ) * max C 0 : ℝ) := by
    apply V.positiveDegree_le
    intro U
    apply EReal.coe_le_coe_iff.mpr
    exact (hC U).trans ((mul_le_mul_of_nonneg_left (le_max_left C 0)
      (Nat.cast_nonneg _)).trans (mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr U.finrank_le) (le_max_right C 0)))
  exact hb.trans_lt (EReal.coe_lt_top _)

/-- Both extended endpoints are excluded before positive degree is represented
by a real number. This includes the zero bundle. -/
theorem exists_positiveDegree_eq_coe (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    ∃ c : ℝ, V.positiveDegree = (c : EReal) := by
  lift V.positiveDegree to ℝ using
    ⟨(V.positiveDegree_lt_top).ne,
      ((EReal.bot_lt_coe 0).trans_le (V.positiveDegree_nonneg)).ne'⟩ with c
  exact ⟨c, rfl⟩

/-- Positive degree vanishes precisely when every actual subspace degree is
nonpositive. The zero subspace supplies the reverse inequality. -/
theorem positiveDegree_eq_zero_iff (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    V.positiveDegree = 0 ↔ ∀ U : Submodule K V,
      (V.restrictOfNormMeasurability U).degree ≤ 0 := by
  constructor
  · intro h U
    have hd := V.degree_restrict_le_positiveDegree U
    rw [h, ← EReal.coe_zero] at hd
    exact EReal.coe_le_coe_iff.mp hd
  · intro h
    exact le_antisymm (V.positiveDegree_le (fun U ↦ by
      exact_mod_cast h U)) (V.positiveDegree_nonneg)

/-- The actual maximal slope detects vanishing positive degree, including the
rank-zero maximal slope convention. -/
theorem positiveDegree_eq_zero_iff_maximalSlope_nonpos (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    V.positiveDegree = 0 ↔ V.maximalSlope ≤ 0 := by
  rw [V.positiveDegree_eq_zero_iff]
  constructor
  · intro h
    apply V.maximalSlope_le
    intro U hU
    apply EReal.coe_le_coe_iff.mpr
    change (V.restrictOfNormMeasurability U).degree /
      (Module.finrank K U : ℝ) ≤ 0
    exact div_nonpos_of_nonpos_of_nonneg (h U) (Nat.cast_nonneg _)
  · intro h U
    by_cases hU : Module.finrank K U = 0
    · exact (degree_eq_zero_of_finrank_eq_zero _ hU).le
    · have hs := (V.slope_restrict_le_maximalSlope U (Nat.pos_of_ne_zero hU)).trans h
      have hs' : (V.restrictOfNormMeasurability U).slope ≤ 0 := by
        exact_mod_cast hs
      rw [degree_eq_rank_mul_slope]
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hs'

end AdelicVectorBundle

end

end ArakelovGeometry
