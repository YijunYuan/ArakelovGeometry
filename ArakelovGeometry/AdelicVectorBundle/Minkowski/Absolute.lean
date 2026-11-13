/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.AbsoluteInvariants.RegularBase

import Mathlib.CategoryTheory.Category.Init

/-!
# Absolute Minkowski levels on actual bundles

The source predicate uses the actual ordinary closure first minimum and the
canonical full native maximal-slope supremum under original regularity.
It quantifies over every positive-rank bundle without admissibility.
-/

@[expose] public section

noncomputable section
namespace ArakelovGeometry.AdelicStructure

universe u v w
variable {K : Type u} [Field K]

/-- The absolute clause of source Definition4.3.73; no finite-place
ultrametricity hypothesis is imposed on the quantified actual bundles. -/
def HasAbsoluteMinkowskiPropertyAtLevel (S : AdelicStructure.{u, v} K) [S.IsProper]
    [hreg : S.HasRegularBase]
    [hN : S.IsArchimedeanNormalized] (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀
    (V : AdelicVectorBundle.{w} S), 0 < Module.finrank K V →
      V.absoluteMaximalSlopeOfRegularBase -
        (C * Real.log (Module.finrank K V) : ℝ) ≤
          V.absoluteMaximalLogarithmicMinimum

variable {S : AdelicStructure.{u, v} K} [S.IsProper]
  [hreg : S.HasRegularBase]
  [hN : S.IsArchimedeanNormalized] {C D : ℝ}

/-- Larger absolute levels weaken the actual universal inequality. -/
theorem HasAbsoluteMinkowskiPropertyAtLevel.mono
    (h : S.HasAbsoluteMinkowskiPropertyAtLevel.{u, v, w} C) (hCD : C ≤ D) :
    S.HasAbsoluteMinkowskiPropertyAtLevel.{u, v, w} D := by
  refine ⟨h.1.trans hCD, fun V hr => ?_⟩
  have hlog : 0 ≤ Real.log (Module.finrank K V) :=
    Real.log_nonneg (by exact_mod_cast hr)
  exact (EReal.sub_le_sub le_rfl
    (EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_right hCD hlog))).trans
      (h.2 V hr)

/-- A real correction can be moved across the absolute inequality without
assuming finite minima or an attained threshold. -/
theorem HasAbsoluteMinkowskiPropertyAtLevel.maximalSlope_le
    (h : S.HasAbsoluteMinkowskiPropertyAtLevel.{u, v, w} C)
    (V : AdelicVectorBundle.{w} S) (hr : 0 < Module.finrank K V) :
    V.absoluteMaximalSlopeOfRegularBase ≤
      V.absoluteMaximalLogarithmicMinimum +
        (C * Real.log (Module.finrank K V) : ℝ) :=
  (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mp (h.2 V hr)

/-- The zero rank-one correction and the actual absolute first-minimum
comparison give equality on every rank-one actual bundle. -/
theorem HasAbsoluteMinkowskiPropertyAtLevel.firstMinimum_eq_maximalSlope_of_finrank_eq_one
    (h : S.HasAbsoluteMinkowskiPropertyAtLevel.{u, v, w} C)
    (V : AdelicVectorBundle.{w} S) (hr : Module.finrank K V = 1) :
    V.absoluteMaximalLogarithmicMinimum =
      V.absoluteMaximalSlopeOfRegularBase := by
  apply le_antisymm
  · exact V.absoluteMaximalLogarithmicMinimum_le_absoluteMaximalSlopeOfRegularBase
  · have hp : 0 < Module.finrank K V := by omega
    simpa only [hr, Nat.cast_one, Real.log_one, mul_zero, EReal.coe_zero, add_zero] using
      h.maximalSlope_le V hp

end ArakelovGeometry.AdelicStructure
