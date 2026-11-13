/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Minkowski.Basic

import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.FirstSlope
import ArakelovGeometry.AdelicVectorBundle.Minima.StrongMinkowski
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Actual ordinary-level consequences of the strong Minkowski property

The actual first general ordered slope differs from the maximal slope by
at most the sharp Archimedean logarithmic correction. The universal strong
property therefore produces ordinary level `C + a∞ / 2`. Hermitian bundles
and curves of zero Archimedean mass retain the same level. The unrestricted
positive-level same-constant assertion remains a separate source obligation.
-/

@[expose] public section

noncomputable section
namespace ArakelovGeometry
universe u v w
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]

namespace AdelicVectorBundle
variable {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The actual strong ordered-minimum bound and first-slope defect give the
corrected first-minimum estimate, without assuming attainment. -/
theorem maximalSlope_le_maximalLogarithmicMinimum_add_of_strongMinkowski
    (V : AdelicVectorBundle.{w} S) [hV : V.toNormFamily.IsUltrametric]
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    {C : ℝ} (hM : S.HasStrongMinkowskiPropertyAtLevel.{u, v, w} C)
    (hr : 0 < Module.finrank K V) :
    V.maximalSlope ≤ V.maximalLogarithmicMinimum +
      ((C + (S.v S.Ωinf).toReal / 2) * Real.log (Module.finrank K V) : ℝ) := by
  have hfirst := V.maximalSlope_le_generalHNOrderedSlope_zero_add_log_rank hr
  have hminimum := V.generalHNOrderedSlope_le_logarithmicMinimum_add_log_rank
     hM ⟨0, hr⟩
  change (V.generalHNOrderedSlope ⟨0, hr⟩ : EReal) ≤
    V.maximalLogarithmicMinimum + (C * Real.log (Module.finrank K V) : ℝ) at hminimum
  rw [EReal.coe_add] at hfirst
  have h := hfirst.trans (add_le_add hminimum (le_refl
    ((Real.log (Module.finrank K V) / 2 * (S.v S.Ωinf).toReal : ℝ) : EReal)))
  have herr : C * Real.log (Module.finrank K V) +
      Real.log (Module.finrank K V) / 2 * (S.v S.Ωinf).toReal =
      (C + (S.v S.Ωinf).toReal / 2) * Real.log (Module.finrank K V) := by ring
  rw [add_assoc, ← EReal.coe_add, herr] at h
  exact h

/-- In rank one the produced correction is zero. -/
theorem maximalSlope_le_maximalLogarithmicMinimum_of_strongMinkowski_finrank_one
    (V : AdelicVectorBundle.{w} S) [hV : V.toNormFamily.IsUltrametric]
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    {C : ℝ} (hM : S.HasStrongMinkowskiPropertyAtLevel.{u, v, w} C)
    (hr : Module.finrank K V = 1) :
    V.maximalSlope ≤ V.maximalLogarithmicMinimum := by
  have h := V.maximalSlope_le_maximalLogarithmicMinimum_add_of_strongMinkowski
     hM (by omega)
  simpa only [hr, Nat.cast_one, Real.log_one, mul_zero, EReal.coe_zero, add_zero] using h

variable {E' : Type (max u w)} [AddCommGroup E'] [Module K E'] [FiniteDimensional K E']

/-- The actual Hermitian and general ordered lists agree, and the first
Hermitian ordered slope is the maximal slope. This retains the same level. -/
theorem maximalSlope_le_maximalLogarithmicMinimum_add_of_strongMinkowski_hermitian
    (V : AdelicVectorBundle.{max u w} S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian]
    {C : ℝ} (hM : S.HasStrongMinkowskiPropertyAtLevel.{u, v, max u w} C)
    (hr : 0 < Module.finrank K V) :
    V.maximalSlope ≤ V.maximalLogarithmicMinimum +
      (C * Real.log (Module.finrank K V) : ℝ) := by
  have h := V.generalHNOrderedSlope_le_logarithmicMinimum_add_log_rank
    (hV := hV.1) hM ⟨0, hr⟩
  rw [V.generalHNOrderedSlope_eq_hermitianHNOrderedSlope,
    V.hermitianHNOrderedSlope_zero_eq_maximalSlope hr] at h
  exact h

end AdelicVectorBundle

namespace AdelicStructure
variable [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized] {C : ℝ}

/-- Source Remark 4.3.81 with the actual general first-slope correction,
quantified over all original admissible positive-rank bundles. -/
theorem HasStrongMinkowskiPropertyAtLevel.minkowski_add_half_archimedeanMass
    (hM : S.HasStrongMinkowskiPropertyAtLevel.{u, v, w} C) :
    S.HasMinkowskiPropertyAtLevel.{u, v, w} (C + (S.v S.Ωinf).toReal / 2) := by
  refine ⟨add_nonneg hM.1 (div_nonneg ENNReal.toReal_nonneg (by norm_num)),
    fun V hr hV => ?_⟩
  exact (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mpr
      (V.maximalSlope_le_maximalLogarithmicMinimum_add_of_strongMinkowski (hV := hV) hM hr)

/-- Zero Archimedean measure removes the correction, even if the locus
contains points of measure zero. -/
theorem HasStrongMinkowskiPropertyAtLevel.minkowski_of_archimedeanMass_eq_zero
    (hM : S.HasStrongMinkowskiPropertyAtLevel.{u, v, w} C)
    (hzero : S.v S.Ωinf = 0) : S.HasMinkowskiPropertyAtLevel.{u, v, w} C := by
  simpa only [hzero, ENNReal.toReal_zero, zero_div, add_zero] using
    hM.minkowski_add_half_archimedeanMass

end AdelicStructure
end ArakelovGeometry
