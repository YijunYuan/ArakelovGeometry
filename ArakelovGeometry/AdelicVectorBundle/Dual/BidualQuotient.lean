/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Bidual
public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic

import ArakelovGeometry.AdelicVectorBundle.Determinant.Bidual
import ArakelovGeometry.AdelicVectorBundle.Dual.Bidual
import ArakelovGeometry.AdelicVectorBundle.Dual.Restriction
import ArakelovGeometry.AdelicVectorBundle.Slope.Quotient
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Actual quotient norms commute with canonical bidualization

Equality of the completed quotient dual norms follows from the canonical
annihilator identification and triple duality. The actual bidual quotient is
ultrametric at finite places and reflexive at normalized infinite places.
Degree invariance then preserves every quotient mean and the true minimum.
-/

@[expose] public section

namespace ArakelovGeometry

noncomputable section

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace NormFamily

/-- Canonical evaluation and the genuine completed quotient norm commute
under the usual infinite-place normalization, without original ultrametricity. -/
theorem dual_dual_pullback_quotient (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized] (U : Submodule K E) :
    (ξ.quotient U).dual.dual.pullback (Module.Dual.eval K (E ⧸ U))
      (Module.eval_apply_injective K) =
      (ξ.dual.dual.pullback (Module.Dual.eval K E)
        (Module.eval_apply_injective K)).quotient U := by
  let β := ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)
  have hd : (β.quotient U).dual = (ξ.quotient U).dual := by
    rw [β.quotient_dual_annihilator, ξ.quotient_dual_annihilator]
    change (β.dual.restrict U.dualAnnihilator).pullback _ _ = _
    rw [ξ.dual_dual_pullback_dual_eq]
  have hu : (β.quotient U).IsUltrametricAtFinitePlaces :=
    (ξ.dual.dual_isUltrametricAtFinitePlaces.pullback _ _).quotient U
  rw [← hd]
  exact (β.quotient U).dual_dual_pullback_eq (hξ := hu)

end NormFamily

namespace AdelicVectorBundle

variable (V : AdelicVectorBundle S)
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]

include hN

/-- The actual adelic constructors commute because their completed norm
families agree, rather than through a supplied quotient-isometry certificate. -/
theorem quotient_bidualOfNormMeasurability (U : Submodule K V) :
    (V.bidualOfNormMeasurability).quotientOfNormMeasurability U =
      (V.quotientOfNormMeasurability U).bidualOfNormMeasurability := by
  apply AdelicVectorBundle.ext
    (hξ := (V.bidualOfNormMeasurability.quotientOfNormMeasurability U).toIsAdelic)
    (hη := (V.quotientOfNormMeasurability U).bidualOfNormMeasurability.toIsAdelic)
  exact (V.toNormFamily.dual_dual_pullback_quotient U).symm

/-- Bidualization preserves the actual infimum of nonzero quotient means,
including the infinite minimum convention of the zero bundle. -/
theorem minimalSlope_bidualOfNormMeasurability [S.IsProper] :
    (V.bidualOfNormMeasurability).minimalSlope = V.minimalSlope := by
  rw [(V.bidualOfNormMeasurability).minimalSlope_eq_iInf_slope_quotient,
    V.minimalSlope_eq_iInf_slope_quotient]
  apply iInf_congr
  intro U
  rw [V.quotient_bidualOfNormMeasurability U.val]
  simp only [slope, degree_bidualOfNormMeasurability]

end AdelicVectorBundle

end

end ArakelovGeometry
