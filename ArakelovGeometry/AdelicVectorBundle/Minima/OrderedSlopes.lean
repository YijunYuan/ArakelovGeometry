/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Ordered
public import ArakelovGeometry.AdelicVectorBundle.Minima.Basic
import ArakelovGeometry.AdelicVectorBundle.Minima.FiltrationRank
import ArakelovGeometry.AdelicVectorBundle.Minima.Slopes
import ArakelovGeometry.AdelicVectorBundle.Minima.SubspaceFiltration
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Actual logarithmic minima and actual general ordered slopes

The genuine restriction to an actual minima cut has last minimum at least
its cut. The actual last-minimum/minimal-slope inequality then supplies the
restricted minimal-slope bound defining the actual general HN filtration.
Actual filtration inclusion and rank cuts give source Proposition4.3.78,
without finite-value or attainment premises on the logarithmic minima.
-/

@[expose] public section

noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
universe u v w
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [S.IsProper]

/-- The actual ordinary restriction to a completed minima cut has minimal
slope at least its real cut, including the zero cut's infinite endpoint. -/
theorem coe_le_minimalSlope_restrict_minimaFiltration (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (t : ℝ) :
    (t : EReal) ≤ (V.restrictOfMeasurableBase (V.minimaFiltration t) hS).minimalSlope hS hN :=
  (V.coe_le_minimalLogarithmicMinimum_restrict_minimaFiltration hS t).trans
    (minimalLogarithmicMinimum_le_minimalSlope
      (V.restrictOfMeasurableBase (V.minimaFiltration t) hS) hS hN)

/-- Source Corollary4.3.78's filtration inclusion, from the produced actual
restricted minimal-slope bound and the actual general HN maximality. -/
theorem minimaFiltration_le_generalHNFiltration (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (t : ℝ) :
    V.minimaFiltration t ≤ V.generalHNFiltration hS hN t :=
  V.le_generalHNFiltration_of_le_minimalSlope_restrict hS hN (V.minimaFiltration t) t
    (V.coe_le_minimalSlope_restrict_minimaFiltration hS hN t)

/-- Source Corollary4.3.78. The zero-based ordered slot `j` corresponds to
the source minimum index `j.val + 1`, so only valid positive indices occur.
No attained or finite-value logarithmic minimum is assumed; rank zero has
no ordered slots. -/
theorem logarithmicMinimum_le_generalHNOrderedSlope (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (j : Fin (Module.finrank K E)) :
    V.logarithmicMinimum (j.val + 1) ≤ (V.generalHNOrderedSlope hS hN j : EReal) := by
  rw [V.logarithmicMinimum_eq_iSup_finrank_minimaFiltration (j.val + 1)]
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  have hr := ht.trans (Submodule.finrank_mono (V.minimaFiltration_le_generalHNFiltration hS hN t))
  exact EReal.coe_le_coe_iff.mpr
    ((V.le_generalHNOrderedSlope_iff_lt_filtration_finrank hS hN t j).mpr
      ((Nat.lt_succ_self j.val).trans_le hr))

end ArakelovGeometry.AdelicVectorBundle
