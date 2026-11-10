/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Ordered
public import ArakelovGeometry.AdelicVectorBundle.Minkowski.Basic
import ArakelovGeometry.AdelicVectorBundle.Minima.FiltrationRank
import ArakelovGeometry.AdelicVectorBundle.Minima.SubspaceFiltration
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Actual ordered logarithmic-minimum bounds from the strong Minkowski property

The genuine HN restriction retains finite-place ultrametricity. Applying the
actual universal strong property to its produced positive rank, then comparing
its rank with the ambient rank, gives the actual shifted minima filtration
inclusion and the valid-index ordered converse. The finite-place admissibility
hypothesis omitted by the printed Proposition4.3.80 remains explicit here.
-/

@[expose] public section

noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
universe u v w
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [S.IsProper]

/-- Apply the actual universal strong property to the genuine HN restricted
bundle and compare its produced rank with the original rank. Finite-place
ultrametricity is required, as in the predicate, and the zero cut is allowed. -/
theorem coe_sub_log_rank_le_minimalLogarithmicMinimum_restrict_generalHNFiltration
    (V : AdelicVectorBundle S E) (hV : V.toNormFamily.IsUltrametric)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    {C : ℝ} (hM : S.HasStrongMinkowskiPropertyAtLevel.{u, v, w} hS hN C) (t : ℝ) :
    ((t - C * Real.log (Module.finrank K E) : ℝ) : EReal) ≤
      minimalLogarithmicMinimum
        (V.restrictOfMeasurableBase (V.generalHNFiltration hS hN t) hS) := by
  let U := V.generalHNFiltration hS hN t
  let R := V.restrictOfMeasurableBase U hS
  by_cases hU : U = ⊥
  · have hr : Module.finrank K U = 0 := by rw [hU, finrank_bot]
    rw [R.minimalLogarithmicMinimum_eq_top_of_finrank_eq_zero hr]
    exact le_top
  · have hr : 0 < Module.finrank K U := Nat.pos_of_ne_zero (fun hz =>
      hU (Submodule.finrank_eq_zero.mp hz))
    have hstrong := hM.2 U R hr (hV.restrict U)
    have hlog := Real.log_le_log (Nat.cast_pos.mpr hr : (0 : ℝ) < _)
      (Nat.cast_le.mpr U.finrank_le)
    have hc := mul_le_mul_of_nonneg_left hlog hM.1
    rw [EReal.coe_sub]
    exact (EReal.sub_le_sub (V.le_minimalSlope_restrict_generalHNFiltration hS hN t)
      (EReal.coe_le_coe hc)).trans hstrong

/-- Corrected source Proposition4.3.80's actual filtration shift. Its finite
place admissibility is visible, and the universal property produces the
restricted last-minimum bound rather than assuming target containment. -/
theorem generalHNFiltration_le_minimaFiltration_sub_log_rank
    (V : AdelicVectorBundle S E) (hV : V.toNormFamily.IsUltrametric)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    {C : ℝ} (hM : S.HasStrongMinkowskiPropertyAtLevel.{u, v, w} hS hN C) (t : ℝ) :
    V.generalHNFiltration hS hN t ≤
      V.minimaFiltration (t - C * Real.log (Module.finrank K E)) := by
  let U := V.generalHNFiltration hS hN t
  let R := V.restrictOfMeasurableBase U hS
  let a := t - C * Real.log (Module.finrank K E)
  have htop : R.minimaFiltration a = ⊤ := (R.minimaFiltration_eq_top_iff a).mpr
    (V.coe_sub_log_rank_le_minimalLogarithmicMinimum_restrict_generalHNFiltration hV hS hN hM t)
  have hm := V.minimaFiltration_restrict_map_le U hS a
  rw [htop, Submodule.map_subtype_top] at hm
  exact hm

/-- Corrected source Proposition4.3.80 on each valid source index `j.val+1`.
Actual HN rank-cut attainment and the produced filtration shift give the
converse bound, without assuming logarithmic-minimum attainment or finiteness. -/
theorem generalHNOrderedSlope_le_logarithmicMinimum_add_log_rank
    (V : AdelicVectorBundle S E) (hV : V.toNormFamily.IsUltrametric)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    {C : ℝ} (hM : S.HasStrongMinkowskiPropertyAtLevel.{u, v, w} hS hN C)
    (j : Fin (Module.finrank K E)) :
    (V.generalHNOrderedSlope hS hN j : EReal) ≤ V.logarithmicMinimum (j.val + 1) +
      (C * Real.log (Module.finrank K E) : ℝ) := by
  let t := V.generalHNOrderedSlope hS hN j
  have hr := (V.lt_finrank_generalHNFiltration_orderedSlope hS hN j).trans_le
    (Submodule.finrank_mono (V.generalHNFiltration_le_minimaFiltration_sub_log_rank hV hS hN hM t))
  have hm := (V.le_finrank_minimaFiltration_iff (j.val + 1)
    (t - C * Real.log (Module.finrank K E))).mp (Nat.succ_le_of_lt hr)
  rw [EReal.coe_sub] at hm
  exact (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mp hm

end ArakelovGeometry.AdelicVectorBundle
