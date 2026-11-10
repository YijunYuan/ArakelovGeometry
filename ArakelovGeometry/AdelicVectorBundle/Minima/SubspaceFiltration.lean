/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Countable
public import ArakelovGeometry.AdelicVectorBundle.Minima.Basic
import ArakelovGeometry.AdelicVectorBundle.Minima.Basis
import ArakelovGeometry.AdelicVectorBundle.Minima.FiltrationRank
import ArakelovGeometry.AdelicVectorBundle.Minima.Restriction
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# The actual ordinary minima filtration through genuine restricted subspaces

Restriction preserves actual threshold vectors and maps completed minima
filtrations into the ambient filtration. The actual restriction to a filtration
space has last minimum at least its cut. Consequently the source 4.3.70 sum and
intersection formula holds with the canonical ordinary restricted bundles under
the explicit measurable-base hypothesis, with a rank-zero extension.
No finite-value minimum or attainment of a supremum is assumed.
-/

@[expose] public section

noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle

universe u v w
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Actual restricted threshold spans map into the ambient actual threshold span. -/
theorem degreeThresholdSpan_restrict_map_le (V : AdelicVectorBundle S E)
    (U : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) (t : ℝ) :
    ((V.restrictOfMeasurableBase U hS).degreeThresholdSpan t).map U.subtype ≤
      V.degreeThresholdSpan t := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro x ⟨hx, ht⟩
  change (x : E) ∈ V.degreeThresholdSpan t
  have hne : (x : E) ≠ 0 := by
    intro h
    exact hx (Subtype.ext h)
  apply V.mem_degreeThresholdSpan ⟨x.val, hne⟩
  rw [← V.vectorDegree_restrictOfMeasurableBase U hS ⟨x, hx⟩]
  exact ht

/-- Actual restricted completed minima filtrations map into the ambient filtration. -/
theorem minimaFiltration_restrict_map_le (V : AdelicVectorBundle S E)
    (U : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) (t : ℝ) :
    ((V.restrictOfMeasurableBase U hS).minimaFiltration t).map U.subtype ≤
      V.minimaFiltration t := by
  apply le_iInf
  intro ε
  apply le_iInf
  intro hε
  exact (Submodule.map_mono
    ((V.restrictOfMeasurableBase U hS).minimaFiltration_le_degreeThresholdSpan t hε)).trans
      (V.degreeThresholdSpan_restrict_map_le U hS (t - ε))

private theorem ordinaryMinimaFiltrationThresholdRefinement (V : AdelicVectorBundle S E)
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ V.minimaFiltration t = V.degreeThresholdSpan (t - δ) := by
  obtain ⟨δ₀, hδ₀, hΦ⟩ := V.exists_minimaFiltration_eq_degreeThresholdSpan t
  have hδ : 0 < min δ₀ ε := lt_min hδ₀ hε
  refine ⟨min δ₀ ε, hδ, min_le_right _ _,
    le_antisymm (V.minimaFiltration_le_degreeThresholdSpan t hδ) ?_⟩
  exact (V.degreeThresholdSpan_antitone (sub_le_sub_left (min_le_left δ₀ ε) t)).trans hΦ.symm.le

/-- The genuine restriction to an actual completed minima filtration space has
last minimum at least the cut, including the zero-space last-minimum convention. -/
theorem coe_le_minimalLogarithmicMinimum_restrict_minimaFiltration
    (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) (t : ℝ) :
    (t : EReal) ≤
      (V.restrictOfMeasurableBase (V.minimaFiltration t) hS).minimalLogarithmicMinimum := by
  classical
  let U := V.minimaFiltration t
  let R := V.restrictOfMeasurableBase U hS
  apply (R.le_finrank_minimaFiltration_iff (Module.finrank K U) t).mp
  apply (R.le_finrank_minimaFiltration_iff_forall_exists_linearIndependent
    (Module.finrank K U) t).mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε, hΦ⟩ := ordinaryMinimaFiltrationThresholdRefinement V t hε
  have hr : Module.finrank K U ≤ Module.finrank K (V.degreeThresholdSpan (t - δ)) :=
    (congrArg (fun F : Submodule K E => Module.finrank K F) hΦ).le
  obtain ⟨s, hli, hs⟩ := (V.le_finrank_degreeThresholdSpan_iff
    (Module.finrank K U) (t - δ)).mp hr
  let g : Fin (Module.finrank K U) → U := fun j => ⟨(s j).val, by
    change (s j).val ∈ V.minimaFiltration t
    rw [hΦ]
    exact V.mem_degreeThresholdSpan (s j) (hs j)⟩
  have hlig : LinearIndependent K g := LinearIndependent.of_comp U.subtype hli
  let f : Fin (Module.finrank K U) → {x : U // x ≠ 0} := fun j => ⟨g j, by
    intro h
    exact (s j).property (congrArg Subtype.val h)⟩
  refine ⟨f, hlig, ?_⟩
  intro j
  rw [V.vectorDegree_restrictOfMeasurableBase U hS]
  exact (sub_le_sub_left hδε t).trans (hs j)

/-- The actual completed cut is the sum of genuine nonzero subspaces whose
ordinary restricted last minimum is at least the cut. -/
theorem minimaFiltration_eq_iSup_restrict_minimalLogarithmicMinimum
    (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) (t : ℝ) :
    V.minimaFiltration t =
      ⨆ (U : Submodule K E) (_ : U ≠ ⊥)
        (_ : (t : EReal) ≤ (V.restrictOfMeasurableBase U hS).minimalLogarithmicMinimum), U := by
  classical
  apply le_antisymm
  · by_cases hΦ : V.minimaFiltration t = ⊥
    · rw [hΦ]
      exact bot_le
    · exact le_iSup_of_le (V.minimaFiltration t) (le_iSup_of_le hΦ (le_iSup_of_le
        (V.coe_le_minimalLogarithmicMinimum_restrict_minimaFiltration hS t) le_rfl))
  · apply iSup_le
    intro U
    apply iSup_le
    intro _
    apply iSup_le
    intro hmin
    have htop := ((V.restrictOfMeasurableBase U hS).minimaFiltration_eq_top_iff t).mpr hmin
    have hm := V.minimaFiltration_restrict_map_le U hS t
    rw [htop, Submodule.map_subtype_top] at hm
    exact hm

/-- Source Proposition 4.3.70, equation (4.82), with actual ordinary restriction
bundles under the explicit measurable-base hypothesis, including rank zero. -/
theorem minimaFiltration_eq_iInf_iSup_restrict_minimalLogarithmicMinimum
    (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) (t : ℝ) :
    V.minimaFiltration t =
      ⨅ (ε : ℝ) (_ : 0 < ε),
        ⨆ (U : Submodule K E) (_ : U ≠ ⊥)
          (_ : ((t - ε : ℝ) : EReal) ≤
            (V.restrictOfMeasurableBase U hS).minimalLogarithmicMinimum), U := by
  simp_rw [← V.minimaFiltration_eq_iSup_restrict_minimalLogarithmicMinimum hS]
  apply le_antisymm
  · apply le_iInf
    intro ε
    apply le_iInf
    intro hε
    exact V.minimaFiltration_antitone (sub_le_self t hε.le)
  · rw [V.minimaFiltration_eq_iInf_lt t]
    apply le_iInf
    intro u
    apply le_iInf
    intro hu
    have hε : 0 < t - u := sub_pos.mpr hu
    have h : (⨅ (ε : ℝ) (_ : 0 < ε), V.minimaFiltration (t - ε)) ≤
        V.minimaFiltration (t - (t - u)) :=
      iInf_le_of_le (t - u) (iInf_le_of_le hε le_rfl)
    convert h using 1
    congr 1
    ring

end ArakelovGeometry.AdelicVectorBundle
