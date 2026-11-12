/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Basic
public import ArakelovGeometry.AdelicVectorBundle.Degree.Vector

import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Ordinary logarithmic minima of actual adelic vector bundles

Definition 4.3.69 uses the span of nonzero rational vectors above a vector-degree
threshold. Minima are initially extended real suprema; finiteness and comparison
with slopes are separate results. The source indices satisfy `1 ≤ i ≤ finrank K E`.
The natural-index extension here also permits index zero, whose value is `⊤`,
and indices beyond the rank, whose value is `⊥`. This gives the source rank-zero
conventions for the first and last minima without discarding the empty space.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section
universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The canonical actual vector degree, using the bundle's proved analytic fields. -/
abbrev vectorDegree (V : AdelicVectorBundle S E) (s : {x : E // x ≠ 0}) : ℝ :=
  V.toNormFamily.vectorDegree s

/-- The span of actual nonzero rational vectors of degree at least the threshold. -/
def degreeThresholdSpan (V : AdelicVectorBundle S E) (t : ℝ) : Submodule K E :=
  Submodule.span K {x | ∃ hx : x ≠ 0, t ≤ V.vectorDegree ⟨x, hx⟩}

/-- Ordinary logarithmic minima. Source indices are `1 ≤ i ≤ finrank K E`;
index zero and indices above rank give the explicit extended endpoint conventions. -/
def logarithmicMinimum (V : AdelicVectorBundle S E) (i : ℕ) : EReal :=
  ⨆ (t : ℝ) (_ : i ≤ Module.finrank K (V.degreeThresholdSpan t)), (t : EReal)

/-- The first ordinary logarithmic minimum, equal to `⊥` in rank zero. -/
def maximalLogarithmicMinimum (V : AdelicVectorBundle S E) : EReal :=
  V.logarithmicMinimum 1

/-- The last ordinary logarithmic minimum, equal to `⊤` in rank zero. -/
def minimalLogarithmicMinimum (V : AdelicVectorBundle S E) : EReal :=
  V.logarithmicMinimum (Module.finrank K E)

/-- The source's completed decreasing minima filtration. -/
def minimaFiltration (V : AdelicVectorBundle S E) (t : ℝ) : Submodule K E :=
  ⨅ (ε : ℝ) (_ : 0 < ε), V.degreeThresholdSpan (t - ε)

/-- Every actual high-degree generator belongs to its threshold span. -/
theorem mem_degreeThresholdSpan (V : AdelicVectorBundle S E) (s : {x : E // x ≠ 0})
    {t : ℝ} (hs : t ≤ V.vectorDegree s) : s.val ∈ V.degreeThresholdSpan t :=
  Submodule.subset_span ⟨s.property, hs⟩

/-- Increasing a degree threshold decreases the actual generated subspace. -/
theorem degreeThresholdSpan_antitone (V : AdelicVectorBundle S E) :
    Antitone V.degreeThresholdSpan := by
  intro a b hab
  apply Submodule.span_mono
  rintro x ⟨hx, hxb⟩
  exact ⟨hx, hab.trans hxb⟩

/-- Every admissible real threshold is bounded by its extended minimum. -/
theorem coe_le_logarithmicMinimum_of_finrank_le (V : AdelicVectorBundle S E)
    {i : ℕ} {t : ℝ} (ht : i ≤ Module.finrank K (V.degreeThresholdSpan t)) :
    (t : EReal) ≤ V.logarithmicMinimum i :=
  le_iSup_of_le t (le_iSup_of_le ht le_rfl)

/-- Ordinary logarithmic minima are nonincreasing with their natural index. -/
theorem logarithmicMinimum_antitone (V : AdelicVectorBundle S E) :
    Antitone V.logarithmicMinimum := by
  intro i j hij
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  exact V.coe_le_logarithmicMinimum_of_finrank_le (hij.trans ht)

/-- Index zero admits every real threshold; its extended minimum is `⊤`. -/
theorem logarithmicMinimum_zero (V : AdelicVectorBundle S E) :
    V.logarithmicMinimum 0 = ⊤ := by
  apply top_unique
  apply EReal.ge_of_forall_gt_iff_ge.mp
  intro t _
  exact V.coe_le_logarithmicMinimum_of_finrank_le (Nat.zero_le _)

/-- Indices above the actual rank have no admissible thresholds. -/
theorem logarithmicMinimum_eq_bot_of_finrank_lt (V : AdelicVectorBundle S E)
    {i : ℕ} (hi : Module.finrank K E < i) : V.logarithmicMinimum i = ⊥ := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  exact False.elim ((not_le_of_gt ((Submodule.finrank_le _).trans_lt hi)) ht)

/-- Every threshold span is contained in the source's completed minima filtration. -/
theorem degreeThresholdSpan_le_minimaFiltration (V : AdelicVectorBundle S E) (t : ℝ) :
    V.degreeThresholdSpan t ≤ V.minimaFiltration t := by
  apply le_iInf
  intro ε
  apply le_iInf
  intro hε
  exact V.degreeThresholdSpan_antitone (sub_le_self _ hε.le)

/-- The completed filtration is contained in every strictly relaxed threshold span. -/
theorem minimaFiltration_le_degreeThresholdSpan (V : AdelicVectorBundle S E) (t : ℝ)
    {ε : ℝ} (hε : 0 < ε) : V.minimaFiltration t ≤ V.degreeThresholdSpan (t - ε) :=
  iInf_le_of_le ε (iInf_le_of_le hε le_rfl)

/-- An actual high-degree nonzero vector belongs to the completed minima filtration. -/
theorem mem_minimaFiltration_of_degree_ge (V : AdelicVectorBundle S E)
    (s : {x : E // x ≠ 0}) {t : ℝ} (hs : t ≤ V.vectorDegree s) :
    s.val ∈ V.minimaFiltration t :=
  V.degreeThresholdSpan_le_minimaFiltration t (V.mem_degreeThresholdSpan s hs)

/-- The whole rational line of an actual high-degree vector lies in the minima filtration. -/
theorem span_singleton_le_minimaFiltration (V : AdelicVectorBundle S E)
    (s : {x : E // x ≠ 0}) {t : ℝ} (hs : t ≤ V.vectorDegree s) :
    Submodule.span K {s.val} ≤ V.minimaFiltration t :=
  (Submodule.span_singleton_le_iff_mem _ _).mpr (V.mem_minimaFiltration_of_degree_ge s hs)

/-- The source minima filtration decreases with its real parameter. -/
theorem minimaFiltration_antitone (V : AdelicVectorBundle S E) :
    Antitone V.minimaFiltration := by
  intro a b hab
  apply le_iInf
  intro ε
  apply le_iInf
  intro hε
  exact (V.minimaFiltration_le_degreeThresholdSpan b hε).trans
    (V.degreeThresholdSpan_antitone (sub_le_sub_right hab ε))

/-- The completed minima filtration is left continuous, without a finiteness premise. -/
theorem minimaFiltration_eq_iInf_lt (V : AdelicVectorBundle S E) (t : ℝ) :
    V.minimaFiltration t = ⨅ (u : ℝ) (_ : u < t), V.minimaFiltration u := by
  apply le_antisymm
  · exact le_iInf (fun u => le_iInf (fun hu => V.minimaFiltration_antitone hu.le))
  · apply le_iInf
    intro ε
    apply le_iInf
    intro hε
    have hhalf : 0 < ε / 2 := half_pos hε
    have hu : t - ε / 2 < t := sub_lt_self _ hhalf
    have hstep : (⨅ (u : ℝ) (_ : u < t), V.minimaFiltration u) ≤
        V.minimaFiltration (t - ε / 2) :=
      iInf_le_of_le (t - ε / 2) (iInf_le_of_le hu le_rfl)
    have h := hstep.trans
      (V.minimaFiltration_le_degreeThresholdSpan (t - ε / 2) hhalf)
    convert h using 1
    congr 1
    ring

/-- A rank-zero bundle has no nonzero threshold generators. -/
theorem degreeThresholdSpan_eq_bot_of_finrank_eq_zero (V : AdelicVectorBundle S E)
    (hr : Module.finrank K E = 0) (t : ℝ) : V.degreeThresholdSpan t = ⊥ := by
  have hz : ∀ x : E, x = 0 := finrank_zero_iff_forall_zero.mp hr
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro x ⟨hx, _⟩
  exact False.elim (hx (hz x))

/-- Every ordinary minima filtration space is zero in rank zero. -/
theorem minimaFiltration_eq_bot_of_finrank_eq_zero (V : AdelicVectorBundle S E)
    (hr : Module.finrank K E = 0) (t : ℝ) : V.minimaFiltration t = ⊥ := by
  apply le_antisymm _ bot_le
  exact (V.minimaFiltration_le_degreeThresholdSpan t (by norm_num : (0 : ℝ) < 1)).trans
    (V.degreeThresholdSpan_eq_bot_of_finrank_eq_zero hr (t - 1)).le

/-- The first minimum has the source rank-zero convention `-∞`. -/
theorem maximalLogarithmicMinimum_eq_bot_of_finrank_eq_zero (V : AdelicVectorBundle S E)
    (hr : Module.finrank K E = 0) : V.maximalLogarithmicMinimum = ⊥ :=
  V.logarithmicMinimum_eq_bot_of_finrank_lt (by rw [hr]; exact Nat.zero_lt_one)

/-- The last minimum has the source rank-zero convention `+∞`. -/
theorem minimalLogarithmicMinimum_eq_top_of_finrank_eq_zero (V : AdelicVectorBundle S E)
    (hr : Module.finrank K E = 0) : V.minimalLogarithmicMinimum = ⊤ := by
  rw [minimalLogarithmicMinimum, hr, V.logarithmicMinimum_zero]

end
end ArakelovGeometry.AdelicVectorBundle
