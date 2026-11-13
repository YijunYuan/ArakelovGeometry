/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Measurability.Density.Basic
public import ArakelovGeometry.AdelicVectorBundle.Minima.Basic

import ArakelovGeometry.AdelicVectorBundle.Minima.Basis
import ArakelovGeometry.AdelicVectorBundle.Minima.FiltrationRank
import ArakelovGeometry.AdelicVectorBundle.Minima.Finite
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual bases of minima cuts and their finite jump set

Every completed cut admits a true high-degree rational basis at each strictly
relaxed threshold. The actual valid real minima form a finite set controlling
all jumps, with original properness, normalization and regularity hypotheses.
-/

@[expose] public section

noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
universe u w
variable {K : Type u} [Field K] {S : AdelicStructure K} {E : Type w}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Every actual completed cut has an actual subtype basis with high ambient
vector degrees at each strictly relaxed threshold. The empty basis is allowed. -/
theorem exists_basis_minimaFiltration_degree_ge (V : AdelicVectorBundle S)
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : Module.Basis (Fin (Module.finrank K (V.minimaFiltration t))) K
        (V.minimaFiltration t),
      ∀ j, t - ε ≤ V.vectorDegree
        ⟨(b j : V), fun h => b.ne_zero j (Subtype.ext h)⟩ := by
  classical
  obtain ⟨δ₀, hδ₀, hΦ⟩ := V.exists_minimaFiltration_eq_degreeThresholdSpan t
  let δ := min δ₀ ε
  have hδ : 0 < δ := lt_min hδ₀ hε
  have hEq : V.minimaFiltration t = V.degreeThresholdSpan (t - δ) := by
    apply le_antisymm (V.minimaFiltration_le_degreeThresholdSpan t hδ)
    rw [hΦ]
    exact V.degreeThresholdSpan_antitone (sub_le_sub_left (min_le_left δ₀ ε) t)
  have hr : Module.finrank K (V.minimaFiltration t) ≤
      Module.finrank K (V.degreeThresholdSpan (t - δ)) := by rw [hEq]
  obtain ⟨s, hli, hs⟩ := (V.le_finrank_degreeThresholdSpan_iff
    (Module.finrank K (V.minimaFiltration t)) (t - δ)).mp hr
  let g : Fin (Module.finrank K (V.minimaFiltration t)) → V.minimaFiltration t :=
    fun j => ⟨(s j).val, by rw [hEq]; exact V.mem_degreeThresholdSpan (s j) (hs j)⟩
  have hlig : LinearIndependent K g :=
    LinearIndependent.of_comp (V.minimaFiltration t).subtype hli
  let b := basisOfLinearIndependentOfCardEqFinrank' g hlig (by simp)
  have hb : ⇑b = g := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  refine ⟨b, fun j => ?_⟩
  simp only [hb]
  change t - ε ≤ V.vectorDegree (s j)
  exact (sub_le_sub_left (min_le_right δ₀ ε) t).trans (hs j)

/-- Agreement of all valid minimum profiles gives equality of the actual
completed filtration spaces, including rank zero. -/
theorem minimaFiltration_eq_of_minimum_profile (V : AdelicVectorBundle S)
    {a b : ℝ}
    (h : ∀ i : ℕ, 1 ≤ i → i ≤ Module.finrank K V →
      ((a : EReal) ≤ V.logarithmicMinimum i ↔ (b : EReal) ≤ V.logarithmicMinimum i)) :
    V.minimaFiltration a = V.minimaFiltration b := by
  classical
  have hr : Module.finrank K (V.minimaFiltration a) =
      Module.finrank K (V.minimaFiltration b) := by
    rw [V.finrank_minimaFiltration_eq_card a, V.finrank_minimaFiltration_eq_card b]
    congr 1
    apply Finset.filter_congr
    intro i hi
    exact h i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
  rcases le_total a b with hab | hba
  · exact (Submodule.eq_of_le_of_finrank_le (V.minimaFiltration_antitone hab) hr.le).symm
  · exact Submodule.eq_of_le_of_finrank_le (V.minimaFiltration_antitone hba) hr.ge

/-- The finite image of valid minimum indices under `EReal.toReal`.
Under the original finiteness hypotheses these are exactly the real minima;
the auxiliary index-zero and above-rank endpoint values are excluded. -/
def logarithmicMinimaJumpSet (V : AdelicVectorBundle S) : Finset ℝ := by
  classical
  exact (Finset.Icc 1 (Module.finrank K V)).image (fun i => (V.logarithmicMinimum i).toReal)

variable [S.IsProper]

/-- With produced original finite minima, membership in the finite jump set
is exactly equality to an actual valid source minimum. -/
theorem mem_logarithmicMinimaJumpSet_iff (V : AdelicVectorBundle S)
    [hreg : S.HasRegularBase]
    [hN : S.IsArchimedeanNormalized] (c : ℝ) :
    c ∈ V.logarithmicMinimaJumpSet ↔
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ Module.finrank K V ∧ V.logarithmicMinimum i = (c : EReal) := by
  classical
  rw [logarithmicMinimaJumpSet, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, hc⟩
    obtain ⟨hi, hr⟩ := Finset.mem_Icc.mp hi
    have hm := EReal.coe_toReal (V.logarithmicMinimum_ne_top hi)
      (V.logarithmicMinimum_ne_bot hr)
    exact ⟨i, hi, hr, hm.symm.trans (congrArg (fun x : ℝ => (x : EReal)) hc)⟩
  · rintro ⟨i, hi, hr, hc⟩
    exact ⟨i, Finset.mem_Icc.mpr ⟨hi, hr⟩, by rw [hc, EReal.toReal_coe]⟩

/-- The actual filtration is constant across an interval containing none of
the produced valid real minima. The controlling interval is `[a,b)`. -/
theorem minimaFiltration_eq_of_disjoint_jump_interval (V : AdelicVectorBundle S)
    [hreg : S.HasRegularBase]
    [hN : S.IsArchimedeanNormalized]
    {a b : ℝ} (hab : a ≤ b)
    (hJ : Disjoint (V.logarithmicMinimaJumpSet : Set ℝ) (Set.Ico a b)) :
    V.minimaFiltration a = V.minimaFiltration b := by
  apply V.minimaFiltration_eq_of_minimum_profile
  intro i hi hr
  obtain ⟨c, hc⟩ := V.exists_logarithmicMinimum_eq_coe hi hr
  rw [hc]
  simp only [EReal.coe_le_coe_iff]
  constructor
  · intro hac
    by_contra hbc
    have hcJ := (V.mem_logarithmicMinimaJumpSet_iff c).mpr ⟨i, hi, hr, hc⟩
    exact Set.disjoint_left.mp hJ hcJ ⟨hac, lt_of_not_ge hbc⟩
  · exact hab.trans

end ArakelovGeometry.AdelicVectorBundle
