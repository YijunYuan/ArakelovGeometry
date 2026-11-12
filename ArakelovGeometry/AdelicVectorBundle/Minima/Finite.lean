/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Minima.Absolute.Basic

import ArakelovGeometry.AdelicVectorBundle.Minima.Absolute.FirstSlope
import ArakelovGeometry.AdelicVectorBundle.Minima.Basis
import ArakelovGeometry.AdelicVectorBundle.Minima.FiltrationRank
import ArakelovGeometry.AdelicVectorBundle.Minima.PositiveAtoms
import Mathlib.CategoryTheory.Category.Init

/-!
# Lower endpoints and approximation of actual ordinary logarithmic minima

A finite actual rational basis supplies a real lower bound for every valid
minimum without properness or slope assumptions. Strict thresholds below the
extended minimum supply independent high-degree tuples, without attainment.
-/

@[expose] public section

noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
variable {K E : Type*} [Field K] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- A finite actual rational basis supplies one real threshold spanning the
entire bundle, including its empty basis in rank zero. -/
theorem exists_degreeThresholdSpan_eq_top (V : AdelicVectorBundle S E) :
    ∃ t : ℝ, V.degreeThresholdSpan t = ⊤ := by
  let b := Module.finBasis K E
  let d : Fin (Module.finrank K E) → ℝ := fun j => V.vectorDegree ⟨b j, b.ne_zero j⟩
  obtain ⟨t, ht⟩ := Finite.bddBelow_range d
  refine ⟨t, top_unique ?_⟩
  rw [← b.span_eq]
  apply Submodule.span_le.mpr
  rintro x ⟨j, rfl⟩
  exact V.mem_degreeThresholdSpan ⟨b j, b.ne_zero j⟩ (ht (Set.mem_range_self j))

/-- Every index at most rank has a real admissible threshold, hence cannot
have bottom minimum. Index zero is an explicitly auxiliary case. -/
theorem logarithmicMinimum_ne_bot (V : AdelicVectorBundle S E)
    {i : ℕ} (hi : i ≤ Module.finrank K E) : V.logarithmicMinimum i ≠ ⊥ := by
  obtain ⟨t, ht⟩ := V.exists_degreeThresholdSpan_eq_top
  have h : (t : EReal) ≤ V.logarithmicMinimum i :=
    V.coe_le_logarithmicMinimum_of_finrank_le (by rw [ht, finrank_top]; exact hi)
  exact ((EReal.bot_lt_coe t).trans_le h).ne'

/-- Every strict threshold below the supremum is surpassed by an actual
independent nonzero rational tuple; the supremum need not be attained. -/
theorem exists_linearIndependent_degree_gt_of_lt_logarithmicMinimum
    (V : AdelicVectorBundle S E) (i : ℕ) {t : ℝ}
    (ht : (t : EReal) < V.logarithmicMinimum i) :
    ∃ s : Fin i → {x : E // x ≠ 0}, LinearIndependent K (fun j => (s j).val) ∧
      ∀ j, t < V.vectorDegree (s j) := by
  rw [logarithmicMinimum, lt_iSup_iff] at ht
  obtain ⟨u, hu⟩ := ht
  obtain ⟨hr, hu⟩ := lt_iSup_iff.mp hu
  obtain ⟨s, hs, hd⟩ := (V.le_finrank_degreeThresholdSpan_iff i u).mp hr
  exact ⟨s, hs, fun j => (EReal.coe_lt_coe_iff.mp hu).trans_le (hd j)⟩

/-- Low enough actual minima filtration cuts are the whole space, with no
properness or regularity alternative needed for this lower-end conclusion. -/
theorem exists_minimaFiltration_eq_top (V : AdelicVectorBundle S E) :
    ∃ t : ℝ, ∀ u ≤ t, V.minimaFiltration u = ⊤ := by
  obtain ⟨t, ht⟩ := V.exists_degreeThresholdSpan_eq_top
  refine ⟨t, fun u hu => top_unique ?_⟩
  rw [← ht]
  exact (V.degreeThresholdSpan_antitone hu).trans (V.degreeThresholdSpan_le_minimaFiltration u)

variable [S.IsProper]

/-- Actual first-minimum bounds and produced finite native slope suprema
exclude positive infinity on each of the original regularity alternatives. -/
theorem absoluteMaximalLogarithmicMinimum_lt_top (V : AdelicVectorBundle S E)
    [hreg : S.HasRegularBase]
    [hN : S.IsArchimedeanNormalized] :
    V.absoluteMaximalLogarithmicMinimum < ⊤ := by
  rcases hreg.condition with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
  · exact (V.absoluteMaximalLogarithmicMinimum_le_absoluteMaximalSlope (hcount := h)).trans_lt
      (V.absoluteMaximalSlope_lt_top (hcount := h))
  · let := hc
    let := hd
    exact (V.absoluteMaximalLogarithmicMinimum_le_absoluteMaximalSlopeOfCountableDiscreteBase
).trans_lt (V.absoluteMaximalSlopeOfCountableDiscreteBase_lt_top)
  · let := hm
    exact (V.absoluteMaximalLogarithmicMinimum_le_absoluteMaximalSlopeOfPositiveAtoms
      (hreg := ⟨(Or.inr (Or.inr ⟨hm, hp, hf⟩))⟩) (hpos := ⟨hp⟩) (hS := ⟨hf⟩)).trans_lt
      (V.toNormFamily.absoluteMaximalSlopeOfPositiveAtoms_lt_top (hpos := ⟨hp⟩) (hS := ⟨hf⟩))

/-- Every positive ordinary index excludes positive infinity, using the
actual original-to-absolute comparison on all three regularity branches. -/
theorem logarithmicMinimum_ne_top (V : AdelicVectorBundle S E)
    [hreg : S.HasRegularBase]
    [hN : S.IsArchimedeanNormalized]
    {i : ℕ} (hi : 1 ≤ i) : V.logarithmicMinimum i ≠ ⊤ :=
  ((V.logarithmicMinimum_antitone hi).trans
    (V.maximalLogarithmicMinimum_le_absoluteMaximalLogarithmicMinimum)).trans_lt
      (V.absoluteMaximalLogarithmicMinimum_lt_top) |>.ne

/-- Every valid source index has a produced real ordinary logarithmic minimum. -/
theorem exists_logarithmicMinimum_eq_coe (V : AdelicVectorBundle S E)
    [hreg : S.HasRegularBase]
    [hN : S.IsArchimedeanNormalized]
    {i : ℕ} (hi : 1 ≤ i) (hr : i ≤ Module.finrank K E) :
    ∃ c : ℝ, V.logarithmicMinimum i = (c : EReal) :=
  ⟨(V.logarithmicMinimum i).toReal,
    (EReal.coe_toReal (V.logarithmicMinimum_ne_top hi)
      (V.logarithmicMinimum_ne_bot hr)).symm⟩

/-- A real epsilon below the actual valid minimum admits an independent
nonzero tuple. The real value is canonical and its finiteness is produced. -/
theorem exists_linearIndependent_degree_ge_logarithmicMinimum_sub
    (V : AdelicVectorBundle S E)
    [hreg : S.HasRegularBase]
    [hN : S.IsArchimedeanNormalized]
    {i : ℕ} (hi : 1 ≤ i) (hr : i ≤ Module.finrank K E) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Fin i → {x : E // x ≠ 0}, LinearIndependent K (fun j => (s j).val) ∧
      ∀ j, (V.logarithmicMinimum i).toReal - ε ≤ V.vectorDegree (s j) := by
  have hm := EReal.coe_toReal (V.logarithmicMinimum_ne_top hi)
    (V.logarithmicMinimum_ne_bot hr)
  have hlt : (((V.logarithmicMinimum i).toReal - ε : ℝ) : EReal) <
      V.logarithmicMinimum i := by
    rw [← hm]
    exact EReal.coe_lt_coe_iff.mpr (sub_lt_self _ hε)
  obtain ⟨s, hs, hd⟩ := V.exists_linearIndependent_degree_gt_of_lt_logarithmicMinimum i hlt
  exact ⟨s, hs, fun j => (hd j).le⟩

/-- Produced finite first minimum separates all sufficiently high actual
filtration cuts; rank zero uses its genuine zero-filtration convention. -/
theorem exists_minimaFiltration_eq_bot (V : AdelicVectorBundle S E)
    [hreg : S.HasRegularBase]
    [hN : S.IsArchimedeanNormalized] :
    ∃ t : ℝ, ∀ u ≥ t, V.minimaFiltration u = ⊥ := by
  by_cases hr : Module.finrank K E = 0
  · exact ⟨0, fun u _ => V.minimaFiltration_eq_bot_of_finrank_eq_zero hr u⟩
  · obtain ⟨c, hc⟩ := V.exists_logarithmicMinimum_eq_coe le_rfl (by omega :
      1 ≤ Module.finrank K E)
    refine ⟨c + 1, fun u hu => (V.minimaFiltration_eq_bot_iff u).mpr ?_⟩
    rw [hc]
    exact EReal.coe_lt_coe_iff.mpr (by linarith)

end ArakelovGeometry.AdelicVectorBundle
