/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.LogarithmicMinimaFinite

/-!
# Actual absolute minima are real and epsilon-approximated

The actual closure bundle supplies the rational basis and independent tuples.
Its finite upper endpoint is produced from original-base hypotheses, without
assuming additional regularity of the closure place space. Valid source indices
are positive and at most original rank; auxiliary endpoints remain unchanged.
-/

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
variable {K E : Type*} [Field K] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The actual closure basis excludes bottom for every index at most original
rank. Indexzero remains an explicitly auxiliary top-valued convention. -/
theorem absoluteLogarithmicMinimum_ne_bot (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    {i : ℕ} (hr : i ≤ Module.finrank K E) :
    V.absoluteLogarithmicMinimum hreg hN i ≠ ⊥ := by
  apply logarithmicMinimum_ne_bot (V.ordinaryScalarExtension (L := AlgebraicClosure K) hreg hN)
  simpa only [Module.finrank_baseChange] using hr

/-- The actual closure filtration has a whole-space lower endpoint without
any regularity assumption on the closure place space. -/
theorem exists_absoluteMinimaFiltration_eq_top (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ∃ a : ℝ, ∀ t ≤ a,
      (V.ordinaryScalarExtension (L := AlgebraicClosure K) hreg hN).minimaFiltration t = ⊤ :=
  (V.ordinaryScalarExtension (L := AlgebraicClosure K) hreg hN).exists_minimaFiltration_eq_top

variable [S.IsProper]

/-- The produced absolute-first-minimum bound excludes top at EVERY positive
natural index; valid source indices will additionally exclude bottom. -/
theorem absoluteLogarithmicMinimum_ne_top (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    {i : ℕ} (hi : 1 ≤ i) : V.absoluteLogarithmicMinimum hreg hN i ≠ ⊤ :=
  ((V.absoluteLogarithmicMinimum_antitone hreg hN hi).trans_lt
    (V.absoluteMaximalLogarithmicMinimum_lt_top hreg hN)).ne

/-- Every valid source index has a real minimum on the genuine actual closure
bundle, with both endpoint exclusions produced from original hypotheses. -/
theorem exists_absoluteLogarithmicMinimum_eq_coe (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    {i : ℕ} (hi : 1 ≤ i) (hr : i ≤ Module.finrank K E) :
    ∃ c : ℝ, V.absoluteLogarithmicMinimum hreg hN i = (c : EReal) :=
  ⟨(V.absoluteLogarithmicMinimum hreg hN i).toReal,
    (EReal.coe_toReal (V.absoluteLogarithmicMinimum_ne_top hreg hN hi)
      (V.absoluteLogarithmicMinimum_ne_bot hreg hN hr)).symm⟩

/-- Actual nonzero closure vectors form an independent epsilon-approximation
tuple for every valid absolute minimum, with no extended-base regularity premise. -/
theorem exists_linearIndependent_degree_ge_absoluteLogarithmicMinimum_sub
    (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    {i : ℕ} (hi : 1 ≤ i) (hr : i ≤ Module.finrank K E) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Fin i → {x : AlgebraicClosure K ⊗[K] E // x ≠ 0},
      LinearIndependent (AlgebraicClosure K) (fun j => (s j).val) ∧
      ∀ j, (V.absoluteLogarithmicMinimum hreg hN i).toReal - ε ≤
        (V.ordinaryScalarExtension (L := AlgebraicClosure K) hreg hN).vectorDegree (s j) := by
  let W := V.ordinaryScalarExtension (L := AlgebraicClosure K) hreg hN
  have hm := EReal.coe_toReal (V.absoluteLogarithmicMinimum_ne_top hreg hN hi)
    (V.absoluteLogarithmicMinimum_ne_bot hreg hN hr)
  have hlt : (((V.absoluteLogarithmicMinimum hreg hN i).toReal - ε : ℝ) : EReal) <
      W.logarithmicMinimum i := by
    change _ < V.absoluteLogarithmicMinimum hreg hN i
    rw [← hm]
    exact EReal.coe_lt_coe_iff.mpr (sub_lt_self _ hε)
  obtain ⟨s, hs, hd⟩ := W.exists_linearIndependent_degree_gt_of_lt_logarithmicMinimum i hlt
  exact ⟨s, hs, fun j => (hd j).le⟩

/-- Finite actual absolute first minimum separates the true closure filtration,
with the zero-rank branch controlled by genuine base-change rank preservation. -/
theorem exists_absoluteMinimaFiltration_eq_bot (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ∃ b : ℝ, ∀ t ≥ b,
      (V.ordinaryScalarExtension (L := AlgebraicClosure K) hreg hN).minimaFiltration t = ⊥ := by
  let W := V.ordinaryScalarExtension (L := AlgebraicClosure K) hreg hN
  by_cases hr : Module.finrank K E = 0
  · have hW : Module.finrank (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] E) = 0 := by
      simpa only [Module.finrank_baseChange] using hr
    exact ⟨0, fun t _ => W.minimaFiltration_eq_bot_of_finrank_eq_zero hW t⟩
  · obtain ⟨c, hc⟩ := V.exists_absoluteLogarithmicMinimum_eq_coe hreg hN le_rfl (by omega :
      1 ≤ Module.finrank K E)
    refine ⟨c + 1, fun t ht => (W.minimaFiltration_eq_bot_iff t).mpr ?_⟩
    change V.absoluteLogarithmicMinimum hreg hN 1 < (t : EReal)
    rw [hc]
    exact EReal.coe_lt_coe_iff.mpr (by linarith)

end ArakelovGeometry.AdelicVectorBundle
