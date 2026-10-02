---
author: sync
content_type: definition
created: '2026-10-02T11:55:12'
decl: MeasureTheory.sequentialSpanMeasurableSpace
file: ArakelovGeometry/ExternalResults/FunctionalMonotoneClass.lean
generated: lean
lean_status: lean_ok
private: true
title: MeasureTheory.sequentialSpanMeasurableSpace
type: lean
updated: '2026-10-02T11:55:12'
---
private abbrev sequentialSpanMeasurableSpace {C : Set (X → ℝ)}
    (h1 : (1 : X → ℝ) ∈ C) (hC : ∀ f ∈ C, ∀ g ∈ C, f * g ∈ C) :
    MeasurableSpace X := by
  classical
  refine {
    MeasurableSet' := fun s ↦ s.indicator (fun _ ↦ (1 : ℝ)) ∈ sequentialSpan C
    measurableSet_empty := by
      rw [Set.indicator_empty]
      exact (sequentialSpan C).zero_mem
    measurableSet_compl := fun s hs ↦ ?_
    measurableSet_iUnion := fun s hs ↦ ?_ }
  · rw [Set.indicator_compl]
    exact (sequentialSpan C).sub_mem (sequentialSpan_const h1 1) hs
  · refine isSeqClosed_sequentialSpan C
      (x := fun n : ℕ ↦ fun x ↦ min 1
        (∑ i ∈ Finset.range n, (s i).indicator (fun _ ↦ (1 : ℝ)) x)) ?_ ?_
    · intro n
      change (fun x ↦ min (1 : ℝ) (∑ i ∈ Finset.range n,
        (s i).indicator (fun _ ↦ (1 : ℝ)) x)) ∈ sequentialSpan C
      have hsum : (∑ i ∈ Finset.range n, (s i).indicator (fun _ ↦ (1 : ℝ))) ∈
          sequentialSpan C := (sequentialSpan C).sum_mem fun i _ ↦ hs i
      simpa only [Function.comp_def, Finset.sum_apply, id_eq] using
        sequentialSpan_continuous_comp h1 hC hsum (continuous_const.min continuous_id)
    · apply tendsto_pi_nhds.mpr
      intro x
      by_cases hx : x ∈ ⋃ i, s i
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop (i + 1)] with n hn
        have hsum : (1 : ℝ) ≤ ∑ j ∈ Finset.range n,
            (s j).indicator (fun _ ↦ (1 : ℝ)) x := by
          calc
            1 = (s i).indicator (fun _ ↦ (1 : ℝ)) x := by simp [hi]
            _ ≤ _ := Finset.single_le_sum
              (fun j _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) x)
              (Finset.mem_range.mpr (by omega))
        simp only [Set.indicator_of_mem hx, min_eq_left hsum]
      · have hx' : ∀ i, x ∉ s i := fun i hi ↦ hx (Set.mem_iUnion.mpr ⟨i, hi⟩)
        simp [hx, hx']