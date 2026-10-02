---
author: sync
content_type: theorem
created: '2026-10-02T12:11:38'
decl: ArakelovGeometry.AdelicStructure.integrable_log_localHeight
docstring: The local logarithmic maximum is integrable without a finite-measure hypothesis.
file: ArakelovGeometry/AdelicCurve/Height/Basic.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.integrable_log_localHeight
type: lean
updated: '2026-10-02T12:11:38'
---
theorem integrable_log_localHeight (a : ι → K) :
    Integrable (fun ω ↦ Real.log (AS.localHeight a ω)) AS.v := by
  have hi := integrable_finsetSum Finset.univ
    (fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦ (AS.integrable_log_eval (a i)).norm)
  apply hi.mono' (AS.measurable_localHeight a).log.aestronglyMeasurable
  filter_upwards [] with ω
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i ↦ AS.ϕ ω (a i))
  change ‖Real.log (Finset.univ.sup' _ _)‖ ≤ _
  rw [he]
  exact Finset.single_le_sum (fun j _ ↦ norm_nonneg (Real.log (AS.ϕ ω (a j)))) hi