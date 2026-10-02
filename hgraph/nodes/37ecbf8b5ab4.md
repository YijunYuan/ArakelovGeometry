---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.mul_mem_boundedEvaluationGenerators
docstring: Bounded evaluation generators form a multiplicative family.
file: ArakelovGeometry/AdelicCurve/Extension/BoundedEvaluationGenerators.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.mul_mem_boundedEvaluationGenerators
type: lean
updated: '2026-10-02T11:55:12'
---
theorem mul_mem_boundedEvaluationGenerators {f g : ParameterSpaceExtension AS L → ℝ}
    (hf : f ∈ boundedEvaluationGenerators AS) (hg : g ∈ boundedEvaluationGenerators AS) :
    f * g ∈ boundedEvaluationGenerators AS := by
  rcases hf with ⟨⟨M, hM⟩, b, φ, hφ, hφ0, ⟨N, hN⟩, rfl⟩
  rcases hg with ⟨⟨P, hP⟩, c, ψ, hψ, hψ0, ⟨Q, hQ⟩, rfl⟩
  refine ⟨⟨|M| * |P|, fun x ↦ ?_⟩, b * c, φ * ψ, hφ.mul hψ,
    fun ω ↦ mul_nonneg (hφ0 ω) (hψ0 ω), ⟨|N| * |Q|, fun ω ↦ ?_⟩, ?_⟩
  · change |(x.ϕ b * φ x.proj) * (x.ϕ c * ψ x.proj)| ≤ _
    rw [abs_mul]
    exact mul_le_mul ((hM x).trans (le_abs_self M)) ((hP x).trans (le_abs_self P))
      (abs_nonneg _) (abs_nonneg _)
  · change |φ ω * ψ ω| ≤ _
    rw [abs_mul]
    exact mul_le_mul ((hN ω).trans (le_abs_self N)) ((hQ ω).trans (le_abs_self Q))
      (abs_nonneg _) (abs_nonneg _)
  · ext x
    simp only [Pi.mul_apply, map_mul]
    ring