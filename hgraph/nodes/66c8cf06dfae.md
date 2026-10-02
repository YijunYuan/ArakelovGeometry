---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.exists_measurable_eval_bound
file: ArakelovGeometry/AdelicCurve/Extension/BoundedEvaluationGenerators.lean
generated: lean
lean_status: lean_ok
private: true
title: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.exists_measurable_eval_bound
type: lean
updated: '2026-10-02T11:55:12'
---
private theorem exists_measurable_eval_bound [Algebra.IsAlgebraic K L] (b : L) :
    ∃ B : AS.Ω → ℝ, Measurable B ∧
      ∀ x : ParameterSpaceExtension AS L, x.ϕ b ≤ B x.proj := by
  classical
  let p := minpoly K b
  let M := fun ω ↦ 1 + ∑ i ∈ Finset.range p.natDegree, AS.ϕ ω (p.coeff i)
  have hM : Measurable M := measurable_const.add
    (Finset.measurable_fun_sum _ fun i _ ↦ measurable_base_eval AS (p.coeff i))
  refine ⟨fun ω ↦ (p.natDegree : ℝ) * M ω, measurable_const.mul hM, fun x ↦ ?_⟩
  apply x.ϕ.apply_root_le_degree_mul (minpoly.monic (Algebra.IsIntegral.isIntegral b))
    (minpoly.aeval K b)
  · dsimp [M]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ (AS.ϕ x.proj).nonneg _)
  · intro i hi
    have hr : x.ϕ (algebraMap K L (p.coeff i)) = AS.ϕ x.proj (p.coeff i) :=
      congrArg (fun v : AbsoluteValue K ℝ ↦ v (p.coeff i)) (ϕ_restriction AS L x)
    rw [hr]
    exact (Finset.single_le_sum (fun j _ ↦ (AS.ϕ x.proj).nonneg _)
      (Finset.mem_range.mpr hi)).trans (le_add_of_nonneg_left zero_le_one)