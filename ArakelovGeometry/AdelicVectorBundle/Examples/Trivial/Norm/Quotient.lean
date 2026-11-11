/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.HN

/-!
# Attained quotient norms at the trivial place

The canonical completed tensor equivalences identify the actual quotient
infimum with the rational lift infimum. Finiteness of the ultrametric norm's
range then produces a lift attaining the quotient norm, including at zero.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

noncomputable section

open AdelicStructure

universe u v w

variable {K : Type u} [Field K] {E : Type v} [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] {Q : Type w} [AddCommGroup Q] [Module K Q]
  (ξ : NormFamily (singleTrivialPlace K) E)
  (q : E →ₗ[K] Q) (hq : Function.Surjective q)

open Classical in
/-- The actual completed-fibre quotient infimum equals the infimum over
rational lifts, through the canonical trivial completed tensor equivalences. -/
theorem trivialSeminorm_pushforward_eq_sInf (y : Q) :
    (ξ.pushforward q hq).trivialSeminorm y =
      sInf (ξ.trivialSeminorm '' {x | q x = y}) := by
  rw [trivialSeminorm_apply]
  rw [ξ.pushforward_norm_eq_sInf q hq PUnit.unit]
  congr 1
  ext r
  constructor
  · rintro ⟨z, hz, rfl⟩
    change (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion ⊗[K] E at z
    change q.baseChange (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion z =
      (1 : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion) ⊗ₜ[K] y at hz
    refine ⟨trivialCompletedTensorEquiv K E z, ?_, ?_⟩
    · change q (trivialCompletedTensorEquiv K E z) = y
      rw [← trivialCompletedTensorEquiv_baseChange q z, hz,
        trivialCompletedTensorEquiv_one_tmul]
    · change ξ.norm PUnit.unit ((trivialCompletedTensorEquiv K E).symm
        (trivialCompletedTensorEquiv K E z)) = ξ.norm PUnit.unit z
      exact congrArg (ξ.norm PUnit.unit)
        ((trivialCompletedTensorEquiv K E).symm_apply_apply z)
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(1 : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion) ⊗ₜ[K] x,
      ?_, ?_⟩
    · change q.baseChange (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
        ((1 : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion) ⊗ₜ[K] x) = _
      rw [LinearMap.baseChange_tmul, hx]
      rfl
    · exact (ξ.trivialSeminorm_apply x).symm

open Classical in
/-- Quotienting contracts the norm of every rational vector. -/
theorem trivialSeminorm_pushforward_le (x : E) :
    (ξ.pushforward q hq).trivialSeminorm (q x) ≤ ξ.trivialSeminorm x := by
  have h := ξ.pushforward_norm_le q hq PUnit.unit
    ((1 : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion) ⊗ₜ[K] x)
  change (ξ.pushforward q hq).norm PUnit.unit
    (q.baseChange (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
      ((1 : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion) ⊗ₜ[K] x)) ≤
    ξ.norm PUnit.unit _ at h
  rw [LinearMap.baseChange_tmul] at h
  rw [trivialSeminorm_apply, trivialSeminorm_apply]
  exact h

open Classical in
/-- Every quotient vector has a rational lift attaining its actual quotient
norm: the nonempty set of lift norms is finite. -/
theorem exists_trivialSeminorm_pushforward_lift (hξ : ξ.IsUltrametric) (y : Q) :
    ∃ x, q x = y ∧ ξ.trivialSeminorm x = (ξ.pushforward q hq).trivialSeminorm y := by
  let A : Set ℝ := ξ.trivialSeminorm '' {x | q x = y}
  have hA : A.Finite := (ξ.finite_range_trivialSeminorm hξ).subset
    (Set.image_subset_range _ _)
  have hn : A.Nonempty := by
    obtain ⟨x, hx⟩ := hq y
    exact ⟨ξ.trivialSeminorm x, x, hx, rfl⟩
  obtain ⟨x, hx, hm⟩ := hn.csInf_mem hA
  refine ⟨x, hx, ?_⟩
  rw [ξ.trivialSeminorm_pushforward_eq_sInf q hq]
  exact hm

end

end ArakelovGeometry.NormFamily
