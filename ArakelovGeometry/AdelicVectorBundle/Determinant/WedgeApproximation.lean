/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Determinant.Basic
import ArakelovGeometry.AdelicVectorBundle.Determinant.Map
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Determinant wedge approximation including degree zero

A scalar coefficient on the wedge retains the actual degree-zero determinant
line. In positive degree the coefficient can be one.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

noncomputable section

variable {K : Type*} [Field K] {S : AdelicStructure K}
  {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Every actual completed determinant vector admits a scalar-weighted wedge
whose product cost is arbitrarily close to its determinant norm, in every rank. -/
theorem exists_smul_determinant_ιMulti_norm_lt (ξ : NormFamily S E) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (a : (S.ϕ ω).Completion)
      (x : Fin (Module.finrank K E) → (S.ϕ ω).Completion ⊗[K] E),
      a • (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm
        (exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K E) x) = z ∧
      ‖a‖ * (∏ i, ξ.norm ω (x i)) < ξ.determinant.norm ω z + ε := by
  by_cases hr : Module.finrank K E = 0
  · let e := exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)
    obtain ⟨a, ha⟩ := exteriorPower_eq_smul_empty (S.ϕ ω).Completion
      (E := (S.ϕ ω).Completion ⊗[K] E) hr (e z)
    have hz : z = a • e.symm (exteriorPower.ιMulti (S.ϕ ω).Completion
        (Module.finrank K E) (fun _ ↦ (0 : (S.ϕ ω).Completion ⊗[K] E))) := by
      have h := congrArg e.symm ha
      simpa only [LinearEquiv.symm_apply_apply, map_smul] using h
    have hn : ξ.determinant.norm ω z = ‖a‖ := by
      rw [hz, ξ.determinant.norm_smul, ξ.determinant_norm_empty_completed hr, mul_one]
    refine ⟨a, fun _ ↦ 0, hz.symm, ?_⟩
    have hp : (∏ i : Fin (Module.finrank K E), ξ.norm ω 0) = 1 := by
      rw [hr]
      simp
    rw [hp, mul_one, hn]
    exact lt_add_of_pos_right _ hε
  · obtain ⟨x, hx, hc⟩ := ξ.exists_determinant_ιMulti_norm_lt (Nat.pos_of_ne_zero hr) ω z hε
    refine ⟨1, x, ?_, ?_⟩
    · simpa only [one_smul] using hx
    · simpa only [norm_one, one_mul] using hc

end

end ArakelovGeometry.NormFamily
