/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Determinant.Basic
import ArakelovGeometry.AdelicVectorBundle.Determinant.WedgeApproximation
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Universal property of actual determinant norms

Scalar-weighted wedge approximation gives maximality among seminorms with
Hadamard's wedge bound, including the degree-zero determinant line.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E)

/-- The actual determinant quotient is maximal among seminorms with
Hadamard's wedge bound. Scalar-weighted wedge approximation includes rank zero. -/
theorem seminorm_le_determinant_of_ιMulti_le (ω : S.Ω)
    (p : Seminorm (S.ϕ ω).Completion
      ((S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)))
    (hp : ∀ x : Fin (Module.finrank K E) → (S.ϕ ω).Completion ⊗[K] E,
      p ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm
        (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K E) x)) ≤
          ∏ i, ξ.norm ω (x i))
    (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    p z ≤ ξ.determinant.norm ω z := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a, x, hx, hc⟩ := ξ.exists_smul_determinant_ιMulti_norm_lt ω z hε
  calc
    p z = ‖a‖ * p ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E
        (Module.finrank K E)).symm
          (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K E) x)) := by
      rw [← hx, map_smul_eq_mul]
    _ ≤ ‖a‖ * ∏ i, ξ.norm ω (x i) :=
      mul_le_mul_of_nonneg_left (hp x) (_root_.norm_nonneg a)
    _ ≤ ξ.determinant.norm ω z + ε := hc.le

end

end ArakelovGeometry.NormFamily
