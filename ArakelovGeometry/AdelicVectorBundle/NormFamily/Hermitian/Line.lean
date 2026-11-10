/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Hermitian.Basic
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Line
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Hermitian norms on lines

Every norm family in rank at most one is Hermitian under the source's usual
Archimedean normalization. The proof transports the scalar parallelogram
identity along a completed generator, without changing the completed scalar action.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Every norm on a line is Hermitian at the source's normalized infinite places. -/
theorem isHermitian_of_finrank_one (ξ : NormFamily S E) (hr : Module.finrank K E = 1)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ξ.IsHermitian hS := by
  apply isHermitian_iff_parallelogram.mpr
  refine ⟨ξ.isUltrametric_of_finrank_le_one hr.le, fun ω hω x y ↦ ?_⟩
  let := hS ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  have hd : Module.finrank (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E) = 1 :=
    Module.finrank_baseChange.trans hr
  have : Nontrivial ((S.ϕ ω).Completion ⊗[K] E) :=
    Module.nontrivial_of_finrank_pos
      (by omega : 0 < Module.finrank (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E))
  obtain ⟨e, he⟩ := exists_ne (0 : (S.ϕ ω).Completion ⊗[K] E)
  obtain ⟨a, rfl⟩ := exists_smul_eq_of_finrank_one hd he x
  obtain ⟨b, rfl⟩ := exists_smul_eq_of_finrank_one hd he y
  rw [← add_smul, ← sub_smul]
  simp only [ξ.norm_smul]
  linear_combination (ξ.norm ω e) ^ 2 *
    parallelogram_law_with_norm (S.ϕ ω).Completion a b

/-- The line result includes rank zero with its unique norm family. -/
theorem isHermitian_of_finrank_le_one (ξ : NormFamily S E) (hr : Module.finrank K E ≤ 1)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ξ.IsHermitian hS := by
  by_cases hz : Module.finrank K E = 0
  · have : Subsingleton E := ⟨fun x y ↦
      ((finrank_zero_iff_forall_zero.mp hz) x).trans
        ((finrank_zero_iff_forall_zero.mp hz) y).symm⟩
    exact isHermitian_of_subsingleton
  · exact ξ.isHermitian_of_finrank_one (by omega) hS

end ArakelovGeometry.NormFamily
