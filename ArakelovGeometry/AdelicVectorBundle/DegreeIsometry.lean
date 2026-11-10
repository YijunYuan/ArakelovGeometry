/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.DeterminantFunctor
import ArakelovGeometry.AdelicVectorBundle.Degree

/-!
# Degree preserved by actual completed-fibre isometries

A rational linear isomorphism preserving every actual completed fibre norm
also preserves the actual determinant norm and its Arakelov degree.
-/

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- Degrees agree under a rational isomorphism which preserves every actual
completed-fibre norm, including in rank zero. -/
theorem degree_eq_of_completed_isometry [S.IsProper]
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F) (e : E ≃ₗ[K] F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (he : ∀ ω x, W.toNormFamily.norm ω
      (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = V.toNormFamily.norm ω x) :
    V.degree hS hN = W.degree hS hN := by
  let D := determinantEquiv K e
  have hr : Module.finrank K (⋀[K]^(Module.finrank K E) E) = 1 :=
    NormFamily.determinant_finrank
  let : Nontrivial (⋀[K]^(Module.finrank K E) E) :=
    Module.nontrivial_of_finrank_pos (by rw [hr]; exact zero_lt_one)
  obtain ⟨z, hz⟩ := exists_ne (0 : ⋀[K]^(Module.finrank K E) E)
  have hDz : D z ≠ 0 := by
    intro h
    exact hz (D.injective (h.trans D.map_zero.symm))
  rw [V.degree_eq_neg_integral hS hN ⟨z, hz⟩,
    W.degree_eq_neg_integral hS hN ⟨D z, hDz⟩]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  have h := V.toNormFamily.determinantEquiv_norm_eq W.toNormFamily ω e
    (he ω) ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] z)
  have h' : W.toNormFamily.determinant.norm ω
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] D z) =
      V.toNormFamily.determinant.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] z) := by
    simpa only [LinearEquiv.baseChange_tmul] using h
  exact (congrArg Real.log h').symm

end ArakelovGeometry.AdelicVectorBundle
