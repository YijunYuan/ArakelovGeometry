/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-! # Rational scalar formulas for norm families -/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

universe u w

variable {K : Type u} [Field K]

namespace AdelicStructure

variable (S : AdelicStructure K)

/-- The canonical rational scalar embedding has its prescribed absolute value. -/
theorem norm_algebraMap_eq_absValue (ω : S.Ω) (a : K) :
    ‖algebraMap K (S.ϕ ω).Completion a‖ = (S.ϕ ω) a := by
  change ‖(WithAbs.toAbs (S.ϕ ω) a : (S.ϕ ω).Completion)‖ = _
  rw [UniformSpace.Completion.norm_coe]
  rfl

/-- Scalar absolute values are measurable, including the zero scalar. -/
theorem measurable_absValue (a : K) : Measurable (fun ω : S.Ω ↦ (S.ϕ ω) a) := by
  by_cases ha : a = 0
  · simp only [ha, map_zero]
    exact measurable_const
  · have he : (fun ω : S.Ω ↦ Real.exp (Real.log ((S.ϕ ω) a))) =
        fun ω ↦ (S.ϕ ω) a := by
      funext ω
      exact Real.exp_log ((S.ϕ ω).pos ha)
    rw [← he]
    exact (S.measurable_log a ha).exp

end AdelicStructure

namespace NormFamily

variable {S : AdelicStructure K} {E : Type w} [AddCommGroup E] [Module K E]

/-- Rational scalar multiplication satisfies the original absolute-value law. -/
theorem norm_rational_smul (ξ : NormFamily S E) (ω : S.Ω) (a : K) (x : E) :
    ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (a • x)) =
      (S.ϕ ω) a * ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) := by
  have ht : algebraMap K (S.ϕ ω).Completion a •
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) =
        (1 : (S.ϕ ω).Completion) ⊗ₜ[K] (a • x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [← ht, ξ.norm_smul, S.norm_algebraMap_eq_absValue]

/-- The logarithmic rational scalar identity at a nonzero vector. -/
theorem logNorm_smul (ξ : NormFamily S E) {a : K} (ha : a ≠ 0)
    {x : E} (hx : x ≠ 0) (ω : S.Ω) :
    ξ.logNorm (a • x) ω = Real.log ((S.ϕ ω) a) + ξ.logNorm x ω := by
  unfold logNorm
  rw [ξ.norm_rational_smul, Real.log_mul ((S.ϕ ω).pos ha).ne'
    (ξ.norm_rational_pos ω hx).ne']

end NormFamily
end ArakelovGeometry
