/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Basic
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Line
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Rational
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# The scalar adelic line

The absolute values of an adelic structure define an adelic bundle on the
actual scalar space `K`. Its completed norms are the singleton basis norms.
The norm of `1` is exactly one, so rank-one domination needs no finite-measure
or Archimedean hypothesis.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

universe u v

variable {K : Type u} [Field K] (S : AdelicStructure.{u, v} K)

/-- The scalar line with the prescribed absolute values. -/
noncomputable def scalarLine : AdelicVectorBundle S K := by
  let b := Module.Basis.singleton (Fin 1) K
  let ξ := NormFamily.ofBasis S K b
  have hnorm (ω : S.Ω) : ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (1 : K)) = 1 := by
    have h := NormFamily.ofBasis_norm_tmul_basis S K b ω 1 0
    rw [show b 0 = 1 from Module.Basis.singleton_apply (Fin 1) K 0] at h
    exact h.trans (norm_one : ‖(1 : (S.ϕ ω).Completion)‖ = 1)
  have hlog : ξ.logNorm 1 = 0 := by
    funext ω
    simp only [NormFamily.logNorm, hnorm, Real.log_one, Pi.zero_apply]
  exact ofLine ξ (Module.finrank_self K) (by exact NormFamily.ofBasis_isMeasurable b) (by
    apply (ξ.isDominated_iff_logNorm_bounds (Module.finrank_self K) one_ne_zero).2
    apply integrable_hasIntegrableBounds
    rw [hlog]
    exact integrable_zero _ _ _)

/-- The scalar line retains the actual singleton completed-basis norm. -/
@[simp]
theorem scalarLine_toNormFamily :
    (scalarLine S).toNormFamily = NormFamily.ofBasis S K (Module.Basis.singleton (Fin 1) K) := rfl

/-- The scalar adelic bundle has rank one. -/
theorem scalarLine_isLine : (scalarLine S).IsLine := Module.finrank_self K

/-- The completed norm of a scalar multiple of the scalar generator. -/
@[simp]
theorem scalarLine_norm_tmul_one (ω : S.Ω) (a : (S.ϕ ω).Completion) :
    (scalarLine S).norm ω (a ⊗ₜ[K] (1 : K)) = ‖a‖ := by
  rw [scalarLine_toNormFamily]
  simpa only [Module.Basis.singleton_apply] using
    NormFamily.ofBasis_norm_tmul_basis S K (Module.Basis.singleton (Fin 1) K) ω a 0

/-- On rational scalars the norm is the original absolute value. -/
@[simp]
theorem scalarLine_norm_rational (ω : S.Ω) (a : K) :
    (scalarLine S).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] a) = S.ϕ ω a := by
  have h := (scalarLine S).toNormFamily.norm_rational_smul ω a (1 : K)
  simpa only [smul_eq_mul, mul_one, scalarLine_norm_tmul_one, norm_one] using h

end ArakelovGeometry.AdelicVectorBundle
