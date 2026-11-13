/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicDivisor.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Principal adelic divisors

The logarithmic map on field units is extended real-linearly using the
canonical scalar-first tensor product. The source's reversed tensor order
is connected explicitly by `TensorProduct.comm`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped TensorProduct

namespace ArakelovGeometry.AdelicDivisor

universe u

variable {K : Type u} [Field K] (S : AdelicStructure K)

/-- The divisor associated with a field unit is the class of its negative
logarithmic absolute value. Integrability is supplied by the adelic structure. -/
noncomputable def principal (a : Kˣ) : AdelicDivisor S :=
  ofIntegrable S (fun ω => -Real.log (S.ϕ ω (a : K)))
    (S.integrable_log (a : K) a.ne_zero).neg

/-- The exact almost-everywhere representative of a principal divisor. -/
theorem coeFn_principal (a : Kˣ) :
    principal S a =ᵐ[S.v] fun ω => -Real.log (S.ϕ ω (a : K)) :=
  ((S.integrable_log (a : K) a.ne_zero).neg).coeFn_toL1

/-- The divisor of one is zero. -/
@[simp]
theorem principal_one : principal S 1 = 0 := by
  apply Lp.ext
  filter_upwards [coeFn_principal S 1, Lp.coeFn_zero ℝ 1 S.v] with ω h₁ h₀
  simp only [h₁, h₀, Units.val_one, map_one, Real.log_one, neg_zero, Pi.zero_apply]

/-- Multiplication of field units adds their actual logarithmic divisors. -/
@[simp]
theorem principal_mul (a b : Kˣ) : principal S (a * b) = principal S a + principal S b := by
  apply Lp.ext
  filter_upwards [coeFn_principal S (a * b), coeFn_principal S a,
    coeFn_principal S b, Lp.coeFn_add (principal S a) (principal S b)] with ω hab ha hb hsum
  simp only [hsum, Pi.add_apply, hab, ha, hb, Units.val_mul, map_mul,
    Real.log_mul ((S.ϕ ω).pos a.ne_zero).ne' ((S.ϕ ω).pos b.ne_zero).ne', neg_add]

/-- The principal logarithmic map, with field multiplication written additively. -/
noncomputable def principalHom : Additive Kˣ →+ AdelicDivisor S where
  toFun a := principal S a.toMul
  map_zero' := principal_one S
  map_add' a b := principal_mul S a.toMul b.toMul

/-- The unique real-linear extension of the logarithmic map to the scalar-first
tensor product. `principalTensorMap_source_tmul` records the source orientation. -/
noncomputable def principalTensorMap : (ℝ ⊗[ℤ] Additive Kˣ) →ₗ[ℝ] AdelicDivisor S :=
  (principalHom S).toIntLinearMap.liftBaseChange ℝ

/-- The real-linear principal map on a pure tensor. -/
@[simp]
theorem principalTensorMap_tmul (t : ℝ) (a : Additive Kˣ) :
    principalTensorMap S (t ⊗ₜ[ℤ] a) = t • principal S a.toMul := rfl

/-- The exact pure-tensor formula in Chen–Moriwaki's factor order. -/
theorem principalTensorMap_source_tmul (a : Additive Kˣ) (t : ℝ) :
    principalTensorMap S (TensorProduct.comm ℤ (Additive Kˣ) ℝ (a ⊗ₜ[ℤ] t)) =
      t • principal S a.toMul := rfl

/-- Uniqueness of the real-linear extension follows from the tensor universal property. -/
theorem principalTensorMap_unique (f : (ℝ ⊗[ℤ] Additive Kˣ) →ₗ[ℝ] AdelicDivisor S)
    (hf : ∀ a, f (1 ⊗ₜ[ℤ] a) = principal S a.toMul) : f = principalTensorMap S := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro t a
  calc
    f (t ⊗ₜ[ℤ] a) = f (t • (1 ⊗ₜ[ℤ] a)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = t • principal S a.toMul := by rw [map_smul, hf]
    _ = principalTensorMap S (t ⊗ₜ[ℤ] a) := (principalTensorMap_tmul S t a).symm

/-- Principal adelic divisors form the closure of the real tensor-map range,
exactly as in the source definition. -/
noncomputable def principalSubspace : Submodule ℝ (AdelicDivisor S) :=
  (principalTensorMap S).range.topologicalClosure

/-- The principal subspace is closed by construction. -/
theorem isClosed_principalSubspace : IsClosed (principalSubspace S : Set (AdelicDivisor S)) :=
  (principalTensorMap S).range.isClosed_topologicalClosure

/-- Each divisor associated with an individual field unit lies in the closed principal space. -/
theorem principal_mem_principalSubspace (a : Kˣ) : principal S a ∈ principalSubspace S := by
  apply (principalTensorMap S).range.le_topologicalClosure
  exact ⟨1 ⊗ₜ[ℤ] Additive.ofMul a, by simp⟩

/-- Degree of the divisor associated with a unit, before imposing properness. -/
theorem degree_principal (a : Kˣ) :
    degree S (principal S a) = -(∫ ω, Real.log (S.ϕ ω (a : K)) ∂S.v) := by
  rw [principal, degree_ofIntegrable, integral_neg]

variable [S.IsProper]

/-- The product formula kills the degree of every individual principal divisor. -/
@[simp]
theorem degree_principal_eq_zero (a : Kˣ) : degree S (principal S a) = 0 := by
  rw [degree_principal, AdelicStructure.IsProper.product_formula (a : K) a.ne_zero, neg_zero]

/-- Real linearity extends the product formula to the full tensor-map image. -/
@[simp]
theorem degree_principalTensorMap (z : ℝ ⊗[ℤ] Additive Kˣ) :
    degree S (principalTensorMap S z) = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul t a => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

/-- Continuity of degree extends the product formula to the closed principal
subspace, which can contain limits outside the algebraic tensor-map image. -/
theorem principalSubspace_le_ker_degree : principalSubspace S ≤ (degree S).ker := by
  apply (principalTensorMap S).range.topologicalClosure_minimal
  · rintro _ ⟨z, rfl⟩
    exact degree_principalTensorMap S z
  · exact (degree S).isClosed_ker

/-- Degree vanishes on every principal adelic divisor in the source's closed sense. -/
theorem degree_eq_zero_of_mem_principalSubspace {ζ : AdelicDivisor S}
    (hζ : ζ ∈ principalSubspace S) : degree S ζ = 0 :=
  principalSubspace_le_ker_degree S hζ

end ArakelovGeometry.AdelicDivisor
