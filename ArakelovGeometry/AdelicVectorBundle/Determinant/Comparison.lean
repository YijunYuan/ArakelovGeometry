/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Determinant.Basic
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Comparison
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Order and scaling of determinant norms

The actual completed determinant norm preserves pointwise order, multiplies
by the rank-th power under rescaling, and increases local distance by at most
the rank. The proofs use nearly optimal single wedge presentations, with a
separate zero-dimensional argument.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- A positive fibrewise comparison constant becomes its rank-th power on
the actual determinant line, including rank zero. -/
theorem determinant_norm_le_mul_pow (ξ η : NormFamily S E) (ω : S.Ω)
    {C : ℝ} (hC : 0 < C) (h : ∀ x, ξ.norm ω x ≤ C * η.norm ω x)
    (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    ξ.determinant.norm ω z ≤ C ^ Module.finrank K E * η.determinant.norm ω z := by
  by_cases hr : Module.finrank K E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hr
    have hpow : C ^ Module.finrank K E = 1 := by rw [hr, pow_zero]
    rw [Subsingleton.elim ξ η, hpow, one_mul]
  · have hr' : 0 < Module.finrank K E := Nat.pos_of_ne_zero hr
    have hCr := pow_pos hC (Module.finrank K E)
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨x, hx, he⟩ := η.exists_determinant_ιMulti_norm_lt hr' ω z (div_pos hε hCr)
    have hp : (∏ i, ξ.norm ω (x i)) ≤ C ^ Module.finrank K E * ∏ i, η.norm ω (x i) := by
      calc
        _ ≤ ∏ i, C * η.norm ω (x i) :=
          Finset.prod_le_prod₀ (fun _ _ ↦ ξ.norm_nonneg ω _) (fun i _ ↦ h (x i))
        _ = _ := by rw [Finset.prod_mul_distrib]; simp
    have he' := mul_lt_mul_of_pos_left he hCr
    rw [mul_add, mul_div_cancel₀ _ hCr.ne'] at he'
    have hdet := ξ.determinant_norm_ιMulti_le ω x
    rw [hx] at hdet
    exact (hdet.trans hp).trans he'.le

/-- Determinant norms preserve pointwise order on a completed fibre. -/
theorem determinant_norm_mono (ξ η : NormFamily S E) (ω : S.Ω)
    (h : ∀ x, ξ.norm ω x ≤ η.norm ω x)
    (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    ξ.determinant.norm ω z ≤ η.determinant.norm ω z := by
  simpa only [one_pow, one_mul] using
    ξ.determinant_norm_le_mul_pow η ω zero_lt_one (by simpa only [one_mul]) z

/-- The determinant construction is order preserving on norm families. -/
theorem determinant_mono {ξ η : NormFamily S E} (h : ξ ≤ η) :
    ξ.determinant ≤ η.determinant := fun ω z ↦ ξ.determinant_norm_mono η ω (h ω) z

/-- Exact determinant rescaling on every actual completed vector. -/
theorem determinant_scale_norm (ξ : NormFamily S E) (f : S.Ω → ℝ)
    (hf : ∀ ω, 0 < f ω) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    (ξ.scale f hf).determinant.norm ω z =
      f ω ^ Module.finrank K E * ξ.determinant.norm ω z := by
  apply le_antisymm
  · exact (ξ.scale f hf).determinant_norm_le_mul_pow ξ ω (hf ω) (fun _ ↦ le_rfl) z
  · have h := ξ.determinant_norm_le_mul_pow (ξ.scale f hf) ω
      (inv_pos.mpr (hf ω)) (by intro x; simp only [scale_norm, ← mul_assoc,
        inv_mul_cancel₀ (hf ω).ne', one_mul, le_refl]) z
    have hh := mul_le_mul_of_nonneg_left h (pow_pos (hf ω) (Module.finrank K E)).le
    simpa only [← mul_assoc, ← mul_pow, mul_inv_cancel₀ (hf ω).ne', one_pow, one_mul]
      using hh

/-- Exact family equality for determinant rescaling, with exponent zero in rank zero. -/
theorem determinant_scale (ξ : NormFamily S E) (f : S.Ω → ℝ) (hf : ∀ ω, 0 < f ω) :
    (ξ.scale f hf).determinant = ξ.determinant.scale
      (fun ω ↦ f ω ^ Module.finrank K E) (fun ω ↦ pow_pos (hf ω) _) := by
  ext ω z
  exact ξ.determinant_scale_norm f hf ω z

/-- Local determinant distance is bounded by rank times the original distance. -/
theorem determinant_localDist_le (ξ η : NormFamily S E) (ω : S.Ω) :
    ξ.determinant.localDist η.determinant ω ≤
      Module.finrank K E * ξ.localDist η ω := by
  apply (ξ.determinant.localDist_le_iff_norm_le η.determinant ω
    (mul_nonneg (Nat.cast_nonneg _) (ξ.localDist_nonneg η ω))).2
  intro z
  constructor
  · have h := ξ.determinant_norm_le_mul_pow η ω (Real.exp_pos (ξ.localDist η ω))
      (fun x ↦ η.norm_le_exp_mul_of_localDist_le ξ ω (by rw [localDist_comm]) x) z
    simpa only [Real.exp_nat_mul] using h
  · have h := η.determinant_norm_le_mul_pow ξ ω (Real.exp_pos (ξ.localDist η ω))
      (ξ.norm_le_exp_localDist_mul η ω) z
    simpa only [Real.exp_nat_mul] using h

end ArakelovGeometry.NormFamily
