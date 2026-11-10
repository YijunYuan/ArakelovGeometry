/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NonpureNumberFieldMinkowskiObstructionDeterminant
import Mathlib.Data.Nat.Factorial.Basic

/-! # Primitive integer arithmetic for the actual nonpure rational plane -/

namespace ArakelovGeometry.NonpureNumberFieldMinkowskiObstruction

theorem prime_not_dvd_root_minus_one (p : Nat.Primes) (a : ℤ)
    (ha : (p.val : ℤ) ∣ a ^ 2 + 1) : ¬ (p.val : ℤ) ∣ a := by
  intro h
  have hs : (p.val : ℤ) ∣ a ^ 2 := by
    simpa only [pow_two] using dvd_mul_of_dvd_left h a
  have h1 : (p.val : ℤ) ∣ 1 := by simpa using dvd_sub ha hs
  exact p.property.not_dvd_one (by exact_mod_cast h1)

theorem primitive_square_sum_pos (x y : ℤ) (hxy : IsCoprime x y) :
    0 < x ^ 2 + y ^ 2 := by
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by
      intro hy
      obtain ⟨b, c, h⟩ := hxy
      simp only [hx, hy, mul_zero, add_zero] at h
      exact zero_ne_one h
    nlinarith [sq_pos_of_ne_zero hy, sq_nonneg x]
  · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg y]

theorem primitive_one_le_euclidean (x y : ℤ) (hxy : IsCoprime x y) :
    1 ≤ Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) := by
  have h : (1 : ℤ) ≤ x ^ 2 + y ^ 2 := by
    have := primitive_square_sum_pos x y hxy
    omega
  have hr : (1 : ℝ) ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 := by exact_mod_cast h
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hr

theorem primitive_good_congruence_first_unit (p : Nat.Primes) (a x y : ℤ)
    (hxy : IsCoprime x y) (hc : (p.val : ℤ) ∣ y - a * x) :
    ¬ (p.val : ℤ) ∣ x := by
  intro hx
  have hy : (p.val : ℤ) ∣ y := by
    simpa only [sub_add_cancel] using dvd_add hc (dvd_mul_of_dvd_right hx a)
  obtain ⟨b, c, hb⟩ := hxy
  have h1 : (p.val : ℤ) ∣ 1 := by
    rw [← hb]
    exact dvd_add (dvd_mul_of_dvd_right hx b) (dvd_mul_of_dvd_right hy c)
  exact p.property.not_dvd_one (by exact_mod_cast h1)

theorem good_congruence_square_sum_dvd (p : Nat.Primes) (a x y : ℤ)
    (ha : (p.val : ℤ) ∣ a ^ 2 + 1) (hc : (p.val : ℤ) ∣ y - a * x) :
    (p.val : ℤ) ∣ x ^ 2 + y ^ 2 := by
  have h := dvd_add (dvd_mul_of_dvd_left ha (x ^ 2))
    (dvd_mul_of_dvd_left hc (y + a * x))
  rw [show x ^ 2 + y ^ 2 = (a ^ 2 + 1) * x ^ 2 + (y - a * x) * (y + a * x) by ring]
  exact h

theorem primitive_good_congruence_euclidean_bound (p : Nat.Primes) (a x y : ℤ)
    (ha : (p.val : ℤ) ∣ a ^ 2 + 1) (hxy : IsCoprime x y)
    (hc : (p.val : ℤ) ∣ y - a * x) :
    Real.sqrt (p.val : ℝ) ≤ Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) := by
  have h : (p.val : ℤ) ≤ x ^ 2 + y ^ 2 :=
    Int.le_of_dvd (primitive_square_sum_pos x y hxy)
      (good_congruence_square_sum_dvd p a x y ha hc)
  have hr : (p.val : ℝ) ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 := by exact_mod_cast h
  exact Real.sqrt_le_sqrt hr

/-- The factorial construction produces arbitrarily large actual prime indices
with a square root of minus one; no unboundedness certificate is assumed. -/
theorem exists_large_prime_minus_one_square (B : ℕ) (hB : 2 ≤ B) :
    ∃ p : Nat.Primes, B < p.val ∧ Odd p.val ∧
      ∃ a : ℤ, (p.val : ℤ) ∣ a ^ 2 + 1 := by
  let a := 2 * B.factorial
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd
    (show a ^ 2 + 1 ≠ 1 by nlinarith)
  have hlarge : B < p := by
    by_contra! h
    have hpa : p ∣ a := dvd_mul_of_dvd_right (Nat.dvd_factorial hp.pos h) 2
    have hs : p ∣ a ^ 2 := by simpa only [pow_two] using dvd_mul_of_dvd_left hpa a
    have h1 : p ∣ 1 := by simpa using Nat.dvd_sub hd hs
    exact hp.not_dvd_one h1
  refine ⟨⟨p, hp⟩, hlarge, hp.odd_of_ne_two (by omega), (a : ℤ), ?_⟩
  exact_mod_cast hd

open AdelicStructure NormFamily
open scoped TensorProduct

/-- The canonical normalized infinity branch on actual integer vectors is
exactly their usual Euclidean norm. -/
theorem family_norm_infinite_integer (p : Nat.Primes) (a : ℤ) (ω : S.Ω)
    (hω : ω ∈ S.Ωinf) (x y : ℤ) :
    (family p a).norm ω (1 ⊗ₜ[ℚ] (![x, y] : Plane)) =
      Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) := by
  have hc (i : Fin 2) : completedCoordinates ω (1 ⊗ₜ[ℚ] (![x, y] : Plane)) i =
      algebraMap ℚ (S.ϕ ω).Completion ((![(x : ℚ), (y : ℚ)] : Plane) i) := by
    simp only [completedCoordinates, basis_equivFun_one_tmul, standardBasis]
    rfl
  let := normalizedNumberFieldArchimedeanCompletions (K := ℚ) ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  have hint (n : ℤ) : ‖(n : (S.ϕ ω).Completion)‖ = |(n : ℝ)| := by
    rw [← RCLike.ofReal_intCast, RCLike.norm_ofReal]
  rw [family_norm_infinite p a ω hω, Fin.sum_univ_two, hc 0, hc 1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    map_intCast, hint, sq_abs]

theorem primitive_one_le_family_norm_infinite (p : Nat.Primes) (a : ℤ) (ω : S.Ω)
    (hω : ω ∈ S.Ωinf) (x y : ℤ) (hxy : IsCoprime x y) :
    1 ≤ (family p a).norm ω (1 ⊗ₜ[ℚ] (![x, y] : Plane)) := by
  rw [family_norm_infinite_integer p a ω hω]
  exact primitive_one_le_euclidean x y hxy

theorem primitive_good_congruence_family_norm_infinite_bound (p : Nat.Primes)
    (a : ℤ) (ha : (p.val : ℤ) ∣ a ^ 2 + 1) (ω : S.Ω) (hω : ω ∈ S.Ωinf)
    (x y : ℤ) (hxy : IsCoprime x y) (hc : (p.val : ℤ) ∣ y - a * x) :
    Real.sqrt (p.val : ℝ) ≤ (family p a).norm ω (1 ⊗ₜ[ℚ] (![x, y] : Plane)) := by
  rw [family_norm_infinite_integer p a ω hω]
  exact primitive_good_congruence_euclidean_bound p a x y ha hxy hc

end ArakelovGeometry.NonpureNumberFieldMinkowskiObstruction
