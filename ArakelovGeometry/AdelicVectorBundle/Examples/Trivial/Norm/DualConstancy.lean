/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Norm.Basic

import ArakelovGeometry.AdelicVectorBundle.Determinant.Bidual
import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Norm.Bidual
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Actual dual constancy at the mass-one trivial place

Constant actual norms and their operator duals have reciprocal values.
Triple duality makes actual semistability equivalent to dual constancy,
without ultrametricity of the original norm. The source dual logarithmic
identity uses ordinary mean, hence degree divided by rank.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u w

variable {K : Type u} [Field K] {E : Type w} [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

namespace NormFamily

open AdelicStructure

open Classical in
/-- Every nonzero functional has the reciprocal constant norm on the
actual completed operator dual of a genuine constant norm. -/
theorem trivialSeminorm_dual_eq_inv_of_trivialSeminorm_eq_const
    (ξ : NormFamily (singleTrivialPlace K) E) {c : ℝ} (hc : 0 < c)
    (h : ∀ x, x ≠ 0 → ξ.trivialSeminorm x = c) (ℓ : Module.Dual K E) (hℓ : ℓ ≠ 0) :
    ξ.dual.trivialSeminorm ℓ = c⁻¹ := by
  have hu : ξ.dual.trivialSeminorm ℓ ≤ c⁻¹ := by
    rw [trivialSeminorm_apply]
    exact ξ.dual_norm_le_inv_of_trivialSeminorm_ge hc
      (fun x hx ↦ (h x hx).ge) _
  apply le_antisymm hu
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hℓ
  have hxn : x ≠ 0 := by
    intro hz
    apply hx
    rw [hz, map_zero, LinearMap.zero_apply]
  have hp := h x hxn
  let C := (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
  let p : Seminorm C (C ⊗[K] E) := ξ.norm PUnit.unit
  let q : Seminorm C (C ⊗[K] Module.Dual K E) := ξ.dual.norm PUnit.unit
  rw [trivialSeminorm_apply] at hp
  change p ((1 : C) ⊗ₜ[K] x) = c at hp
  have he := ξ.norm_dual_tmul_apply_tmul_le PUnit.unit (1 : C) (1 : C) ℓ x
  change ‖(1 : C) * 1 * algebraMap K C (ℓ x)‖ ≤
    q ((1 : C) ⊗ₜ[K] ℓ) * p ((1 : C) ⊗ₜ[K] x) at he
  rw [one_mul, one_mul, norm_trivialCompletion K, trivialCompletionAlgEquiv_algebraMap,
    AbsoluteValue.trivial_apply (by simpa only [LinearMap.zero_apply] using hx), hp] at he
  rw [trivialSeminorm_apply]
  change c⁻¹ ≤ q ((1 : C) ⊗ₜ[K] ℓ)
  simpa only [one_div] using (div_le_iff₀ hc).mpr he

open Classical in
/-- A constant actual canonical bidual has the same reciprocal constant
on the original actual dual, by the genuine triple-dual family identity. -/
theorem trivialSeminorm_dual_eq_inv_of_trivialSeminorm_bidual_eq_const
    (ξ : NormFamily (singleTrivialPlace K) E) {c : ℝ} (hc : 0 < c)
    (h : ∀ x, x ≠ 0 → (ξ.dual.dual.pullback (Module.Dual.eval K E)
      (Module.eval_apply_injective K)).trivialSeminorm x = c)
    (ℓ : Module.Dual K E) (hℓ : ℓ ≠ 0) : ξ.dual.trivialSeminorm ℓ = c⁻¹ := by
  have he := trivialSeminorm_dual_eq_inv_of_trivialSeminorm_eq_const
    (ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)) hc h ℓ hℓ
  rwa [ξ.dual_dual_pullback_dual_eq] at he

open Classical in
/-- Constant actual dual norms make the actual canonical bidual constant
on every nonzero original vector, using injective algebraic evaluation. -/
theorem trivialSeminorm_bidual_eq_inv_of_trivialSeminorm_dual_eq_const
    (ξ : NormFamily (singleTrivialPlace K) E) {d : ℝ} (hd : 0 < d)
    (h : ∀ ℓ, ℓ ≠ 0 → ξ.dual.trivialSeminorm ℓ = d) (x : E) (hx : x ≠ 0) :
    (ξ.dual.dual.pullback (Module.Dual.eval K E)
      (Module.eval_apply_injective K)).trivialSeminorm x = d⁻¹ := by
  have hxeval : Module.Dual.eval K E x ≠ 0 := by
    intro hz
    apply hx
    apply Module.eval_apply_injective K
    simpa only [map_zero] using hz
  have he := ξ.dual.trivialSeminorm_dual_eq_inv_of_trivialSeminorm_eq_const
    hd h (Module.Dual.eval K E x) hxeval
  rw [trivialSeminorm_apply] at he ⊢
  let C := (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
  let qq : Seminorm C (C ⊗[K] Module.Dual K (Module.Dual K E)) :=
    ξ.dual.dual.norm PUnit.unit
  change qq ((Module.Dual.eval K E).baseChange C ((1 : C) ⊗ₜ[K] x)) = d⁻¹
  rw [LinearMap.baseChange_tmul]
  exact he

end NormFamily

namespace AdelicVectorBundle

open AdelicStructure

variable (V : AdelicVectorBundle (singleTrivialPlace K))
  [hS : (singleTrivialPlace K).NormMeasurabilityHypotheses]
  [hN : (singleTrivialPlace K).IsArchimedeanNormalized]

open Classical in
/-- The actual source dual-constancy characterization retains the true
positive-rank semistability scope and allows arbitrary original norms. -/
theorem isSemistable_iff_exists_trivialSeminorm_dual_eq_const
    (hr : 0 < Module.finrank K V) :
    V.IsSemistable ↔ ∃ d : ℝ, 0 < d ∧
      ∀ ℓ, ℓ ≠ 0 → V.toNormFamily.dual.trivialSeminorm ℓ = d := by
  rw [V.isSemistable_iff_exists_trivialSeminorm_bidual_eq_const hr]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c⁻¹, inv_pos.mpr hc, fun ℓ hℓ ↦
      V.toNormFamily.trivialSeminorm_dual_eq_inv_of_trivialSeminorm_bidual_eq_const hc h ℓ hℓ⟩
  · rintro ⟨d, hd, h⟩
    exact ⟨d⁻¹, inv_pos.mpr hd, fun x hx ↦
      V.toNormFamily.trivialSeminorm_bidual_eq_inv_of_trivialSeminorm_dual_eq_const hd h x hx⟩

open Classical in
/-- Corrected Remark4.3.62 on every nonzero actual completed functional:
the source expression requires degree divided by positive rank. -/
theorem neg_log_dual_norm_eq_neg_degree_div_of_isSemistable
    [hV : V.IsSemistable] (ω : (singleTrivialPlace K).Ω)
    (z : ((singleTrivialPlace K).ϕ ω).Completion ⊗[K] Module.Dual K V) (hz : z ≠ 0) :
    -Real.log (V.toNormFamily.dual.norm ω z) =
      -(V.degree / (Module.finrank K V : ℝ)) := by
  obtain ⟨c, hc, h⟩ := (V.isSemistable_iff_exists_trivialSeminorm_bidual_eq_const
    hV.1).mp hV
  have hd : ∀ ℓ, ℓ ≠ 0 → V.toNormFamily.dual.trivialSeminorm ℓ = c⁻¹ :=
    fun ℓ hℓ ↦ V.toNormFamily.trivialSeminorm_dual_eq_inv_of_trivialSeminorm_bidual_eq_const
      hc h ℓ hℓ
  rw [V.toNormFamily.dual.norm_eq_const_of_trivialSeminorm_eq_const hd ω z hz,
    Real.log_inv, neg_neg]
  have hs := (V.slopes_eq_neg_log_of_trivialSeminorm_bidual_eq_const hc h hV.1).1
  change Real.log c = -V.slope
  rw [hs, neg_neg]

omit [FiniteDimensional K E] in
open Classical in
omit hN in
/-- A genuine actual rank-two bundle refutes the printed missing-rank
divisor in Remark4.3.62, over any field including characteristic two. -/
theorem exists_rank_two_dual_formula_counterexample :
    ∃ V : AdelicVectorBundle.{u} (singleTrivialPlace K), V.rank = 2 ∧
      V.IsSemistable (hN := ⟨(singleTrivialPlace_normalized K)⟩) ∧
      V.degree (hN := ⟨(singleTrivialPlace_normalized K)⟩) = -2 ∧
      ∃ ℓ : Module.Dual K V, ℓ ≠ 0 ∧
        -Real.log (V.toNormFamily.dual.trivialSeminorm ℓ) = 1 ∧
        -Real.log (V.toNormFamily.dual.trivialSeminorm ℓ) ≠
          -V.degree (hN := ⟨(singleTrivialPlace_normalized K)⟩) := by
  let p : Seminorm (WithAbs (AbsoluteValue.trivial : AbsoluteValue K ℝ)) (Fin 2 → K) :=
    Seminorm.of (fun x ↦ if x = 0 then 0 else Real.exp 1)
      (by
        intro x y
        by_cases hx : x = 0
        · subst x
          simp
        by_cases hy : y = 0
        · subst y
          simp
        by_cases hs : x + y = 0
        · rw [ite_eq_left hs, ite_eq_right hx, ite_eq_right hy]
          exact add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
        rw [ite_eq_right hs, ite_eq_right hx, ite_eq_right hy]
        exact le_add_of_nonneg_right (Real.exp_pos _).le)
      (by
        intro a x
        change (if a.ofAbs • x = 0 then 0 else Real.exp 1) =
          ‖a‖ * (if x = 0 then 0 else Real.exp 1)
        rw [WithAbs.norm_eq_apply_ofAbs]
        by_cases ha : a.ofAbs = 0
        · rw [ha, zero_smul, ite_eq_left rfl, map_zero, zero_mul]
        rw [AbsoluteValue.trivial_apply ha]
        by_cases hx : x = 0
        · subst x
          simp
        rw [ite_eq_right (smul_ne_zero ha hx), ite_eq_right hx, one_mul])
  have hp : ∀ x, p x = 0 ↔ x = 0 := by
    intro x
    change (if x = 0 then 0 else Real.exp 1) = 0 ↔ x = 0
    by_cases hx : x = 0 <;> simp [hx, Real.exp_ne_zero]
  let V := AdelicVectorBundle.ofTrivialNorm p hp
  have h : ∀ x, x ≠ 0 → V.toNormFamily.trivialSeminorm x = Real.exp 1 := by
    intro x hx
    change (NormFamily.ofTrivialNorm p hp).trivialSeminorm x = Real.exp 1
    rw [NormFamily.trivialSeminorm_ofTrivialNorm]
    change (if x = 0 then 0 else Real.exp 1) = Real.exp 1
    rw [ite_eq_right hx]
  have hdim : Module.finrank K (Fin 2 → K) = 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hV := V.isSemistable_of_trivialSeminorm_eq_const
    (hN := ⟨(singleTrivialPlace_normalized K)⟩) (Real.exp_pos _) h
      (by rw [hdim]; norm_num)
  have hd : V.degree (hN := ⟨(singleTrivialPlace_normalized K)⟩) = -2 := by
    rw [V.degree_eq_neg_finrank_mul_log_of_trivialSeminorm_eq_const
      (hN := ⟨(singleTrivialPlace_normalized K)⟩) (Real.exp_pos _) h,
      hdim, Real.log_exp]
    norm_num
  let ℓ : Module.Dual K (Fin 2 → K) := LinearMap.proj 0
  have hℓ : ℓ ≠ 0 := by
    intro hz
    have he := DFunLike.congr_fun hz (fun _ ↦ (1 : K))
    change (1 : K) = 0 at he
    exact one_ne_zero he
  have hl : -Real.log (V.toNormFamily.dual.trivialSeminorm ℓ) = 1 := by
    rw [V.toNormFamily.trivialSeminorm_dual_eq_inv_of_trivialSeminorm_eq_const
      (Real.exp_pos _) h ℓ hℓ, Real.log_inv, Real.log_exp, neg_neg]
  refine ⟨V, hdim, hV, hd, ℓ, hℓ, hl, ?_⟩
  rw [hl, hd]
  norm_num

end AdelicVectorBundle

end

end ArakelovGeometry
