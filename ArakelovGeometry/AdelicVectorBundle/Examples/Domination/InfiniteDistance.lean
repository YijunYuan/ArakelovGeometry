/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Domination.InfiniteCounting

import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Dominated norms need not have a dominated distance

The full arbitrary infinite-field counting example of Remark 4.1.9, on the same
canonical completed fibres as the preceding domination counterexample.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.InfiniteCountingDistanceCounterexample

noncomputable section

open AdelicStructure InfiniteCountingDominationCounterexample

universe u

variable (K : Type u) [Field K]

local instance : MeasurableSpace K := (countingCurve K).A

local instance : DecidablePred (fun x : K ↦ x = 0) :=
  fun _ ↦ Classical.propDecidable _

private theorem inverse_rawNorm_bounds (a : K) {x : (Plane K)} (hx : x ≠ 0) :
    1 ≤ ((rawNorm K) a x)⁻¹ ∧ ((rawNorm K) a x)⁻¹ ≤ 2 := by
  simp only [rawNorm, ite_eq_right hx]
  split_ifs <;> norm_num

open Classical in
/-- Inversion of this two-valued norm preserves the triangle inequality. -/
theorem inverse_norm_add_le (a : (countingCurve K).Ω)
    (x y : ((countingCurve K).ϕ a).Completion ⊗[K] (Plane K)) :
    ((normFamily K).norm a (x + y))⁻¹ ≤
      ((normFamily K).norm a x)⁻¹ + ((normFamily K).norm a y)⁻¹ := by
  change ((rawNorm K) a (trivialCompletedTensorEquiv K (Plane K) (x + y)))⁻¹ ≤
    ((rawNorm K) a (trivialCompletedTensorEquiv K (Plane K) x))⁻¹ +
      ((rawNorm K) a (trivialCompletedTensorEquiv K (Plane K) y))⁻¹
  by_cases hx : x = 0
  · subst x
    rw [zero_add]
    have hz : trivialCompletedTensorEquiv K (Plane K)
        (0 : ((countingCurve K).ϕ a).Completion ⊗[K] (Plane K)) = 0 :=
      (LinearEquiv.map_eq_zero_iff _).2 rfl
    rw [hz, (rawNorm_zero K), inv_zero, zero_add]
  by_cases hy : y = 0
  · subst y
    rw [add_zero]
    have hz : trivialCompletedTensorEquiv K (Plane K)
        (0 : ((countingCurve K).ϕ a).Completion ⊗[K] (Plane K)) = 0 :=
      (LinearEquiv.map_eq_zero_iff _).2 rfl
    rw [hz, (rawNorm_zero K), inv_zero, add_zero]
  have hxr : trivialCompletedTensorEquiv K (Plane K) x ≠ 0 :=
    (LinearEquiv.map_eq_zero_iff _).not.mpr hx
  have hyr : trivialCompletedTensorEquiv K (Plane K) y ≠ 0 :=
    (LinearEquiv.map_eq_zero_iff _).not.mpr hy
  have hl := ((inverse_rawNorm_bounds K) a hxr).1
  have hr := ((inverse_rawNorm_bounds K) a hyr).1
  have hs : ((rawNorm K) a (trivialCompletedTensorEquiv K (Plane K) (x + y)))⁻¹ ≤ 2 := by
    by_cases hxy : trivialCompletedTensorEquiv K (Plane K) (x + y) = 0
    · simp [hxy]
    · exact ((inverse_rawNorm_bounds K) a hxy).2
  linarith

open Classical in
/-- Inversion preserves homogeneity over the trivially valued field. -/
theorem inverse_norm_smul (a : (countingCurve K).Ω)
    (c : ((countingCurve K).ϕ a).Completion)
    (z : ((countingCurve K).ϕ a).Completion ⊗[K] (Plane K)) :
    ((normFamily K).norm a (c • z))⁻¹ = ‖c‖ * ((normFamily K).norm a z)⁻¹ := by
  have hc : ‖c‖⁻¹ = ‖c‖ := by
    rw [norm_trivialCompletion K]
    by_cases h : trivialCompletionAlgEquiv K c = 0
    · simp [h]
    · simp [AbsoluteValue.trivial_apply h]
  rw [map_smul_eq_mul, mul_inv_rev, hc, mul_comm]

open Classical in
/-- The actual source expensive-line norm, on the same completed fibres.
Real inversion sends zero to zero; all nonzero norms are one or two. -/
def expensiveFamily : NormFamily (countingCurve K) (Plane K) where
  norm a := Seminorm.of (fun z ↦ ((normFamily K).norm a z)⁻¹)
    ((inverse_norm_add_le K) a) ((inverse_norm_smul K) a)
  norm_eq_zero_iff a z := by
    change ((normFamily K).norm a z)⁻¹ = 0 ↔ z = 0
    rw [inv_eq_zero, (normFamily K).norm_eq_zero_iff]

@[simp]
theorem expensiveFamily_norm (a : (countingCurve K).Ω)
    (z : ((countingCurve K).ϕ a).Completion ⊗[K] (Plane K)) :
    (expensiveFamily K).norm a z = ((normFamily K).norm a z)⁻¹ := rfl

open Classical in
/-- The exact source formula holds on every completed vector. -/
theorem expensiveFamily_norm_completed (a : (countingCurve K).Ω)
    (z : ((countingCurve K).ϕ a).Completion ⊗[K] (Plane K)) :
    (expensiveFamily K).norm a z =
      if trivialCompletedTensorEquiv K (Plane K) z = 0 then 0
      else if (trivialCompletedTensorEquiv K (Plane K) z).2 =
        a * (trivialCompletedTensorEquiv K (Plane K) z).1 then 2 else 1 := by
  rw [(expensiveFamily_norm K), (normFamily_norm K)]
  simp only [rawNorm]
  split_ifs <;> norm_num

open Classical in
@[simp]
theorem expensiveFamily_norm_rational (a : (countingCurve K).Ω) (x : (Plane K)) :
    (expensiveFamily K).norm a ((1 : ((countingCurve K).ϕ a).Completion) ⊗ₜ[K] x) =
      if x = 0 then 0 else if x.2 = a * x.1 then 2 else 1 := by
  rw [(expensiveFamily_norm_completed K), trivialCompletedTensorEquiv_one_tmul]

/-- The expensive-line logarithm is the negative of the produced integrable
cheap-line logarithm, including zero. -/
theorem expensiveFamily_logNorm_eq_neg (x : (Plane K)) (a : (countingCurve K).Ω) :
    (expensiveFamily K).logNorm x a = -(normFamily K).logNorm x a :=
  Real.log_inv _

theorem expensiveFamily_integrable_logNorm {x : (Plane K)} (hx : x ≠ 0) :
    Integrable ((expensiveFamily K).logNorm x) (countingCurve K).v := by
  have he : (expensiveFamily K).logNorm x = -(normFamily K).logNorm x :=
    funext ((expensiveFamily_logNorm_eq_neg K) x)
  rw [he]
  exact ((integrable_logNorm K) hx).neg

theorem expensiveFamily_isUpperDominated : (expensiveFamily K).IsUpperDominated := by
  constructor
  intro x hx
  exact ⟨(expensiveFamily K).logNorm x, (expensiveFamily_integrable_logNorm K) hx,
    Filter.Eventually.of_forall fun _ ↦ le_rfl⟩

private theorem exists_offline_nonzero_evaluation (a : K)
    (ℓ : Module.Dual K (Plane K)) (hℓ : ℓ ≠ 0) :
    ∃ x : (Plane K), x ≠ 0 ∧ x.2 ≠ a * x.1 ∧ ℓ x ≠ 0 := by
  by_cases hv : ℓ ((0, 1) : (Plane K)) = 0
  · have hu : ℓ ((1, 0) : (Plane K)) ≠ 0 := by
      intro hu
      apply hℓ
      apply LinearMap.ext
      intro x
      change ℓ x = 0
      have he : x = x.1 • ((1, 0) : (Plane K)) + x.2 • ((0, 1) : (Plane K)) := by
        ext <;> simp [smul_eq_mul]
      rw [he, map_add, map_smul, map_smul, hu, hv]
      simp
    refine ⟨(1, a + 1), by simp, by simp, ?_⟩
    have he : ((1, a + 1) : (Plane K)) =
        ((1, 0) : (Plane K)) + (a + 1) • ((0, 1) : (Plane K)) := by
      ext <;> simp [smul_eq_mul]
    rw [he, map_add, map_smul, hv, smul_zero, add_zero]
    exact hu
  · exact ⟨(0, 1), by simp, by simp, hv⟩

open Classical in
/-- The actual completed operator dual is the flat trivial norm. -/
theorem expensiveFamily_dual_norm_rational (a : (countingCurve K).Ω)
    (ℓ : Module.Dual K (Plane K)) :
    (expensiveFamily K).dual.norm a
      ((1 : ((countingCurve K).ϕ a).Completion) ⊗ₜ[K] ℓ) =
      if ℓ = 0 then 0 else 1 := by
  by_cases hℓ : ℓ = 0
  · subst ℓ
    simp
  rw [ite_eq_right hℓ]
  apply le_antisymm
  · apply (expensiveFamily K).dual_norm_le a _ zero_le_one
    intro z
    rw [(completed_eq_one_tmul K) a z, dualBaseChangeEquiv_tmul_apply_tmul,
      one_mul, one_mul, norm_trivialCompletion K, trivialCompletionAlgEquiv_algebraMap,
      (expensiveFamily_norm_rational K)]
    by_cases hz : trivialCompletedTensorEquiv K (Plane K) z = 0
    · simp [hz]
    · rw [ite_eq_right hz, one_mul]
      have hval : (AbsoluteValue.trivial : AbsoluteValue K ℝ)
          (ℓ (trivialCompletedTensorEquiv K (Plane K) z)) ≤ 1 := by
        by_cases he : ℓ (trivialCompletedTensorEquiv K (Plane K) z) = 0
        · simp [he]
        · rw [AbsoluteValue.trivial_apply he]
      split_ifs <;> linarith
  · obtain ⟨x, hx, hline, he⟩ := (exists_offline_nonzero_evaluation K) a ℓ hℓ
    have hb := (expensiveFamily K).norm_dual_tmul_apply_tmul_le a
      (1 : ((countingCurve K).ϕ a).Completion) 1 ℓ x
    have heval : ‖(1 : ((countingCurve K).ϕ a).Completion) * 1 *
        algebraMap K ((countingCurve K).ϕ a).Completion (ℓ x)‖ = 1 := by
      rw [one_mul, one_mul, norm_trivialCompletion K, trivialCompletionAlgEquiv_algebraMap,
        AbsoluteValue.trivial_apply he]
    rw [heval, (expensiveFamily_norm_rational K), ite_eq_right hx, ite_eq_right hline,
      mul_one] at hb
    exact hb

open Classical in
theorem expensiveFamily_dual_norm_completed (a : (countingCurve K).Ω)
    (z : ((countingCurve K).ϕ a).Completion ⊗[K] Module.Dual K (Plane K)) :
    (expensiveFamily K).dual.norm a z = if z = 0 then 0 else 1 := by
  calc
    _ = (expensiveFamily K).dual.norm a
        ((1 : ((countingCurve K).ϕ a).Completion) ⊗ₜ[K]
          trivialCompletedTensorEquiv K (Module.Dual K (Plane K)) z) :=
      congrArg ((expensiveFamily K).dual.norm a) ((completed_eq_one_tmul K) a z)
    _ = _ := by
      rw [(expensiveFamily_dual_norm_rational K)]
      simp only [LinearEquiv.map_eq_zero_iff]

theorem expensiveFamily_dual_logNorm_eq_zero (ℓ : Module.Dual K (Plane K))
    (a : (countingCurve K).Ω) : (expensiveFamily K).dual.logNorm ℓ a = 0 := by
  change Real.log _ = 0
  rw [(expensiveFamily_dual_norm_rational K)]
  split_ifs <;> simp

theorem expensiveFamily_dual_isUpperDominated :
    (expensiveFamily K).dual.IsUpperDominated := by
  constructor
  intro ℓ _
  exact ⟨0, integrable_zero _ _ _, Filter.Eventually.of_forall fun a ↦ by
    simp only [(expensiveFamily_dual_logNorm_eq_zero K), Pi.zero_apply, le_refl]⟩

theorem expensiveFamily_isDominated : (expensiveFamily K).IsDominated :=
  ⟨(expensiveFamily_isUpperDominated K), (expensiveFamily_dual_isUpperDominated K)⟩

/-- The source's actual coordinate maximum family, defined through the
canonical completed base-field basis. -/
def basisFamily : NormFamily (countingCurve K) (Plane K) :=
  NormFamily.ofBasis (countingCurve K) (Plane K) (Module.Basis.finTwoProd K)

open Classical in
theorem basisFamily_norm_rational (a : (countingCurve K).Ω) (x : (Plane K)) :
    (basisFamily K).norm a ((1 : ((countingCurve K).ϕ a).Completion) ⊗ₜ[K] x) =
      if x = 0 then 0 else 1 := by
  by_cases hx : x = 0
  · subst x
    rw [TensorProduct.tmul_zero, ite_eq_left rfl]
    exact ((basisFamily K).norm_eq_zero_iff a 0).2 rfl
  rw [ite_eq_right hx]
  change (NormFamily.ofBasis (countingCurve K) (Plane K) (Module.Basis.finTwoProd K)).norm a _ = 1
  rw [NormFamily.ofBasis_norm_rational]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    change ‖(AbsoluteValue.trivial : AbsoluteValue K ℝ)
      ((Module.Basis.finTwoProd K).equivFun x i)‖ ≤ 1
    by_cases hi : (Module.Basis.finTwoProd K).equivFun x i = 0
    · simp [hi]
    · rw [AbsoluteValue.trivial_apply hi, norm_one]
  · have hf : (Module.Basis.finTwoProd K).equivFun x ≠ 0 :=
      (LinearEquiv.map_eq_zero_iff _).not.mpr hx
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hf
    have hci : (Module.Basis.finTwoProd K).equivFun x i ≠ 0 := by
      simpa only [Pi.zero_apply] using hi
    have hb := norm_le_pi_norm
      (fun i ↦ ((countingCurve K).ϕ a) ((Module.Basis.finTwoProd K).equivFun x i)) i
    change ‖(AbsoluteValue.trivial : AbsoluteValue K ℝ)
      ((Module.Basis.finTwoProd K).equivFun x i)‖ ≤ _ at hb
    rw [AbsoluteValue.trivial_apply hci, norm_one] at hb
    exact hb

open Classical in
/-- The canonical completed basis norm is one at every nonzero completed vector. -/
theorem basisFamily_norm_completed (a : (countingCurve K).Ω)
    (z : ((countingCurve K).ϕ a).Completion ⊗[K] (Plane K)) :
    (basisFamily K).norm a z = if z = 0 then 0 else 1 := by
  calc
    _ = (basisFamily K).norm a ((1 : ((countingCurve K).ϕ a).Completion) ⊗ₜ[K]
        trivialCompletedTensorEquiv K (Plane K) z) :=
      congrArg ((basisFamily K).norm a) ((completed_eq_one_tmul K) a z)
    _ = _ := by
      rw [(basisFamily_norm_rational K)]
      simp only [LinearEquiv.map_eq_zero_iff]

open Classical in
theorem basisFamily_dual_norm_rational (a : (countingCurve K).Ω)
    (ℓ : Module.Dual K (Plane K)) :
    (basisFamily K).dual.norm a ((1 : ((countingCurve K).ϕ a).Completion) ⊗ₜ[K] ℓ) =
      if ℓ = 0 then 0 else 1 := by
  by_cases hℓ : ℓ = 0
  · subst ℓ
    simp
  rw [ite_eq_right hℓ]
  apply le_antisymm
  · apply (basisFamily K).dual_norm_le a _ zero_le_one
    intro z
    rw [(completed_eq_one_tmul K) a z, dualBaseChangeEquiv_tmul_apply_tmul,
      one_mul, one_mul, norm_trivialCompletion K, trivialCompletionAlgEquiv_algebraMap,
      (basisFamily_norm_rational K)]
    by_cases hz : trivialCompletedTensorEquiv K (Plane K) z = 0
    · simp [hz]
    · rw [ite_eq_right hz, mul_one]
      by_cases he : ℓ (trivialCompletedTensorEquiv K (Plane K) z) = 0
      · simp [he]
      · rw [AbsoluteValue.trivial_apply he]
  · obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hℓ
    have he : ℓ x ≠ 0 := by simpa only [LinearMap.zero_apply] using hx
    have hn : x ≠ 0 := by rintro rfl; simp at he
    have hb := (basisFamily K).norm_dual_tmul_apply_tmul_le a
      (1 : ((countingCurve K).ϕ a).Completion) 1 ℓ x
    have heval : ‖(1 : ((countingCurve K).ϕ a).Completion) * 1 *
        algebraMap K ((countingCurve K).ϕ a).Completion (ℓ x)‖ = 1 := by
      rw [one_mul, one_mul, norm_trivialCompletion K, trivialCompletionAlgEquiv_algebraMap,
        AbsoluteValue.trivial_apply he]
    rw [heval, (basisFamily_norm_rational K), ite_eq_right hn, mul_one] at hb
    exact hb

theorem basisFamily_isDominated : (basisFamily K).IsDominated := by
  constructor
  · constructor
    intro x _
    refine ⟨0, integrable_zero _ _ _, Filter.Eventually.of_forall ?_⟩
    intro a
    change Real.log _ ≤ 0
    rw [(basisFamily_norm_rational K)]
    split_ifs <;> simp
  · constructor
    intro ℓ _
    refine ⟨0, integrable_zero _ _ _, Filter.Eventually.of_forall ?_⟩
    intro a
    change Real.log _ ≤ 0
    rw [(basisFamily_dual_norm_rational K)]
    split_ifs <;> simp

open Classical in
/-- The genuine completed-fibre supremum distance is the positive constant log two. -/
theorem expensiveFamily_localDist_basisFamily (a : (countingCurve K).Ω) :
    (expensiveFamily K).localDist (basisFamily K) a = Real.log 2 := by
  have hp : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  apply le_antisymm
  · apply (expensiveFamily K).localDist_le (basisFamily K) a
    intro z
    rw [(expensiveFamily_norm_completed K), (basisFamily_norm_completed K)]
    have he : trivialCompletedTensorEquiv K (Plane K) z = 0 ↔ z = 0 :=
      LinearEquiv.map_eq_zero_iff _
    simp only [he]
    split_ifs <;> simp [abs_of_nonneg hp, hp]
  · have hb := (expensiveFamily K).log_norm_sub_le_localDist (basisFamily K) a
      ((1 : ((countingCurve K).ϕ a).Completion) ⊗ₜ[K] ((1, a) : (Plane K)))
    rw [(expensiveFamily_norm_rational K), (basisFamily_norm_rational K)] at hb
    have hn : ((1, a) : (Plane K)) ≠ 0 := by simp
    simpa [hn, abs_of_nonneg hp] using hb

open Classical in
/-- Every actual completed basis-dual functional has the flat trivial norm. -/
theorem basisFamily_dual_norm_completed (a : (countingCurve K).Ω)
    (z : ((countingCurve K).ϕ a).Completion ⊗[K] Module.Dual K (Plane K)) :
    (basisFamily K).dual.norm a z = if z = 0 then 0 else 1 := by
  calc
    _ = (basisFamily K).dual.norm a
        ((1 : ((countingCurve K).ϕ a).Completion) ⊗ₜ[K]
          trivialCompletedTensorEquiv K (Module.Dual K (Plane K)) z) :=
      congrArg ((basisFamily K).dual.norm a) (completed_eq_one_tmul K a z)
    _ = _ := by
      rw [basisFamily_dual_norm_rational K]
      simp only [LinearEquiv.map_eq_zero_iff]

/-- A literal actual completed triangle witnesses failure of ultrametricity
in every field characteristic, with no vector or norm equality assumed. -/
theorem expensiveFamily_nonultrametric_witness (a : (countingCurve K).Ω) :
    ∃ z w : ((countingCurve K).ϕ a).Completion ⊗[K] Plane K,
      max ((expensiveFamily K).norm a z) ((expensiveFamily K).norm a w) <
        (expensiveFamily K).norm a (z + w) := by
  classical
  refine ⟨(1 : ((countingCurve K).ϕ a).Completion) ⊗ₜ[K] ((1, a + 1) : Plane K),
    (1 : ((countingCurve K).ϕ a).Completion) ⊗ₜ[K] ((0, -1) : Plane K), ?_⟩
  have he : ((1, a + 1) : Plane K) + ((0, -1) : Plane K) = ((1, a) : Plane K) := by
    ext <;> simp
  rw [← TensorProduct.tmul_add, he, expensiveFamily_norm_rational K,
    expensiveFamily_norm_rational K, expensiveFamily_norm_rational K]
  have hline : a + 1 ≠ a := by
    intro h
    have hz : (1 : K) = 0 := add_left_cancel (show a + 1 = a + 0 by
      rw [add_zero]
      exact h)
    exact one_ne_zero hz
  simp [hline]

variable [Infinite K]

/-- No integrable upper envelope exists for the actual distance on infinite counting measure. -/
theorem localDist_not_hasIntegrableUpperBound :
    ¬ HasIntegrableUpperBound ((expensiveFamily K).localDist (basisFamily K))
      (countingCurve K).v := by
  rintro ⟨A, hA, hbound⟩
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : Integrable (fun _ : (countingCurve K).Ω ↦ Real.log 2) (countingCurve K).v := by
    apply hA.mono' measurable_const.aestronglyMeasurable
    filter_upwards [hbound] with a ha
    rw [(expensiveFamily_localDist_basisFamily K)] at ha
    simpa only [Real.norm_eq_abs, abs_of_pos hp] using ha
  have hs := integrable_count_iff.mp hc
  have hz : ‖Real.log 2‖ = 0 := (summable_const_iff _).mp hs
  exact hp.ne' (norm_eq_zero.mp hz)

/-- Both actual source families are dominated, while their distance is not.
No upper-distance conclusion or norm comparison is supplied as a premise. -/
theorem dominated_pair_with_non_dominated_distance :
    (expensiveFamily K).IsDominated ∧ (basisFamily K).IsDominated ∧
      ¬ HasIntegrableUpperBound ((expensiveFamily K).localDist (basisFamily K))
        (countingCurve K).v :=
  ⟨(expensiveFamily_isDominated K), (basisFamily_isDominated K),
    (localDist_not_hasIntegrableUpperBound K)⟩

/-- The full source example produces the proper infinite-field curve,
both actual dominated norm families, and their failure of any integrable
distance envelope. -/
theorem exists_dominated_pair_with_non_dominated_distance :
    ∃ S : AdelicStructure.{u, u} K, S.IsProper ∧
      ∃ ξ η : NormFamily S (Plane K),
        ξ.IsDominated ∧ η.IsDominated ∧
          ¬ HasIntegrableUpperBound (ξ.localDist η) S.v :=
  ⟨countingCurve K, inferInstance, expensiveFamily K, basisFamily K,
    dominated_pair_with_non_dominated_distance K⟩

end

end ArakelovGeometry.InfiniteCountingDistanceCounterexample
