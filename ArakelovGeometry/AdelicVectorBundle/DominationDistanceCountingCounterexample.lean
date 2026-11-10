/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.BasisNorm
public import ArakelovGeometry.AdelicVectorBundle.DominationCountingCounterexample
public import Mathlib.LinearAlgebra.Basis.Fin

/-!
# Dominated norms need not have a dominated distance

The genuine infinite-counting example of Remark 4.1.9, on the same
canonical completed fibres as the preceding domination counterexample.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.CountingDistanceCounterexample

noncomputable section

open AdelicStructure CountingDominationCounterexample

local instance : DecidablePred (fun x : ℚ ↦ x = 0) :=
  fun _ ↦ Classical.propDecidable _

private theorem inverse_rawNorm_bounds (a : ℚ) {x : Plane} (hx : x ≠ 0) :
    1 ≤ (rawNorm a x)⁻¹ ∧ (rawNorm a x)⁻¹ ≤ 2 := by
  simp only [rawNorm, ite_eq_right hx]
  split_ifs <;> norm_num

open Classical in
/-- Inversion of this two-valued norm preserves the triangle inequality. -/
theorem inverse_norm_add_le (a : countingCurve.Ω)
    (x y : (countingCurve.ϕ a).Completion ⊗[ℚ] Plane) :
    (normFamily.norm a (x + y))⁻¹ ≤
      (normFamily.norm a x)⁻¹ + (normFamily.norm a y)⁻¹ := by
  change (rawNorm a (trivialCompletedTensorEquiv ℚ Plane (x + y)))⁻¹ ≤
    (rawNorm a (trivialCompletedTensorEquiv ℚ Plane x))⁻¹ +
      (rawNorm a (trivialCompletedTensorEquiv ℚ Plane y))⁻¹
  by_cases hx : x = 0
  · subst x
    rw [zero_add]
    have hz : trivialCompletedTensorEquiv ℚ Plane
        (0 : (countingCurve.ϕ a).Completion ⊗[ℚ] Plane) = 0 :=
      (LinearEquiv.map_eq_zero_iff _).2 rfl
    rw [hz, rawNorm_zero, inv_zero, zero_add]
  by_cases hy : y = 0
  · subst y
    rw [add_zero]
    have hz : trivialCompletedTensorEquiv ℚ Plane
        (0 : (countingCurve.ϕ a).Completion ⊗[ℚ] Plane) = 0 :=
      (LinearEquiv.map_eq_zero_iff _).2 rfl
    rw [hz, rawNorm_zero, inv_zero, add_zero]
  have hxr : trivialCompletedTensorEquiv ℚ Plane x ≠ 0 :=
    (LinearEquiv.map_eq_zero_iff _).not.mpr hx
  have hyr : trivialCompletedTensorEquiv ℚ Plane y ≠ 0 :=
    (LinearEquiv.map_eq_zero_iff _).not.mpr hy
  have hl := (inverse_rawNorm_bounds a hxr).1
  have hr := (inverse_rawNorm_bounds a hyr).1
  have hs : (rawNorm a (trivialCompletedTensorEquiv ℚ Plane (x + y)))⁻¹ ≤ 2 := by
    by_cases hxy : trivialCompletedTensorEquiv ℚ Plane (x + y) = 0
    · simp [hxy]
    · exact (inverse_rawNorm_bounds a hxy).2
  linarith

open Classical in
/-- Inversion preserves homogeneity over the trivially valued field. -/
theorem inverse_norm_smul (a : countingCurve.Ω)
    (c : (countingCurve.ϕ a).Completion)
    (z : (countingCurve.ϕ a).Completion ⊗[ℚ] Plane) :
    (normFamily.norm a (c • z))⁻¹ = ‖c‖ * (normFamily.norm a z)⁻¹ := by
  have hc : ‖c‖⁻¹ = ‖c‖ := by
    rw [norm_trivialCompletion ℚ]
    by_cases h : trivialCompletionAlgEquiv ℚ c = 0
    · simp [h]
    · simp [AbsoluteValue.trivial_apply h]
  rw [map_smul_eq_mul, mul_inv_rev, hc, mul_comm]

open Classical in
/-- The actual source expensive-line norm, on the same completed fibres.
Real inversion sends zero to zero; all nonzero norms are one or two. -/
def expensiveFamily : NormFamily countingCurve Plane where
  norm a := Seminorm.of (fun z ↦ (normFamily.norm a z)⁻¹)
    (inverse_norm_add_le a) (inverse_norm_smul a)
  norm_eq_zero_iff a z := by
    change (normFamily.norm a z)⁻¹ = 0 ↔ z = 0
    rw [inv_eq_zero, normFamily.norm_eq_zero_iff]

@[simp]
theorem expensiveFamily_norm (a : countingCurve.Ω)
    (z : (countingCurve.ϕ a).Completion ⊗[ℚ] Plane) :
    expensiveFamily.norm a z = (normFamily.norm a z)⁻¹ := rfl

open Classical in
/-- The exact source formula holds on every completed vector. -/
theorem expensiveFamily_norm_completed (a : countingCurve.Ω)
    (z : (countingCurve.ϕ a).Completion ⊗[ℚ] Plane) :
    expensiveFamily.norm a z =
      if trivialCompletedTensorEquiv ℚ Plane z = 0 then 0
      else if (trivialCompletedTensorEquiv ℚ Plane z).2 =
        a * (trivialCompletedTensorEquiv ℚ Plane z).1 then 2 else 1 := by
  rw [expensiveFamily_norm, normFamily_norm]
  simp only [rawNorm]
  split_ifs <;> norm_num

open Classical in
@[simp]
theorem expensiveFamily_norm_rational (a : countingCurve.Ω) (x : Plane) :
    expensiveFamily.norm a ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] x) =
      if x = 0 then 0 else if x.2 = a * x.1 then 2 else 1 := by
  rw [expensiveFamily_norm_completed, trivialCompletedTensorEquiv_one_tmul]

/-- The expensive-line logarithm is the negative of the produced integrable
cheap-line logarithm, including zero. -/
theorem expensiveFamily_logNorm_eq_neg (x : Plane) (a : countingCurve.Ω) :
    expensiveFamily.logNorm x a = -normFamily.logNorm x a :=
  Real.log_inv _

theorem expensiveFamily_integrable_logNorm {x : Plane} (hx : x ≠ 0) :
    Integrable (expensiveFamily.logNorm x) countingCurve.v := by
  have he : expensiveFamily.logNorm x = -normFamily.logNorm x :=
    funext (expensiveFamily_logNorm_eq_neg x)
  rw [he]
  exact (integrable_logNorm hx).neg

theorem expensiveFamily_isUpperDominated : expensiveFamily.IsUpperDominated := by
  intro x hx
  exact ⟨expensiveFamily.logNorm x, expensiveFamily_integrable_logNorm hx,
    Filter.Eventually.of_forall fun _ ↦ le_rfl⟩

private theorem exists_offline_nonzero_evaluation (a : ℚ)
    (ℓ : Module.Dual ℚ Plane) (hℓ : ℓ ≠ 0) :
    ∃ x : Plane, x ≠ 0 ∧ x.2 ≠ a * x.1 ∧ ℓ x ≠ 0 := by
  by_cases hv : ℓ ((0, 1) : Plane) = 0
  · have hu : ℓ ((1, 0) : Plane) ≠ 0 := by
      intro hu
      apply hℓ
      apply LinearMap.ext
      intro x
      change ℓ x = 0
      have he : x = x.1 • ((1, 0) : Plane) + x.2 • ((0, 1) : Plane) := by
        ext <;> simp [smul_eq_mul]
      rw [he, map_add, map_smul, map_smul, hu, hv]
      simp
    refine ⟨(1, a + 1), by simp, by simp, ?_⟩
    have he : ((1, a + 1) : Plane) =
        ((1, 0) : Plane) + (a + 1) • ((0, 1) : Plane) := by
      ext <;> simp [smul_eq_mul]
    rw [he, map_add, map_smul, hv, smul_zero, add_zero]
    exact hu
  · exact ⟨(0, 1), by simp, by simp, hv⟩

open Classical in
/-- The actual completed operator dual is the flat trivial norm. -/
theorem expensiveFamily_dual_norm_rational (a : countingCurve.Ω)
    (ℓ : Module.Dual ℚ Plane) :
    expensiveFamily.dual.norm a
      ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] ℓ) =
      if ℓ = 0 then 0 else 1 := by
  by_cases hℓ : ℓ = 0
  · subst ℓ
    simp
  rw [ite_eq_right hℓ]
  apply le_antisymm
  · apply expensiveFamily.dual_norm_le a _ zero_le_one
    intro z
    rw [completed_eq_one_tmul a z, dualBaseChangeEquiv_tmul_apply_tmul,
      one_mul, one_mul, norm_trivialCompletion ℚ, trivialCompletionAlgEquiv_algebraMap,
      expensiveFamily_norm_rational]
    by_cases hz : trivialCompletedTensorEquiv ℚ Plane z = 0
    · simp [hz]
    · rw [ite_eq_right hz, one_mul]
      have hval : (AbsoluteValue.trivial : AbsoluteValue ℚ ℝ)
          (ℓ (trivialCompletedTensorEquiv ℚ Plane z)) ≤ 1 := by
        by_cases he : ℓ (trivialCompletedTensorEquiv ℚ Plane z) = 0
        · simp [he]
        · rw [AbsoluteValue.trivial_apply he]
      split_ifs <;> linarith
  · obtain ⟨x, hx, hline, he⟩ := exists_offline_nonzero_evaluation a ℓ hℓ
    have hb := expensiveFamily.norm_dual_tmul_apply_tmul_le a
      (1 : (countingCurve.ϕ a).Completion) 1 ℓ x
    have heval : ‖(1 : (countingCurve.ϕ a).Completion) * 1 *
        algebraMap ℚ (countingCurve.ϕ a).Completion (ℓ x)‖ = 1 := by
      rw [one_mul, one_mul, norm_trivialCompletion ℚ, trivialCompletionAlgEquiv_algebraMap,
        AbsoluteValue.trivial_apply he]
    rw [heval, expensiveFamily_norm_rational, ite_eq_right hx, ite_eq_right hline, mul_one] at hb
    exact hb

open Classical in
theorem expensiveFamily_dual_norm_completed (a : countingCurve.Ω)
    (z : (countingCurve.ϕ a).Completion ⊗[ℚ] Module.Dual ℚ Plane) :
    expensiveFamily.dual.norm a z = if z = 0 then 0 else 1 := by
  calc
    _ = expensiveFamily.dual.norm a
        ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ]
          trivialCompletedTensorEquiv ℚ (Module.Dual ℚ Plane) z) :=
      congrArg (expensiveFamily.dual.norm a) (completed_eq_one_tmul a z)
    _ = _ := by
      rw [expensiveFamily_dual_norm_rational]
      simp only [LinearEquiv.map_eq_zero_iff]

theorem expensiveFamily_dual_logNorm_eq_zero (ℓ : Module.Dual ℚ Plane)
    (a : countingCurve.Ω) : expensiveFamily.dual.logNorm ℓ a = 0 := by
  change Real.log _ = 0
  rw [expensiveFamily_dual_norm_rational]
  split_ifs <;> simp

theorem expensiveFamily_dual_isUpperDominated :
    expensiveFamily.dual.IsUpperDominated := by
  intro ℓ _
  exact ⟨0, integrable_zero _ _ _, Filter.Eventually.of_forall fun a ↦ by
    simp only [expensiveFamily_dual_logNorm_eq_zero, Pi.zero_apply, le_refl]⟩

theorem expensiveFamily_isDominated : expensiveFamily.IsDominated :=
  ⟨expensiveFamily_isUpperDominated, expensiveFamily_dual_isUpperDominated⟩

/-- The source's actual coordinate maximum family, defined through the
canonical completed rational basis. -/
def basisFamily : NormFamily countingCurve Plane :=
  NormFamily.ofBasis countingCurve Plane (Module.Basis.finTwoProd ℚ)

open Classical in
theorem basisFamily_norm_rational (a : countingCurve.Ω) (x : Plane) :
    basisFamily.norm a ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] x) =
      if x = 0 then 0 else 1 := by
  by_cases hx : x = 0
  · subst x
    rw [TensorProduct.tmul_zero, ite_eq_left rfl]
    exact (basisFamily.norm_eq_zero_iff a 0).2 rfl
  rw [ite_eq_right hx]
  change (NormFamily.ofBasis countingCurve Plane (Module.Basis.finTwoProd ℚ)).norm a _ = 1
  rw [NormFamily.ofBasis_norm_rational]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    change ‖(AbsoluteValue.trivial : AbsoluteValue ℚ ℝ)
      ((Module.Basis.finTwoProd ℚ).equivFun x i)‖ ≤ 1
    by_cases hi : (Module.Basis.finTwoProd ℚ).equivFun x i = 0
    · simp [hi]
    · rw [AbsoluteValue.trivial_apply hi, norm_one]
  · have hf : (Module.Basis.finTwoProd ℚ).equivFun x ≠ 0 :=
      (LinearEquiv.map_eq_zero_iff _).not.mpr hx
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hf
    have hci : (Module.Basis.finTwoProd ℚ).equivFun x i ≠ 0 := by
      simpa only [Pi.zero_apply] using hi
    have hb := norm_le_pi_norm
      (fun i ↦ (countingCurve.ϕ a) ((Module.Basis.finTwoProd ℚ).equivFun x i)) i
    change ‖(AbsoluteValue.trivial : AbsoluteValue ℚ ℝ)
      ((Module.Basis.finTwoProd ℚ).equivFun x i)‖ ≤ _ at hb
    rw [AbsoluteValue.trivial_apply hci, norm_one] at hb
    exact hb

open Classical in
/-- The canonical completed basis norm is one at every nonzero completed vector. -/
theorem basisFamily_norm_completed (a : countingCurve.Ω)
    (z : (countingCurve.ϕ a).Completion ⊗[ℚ] Plane) :
    basisFamily.norm a z = if z = 0 then 0 else 1 := by
  calc
    _ = basisFamily.norm a ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ]
        trivialCompletedTensorEquiv ℚ Plane z) :=
      congrArg (basisFamily.norm a) (completed_eq_one_tmul a z)
    _ = _ := by
      rw [basisFamily_norm_rational]
      simp only [LinearEquiv.map_eq_zero_iff]

open Classical in
theorem basisFamily_dual_norm_rational (a : countingCurve.Ω)
    (ℓ : Module.Dual ℚ Plane) :
    basisFamily.dual.norm a ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] ℓ) =
      if ℓ = 0 then 0 else 1 := by
  by_cases hℓ : ℓ = 0
  · subst ℓ
    simp
  rw [ite_eq_right hℓ]
  apply le_antisymm
  · apply basisFamily.dual_norm_le a _ zero_le_one
    intro z
    rw [completed_eq_one_tmul a z, dualBaseChangeEquiv_tmul_apply_tmul,
      one_mul, one_mul, norm_trivialCompletion ℚ, trivialCompletionAlgEquiv_algebraMap,
      basisFamily_norm_rational]
    by_cases hz : trivialCompletedTensorEquiv ℚ Plane z = 0
    · simp [hz]
    · rw [ite_eq_right hz, mul_one]
      by_cases he : ℓ (trivialCompletedTensorEquiv ℚ Plane z) = 0
      · simp [he]
      · rw [AbsoluteValue.trivial_apply he]
  · obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hℓ
    have he : ℓ x ≠ 0 := by simpa only [LinearMap.zero_apply] using hx
    have hn : x ≠ 0 := by rintro rfl; simp at he
    have hb := basisFamily.norm_dual_tmul_apply_tmul_le a
      (1 : (countingCurve.ϕ a).Completion) 1 ℓ x
    have heval : ‖(1 : (countingCurve.ϕ a).Completion) * 1 *
        algebraMap ℚ (countingCurve.ϕ a).Completion (ℓ x)‖ = 1 := by
      rw [one_mul, one_mul, norm_trivialCompletion ℚ, trivialCompletionAlgEquiv_algebraMap,
        AbsoluteValue.trivial_apply he]
    rw [heval, basisFamily_norm_rational, ite_eq_right hn, mul_one] at hb
    exact hb

theorem basisFamily_isDominated : basisFamily.IsDominated := by
  constructor
  · intro x _
    refine ⟨0, integrable_zero _ _ _, Filter.Eventually.of_forall ?_⟩
    intro a
    change Real.log _ ≤ 0
    rw [basisFamily_norm_rational]
    split_ifs <;> simp
  · intro ℓ _
    refine ⟨0, integrable_zero _ _ _, Filter.Eventually.of_forall ?_⟩
    intro a
    change Real.log _ ≤ 0
    rw [basisFamily_dual_norm_rational]
    split_ifs <;> simp

open Classical in
/-- The genuine completed-fibre supremum distance is the positive constant log two. -/
theorem expensiveFamily_localDist_basisFamily (a : countingCurve.Ω) :
    expensiveFamily.localDist basisFamily a = Real.log 2 := by
  have hp : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  apply le_antisymm
  · apply expensiveFamily.localDist_le basisFamily a
    intro z
    rw [expensiveFamily_norm_completed, basisFamily_norm_completed]
    have he : trivialCompletedTensorEquiv ℚ Plane z = 0 ↔ z = 0 :=
      LinearEquiv.map_eq_zero_iff _
    simp only [he]
    split_ifs <;> simp [abs_of_nonneg hp, hp]
  · have hb := expensiveFamily.log_norm_sub_le_localDist basisFamily a
      ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] ((1, a) : Plane))
    rw [expensiveFamily_norm_rational, basisFamily_norm_rational] at hb
    have hn : ((1, a) : Plane) ≠ 0 := by simp
    simpa [hn, abs_of_nonneg hp] using hb

/-- No integrable upper envelope exists for the actual distance on infinite counting measure. -/
theorem localDist_not_hasIntegrableUpperBound :
    ¬ HasIntegrableUpperBound (expensiveFamily.localDist basisFamily) countingCurve.v := by
  rintro ⟨A, hA, hbound⟩
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : Integrable (fun _ : countingCurve.Ω ↦ Real.log 2) countingCurve.v := by
    apply hA.mono' measurable_const.aestronglyMeasurable
    filter_upwards [hbound] with a ha
    rw [expensiveFamily_localDist_basisFamily] at ha
    simpa only [Real.norm_eq_abs, abs_of_pos hp] using ha
  have hs := integrable_count_iff.mp hc
  have hz : ‖Real.log 2‖ = 0 := (summable_const_iff _).mp hs
  exact hp.ne' (norm_eq_zero.mp hz)

/-- Both actual source families are dominated, while their distance is not.
No upper-distance conclusion or norm comparison is supplied as a premise. -/
theorem dominated_pair_with_non_dominated_distance :
    expensiveFamily.IsDominated ∧ basisFamily.IsDominated ∧
      ¬ HasIntegrableUpperBound (expensiveFamily.localDist basisFamily) countingCurve.v :=
  ⟨expensiveFamily_isDominated, basisFamily_isDominated,
    localDist_not_hasIntegrableUpperBound⟩

end

end ArakelovGeometry.CountingDistanceCounterexample
