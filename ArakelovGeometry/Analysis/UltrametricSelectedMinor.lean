/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.UltrametricCoordinateSplit

/-!
# Residual minima for a prescribed normalized minor

The same selected minor can be used across a measurable family of absolute
values. This module computes the residual minimum from its actual normalized
coefficient bounds; the minor is not reselected after completion.
-/

noncomputable section
open scoped Matrix

namespace ArakelovGeometry.Matrix

variable {L m n : Type*} [NormedField L] [IsUltrametricDist L]
  [Fintype m] [Fintype n] [DecidableEq n]

/-- Every prescribed nonsingular minor with normalized entries of norm at most
one gives the minimum representative modulo the actual column space. -/
theorem residual_minimum_of_normalized_minor (A : Matrix m n L) (I : n → m)
    (hd : (A.submatrix I id).det ≠ 0)
    (hid : (A * (A.submatrix I id)⁻¹).submatrix I id = 1)
    (hB : ∀ i j, ‖(A * (A.submatrix I id)⁻¹) i j‖ ≤ 1) (x : m → L) :
    let p := x - (A * (A.submatrix I id)⁻¹) *ᵥ (x ∘ I)
    (∀ j, p (I j) = 0) ∧
      (∀ a : n → L, ‖p‖ ≤ ‖x + A *ᵥ a‖) ∧
      ∃ a : n → L, x + A *ᵥ a = p := by
  let C := A.submatrix I id
  let B := A * C⁻¹
  let p := x - B *ᵥ (x ∘ I)
  have hunit : IsUnit C.det := isUnit_iff_ne_zero.mpr hd
  have hBA : B * C = A := by
    dsimp only [B]
    rw [_root_.Matrix.mul_assoc, _root_.Matrix.nonsing_inv_mul C hunit,
      _root_.Matrix.mul_one]
  have hpivot (a : n → L) : (B *ᵥ a) ∘ I = a := by
    have h : B.submatrix I id *ᵥ a = a := by rw [hid, _root_.Matrix.one_mulVec]
    exact h
  have hcontract (a : n → L) : ‖B *ᵥ a‖ ≤ ‖a‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr
    intro i
    change ‖∑ j, B i j * a j‖ ≤ ‖a‖
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg a)
    intro j _
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hB i j) (norm_nonneg (a j))).trans
      (by simpa using norm_le_pi_norm a j)
  have hp : ∀ j, p (I j) = 0 := by
    intro j
    change x (I j) - (B *ᵥ (x ∘ I)) (I j) = 0
    have hj : (B *ᵥ (x ∘ I)) (I j) = x (I j) := congrFun (hpivot (x ∘ I)) j
    rw [hj]
    exact sub_self _
  refine ⟨hp, ?_, ?_⟩
  · intro a
    let y := x + A *ᵥ a
    have hy : y - B *ᵥ (y ∘ I) = p := by
      have hA : (A *ᵥ a) ∘ I = C *ᵥ a := rfl
      have hcomp : y ∘ I = x ∘ I + C *ᵥ a := by
        ext j
        exact congrFun (congrArg (fun z : n → L ↦ (x ∘ I) + z) hA) j
      rw [hcomp, _root_.Matrix.mulVec_add, _root_.Matrix.mulVec_mulVec a B C, hBA]
      dsimp only [y, p]
      abel
    have hpivle : ‖y ∘ I‖ ≤ ‖y‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr
      intro j
      exact norm_le_pi_norm y (I j)
    change ‖p‖ ≤ ‖y‖
    rw [← hy]
    have hsub : ‖y - B *ᵥ (y ∘ I)‖ ≤ max ‖y‖ ‖B *ᵥ (y ∘ I)‖ := by
      simpa only [sub_eq_add_neg, norm_neg] using
        IsUltrametricDist.norm_add_le_max y (-(B *ᵥ (y ∘ I)))
    exact hsub.trans (max_le le_rfl ((hcontract _).trans hpivle))
  · refine ⟨-(C⁻¹ *ᵥ (x ∘ I)), ?_⟩
    change x + A *ᵥ (-(C⁻¹ *ᵥ (x ∘ I))) = x - B *ᵥ (x ∘ I)
    rw [_root_.Matrix.mulVec_neg]
    simp only [B, _root_.Matrix.mulVec_mulVec, sub_eq_add_neg]

end ArakelovGeometry.Matrix
