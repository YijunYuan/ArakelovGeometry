/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import ArakelovGeometry.LinearAlgebra.MaximalMinor
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Topology.MetricSpace.Ultra.Pi

/-!
# Actual ultrametric coordinate splitting

An actual maximal row minor gives an isometric splitting of the coordinate
maximum norm. The canonical residual attains the smallest norm among all
representatives modulo the original column space. No adapted basis or norm
identity is supplied as a hypothesis.
-/

@[expose] public section

noncomputable section

open scoped Matrix

namespace ArakelovGeometry.Matrix

variable {L m n : Type*} [NormedField L] [IsUltrametricDist L]
  [Fintype m] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
private theorem mulVec_norm_le (B : Matrix m n L) (hB : ∀ i j, ‖B i j‖ ≤ 1)
    (a : n → L) : ‖B *ᵥ a‖ ≤ ‖a‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr
  intro i
  change ‖∑ j, B i j * a j‖ ≤ ‖a‖
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg a)
  intro j _
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (hB i j) (norm_nonneg (a j))).trans
    (by simpa using norm_le_pi_norm a j)

omit [IsUltrametricDist L] [Fintype m] in
private theorem pivot_mulVec (B : Matrix m n L) (I : n → m)
    (hI : B.submatrix I id = 1) (a : n → L) : (B *ᵥ a) ∘ I = a := by
  have hm : B.submatrix I id *ᵥ a = a := by rw [hI, _root_.Matrix.one_mulVec]
  exact hm

private theorem split_norm_eq (B : Matrix m n L) (I : n → m)
    (hI : B.submatrix I id = 1) (hB : ∀ i j, ‖B i j‖ ≤ 1)
    (a : n → L) (b : m → L) (hb : ∀ j, b (I j) = 0) :
    ‖B *ᵥ a + b‖ = max ‖a‖ ‖b‖ := by
  have ha : ‖a‖ ≤ ‖B *ᵥ a + b‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    have he : (B *ᵥ a + b) (I j) = a j := by
      simp only [Pi.add_apply, hb j, add_zero]
      exact congrFun (pivot_mulVec B I hI a) j
    rw [← he]
    exact norm_le_pi_norm _ _
  have hcontract := mulVec_norm_le B hB a
  have hble : ‖b‖ ≤ ‖B *ᵥ a + b‖ := by
    have he : b = (B *ᵥ a + b) - B *ᵥ a := by simp
    have hs : ‖(B *ᵥ a + b) - B *ᵥ a‖ ≤ max ‖B *ᵥ a + b‖ ‖B *ᵥ a‖ := by
      simpa [sub_eq_add_neg] using
        IsUltrametricDist.norm_add_le_max (B *ᵥ a + b) (-(B *ᵥ a))
    exact (congrArg norm he).trans_le (hs.trans (max_le le_rfl (hcontract.trans ha)))
  apply le_antisymm
  · exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le_max hcontract le_rfl)
  · exact max_le ha hble

/-- A maximal minor produces an actual isometric splitting of every coordinate vector. -/
theorem exists_maximal_minor_split (A : Matrix m n L) (hA : LinearIndependent L A.col) :
    ∃ I : n → m, Function.Injective I ∧ (A.submatrix I id).det ≠ 0 ∧
      ∀ (a : n → L) (b : m → L), (∀ j, b (I j) = 0) →
        ‖(A * (A.submatrix I id)⁻¹) *ᵥ a + b‖ = max ‖a‖ ‖b‖ := by
  obtain ⟨I, hi, hd, _, hid, hB⟩ :=
    exists_maximal_row_minor_normalization A hA (NormedField.toAbsoluteValue L)
  exact ⟨I, hi, hd, fun a b hb ↦ split_norm_eq _ I hid hB a b hb⟩

/-- The residual supplied by actual maximal-minor normalization attains the quotient norm. -/
theorem exists_maximal_minor_quotient_minimum (A : Matrix m n L)
    (hA : LinearIndependent L A.col) :
    ∃ I : n → m, Function.Injective I ∧ (A.submatrix I id).det ≠ 0 ∧
      ∀ x : m → L,
        let p := x - (A * (A.submatrix I id)⁻¹) *ᵥ (x ∘ I)
        (∀ j, p (I j) = 0) ∧ ‖p‖ ≤ ‖x‖ ∧
        (∀ a : n → L, ‖p‖ ≤ ‖x + A *ᵥ a‖) ∧
        ∃ a : n → L, x + A *ᵥ a = p := by
  obtain ⟨I, hi, hd, _, hid, hB⟩ :=
    exists_maximal_row_minor_normalization A hA (NormedField.toAbsoluteValue L)
  let C := A.submatrix I id
  let B := A * C⁻¹
  have hunit : IsUnit C.det := isUnit_iff_ne_zero.mpr hd
  have hBA : B * C = A := by
    dsimp [B]
    rw [_root_.Matrix.mul_assoc, _root_.Matrix.nonsing_inv_mul C hunit,
      _root_.Matrix.mul_one]
  refine ⟨I, hi, hd, ?_⟩
  intro x
  let p := x - B *ᵥ (x ∘ I)
  have hp : ∀ j, p (I j) = 0 := by
    intro j
    change x (I j) - (B *ᵥ (x ∘ I)) (I j) = 0
    have hj : (B *ᵥ (x ∘ I)) (I j) = x (I j) :=
      congrFun (pivot_mulVec B I hid (x ∘ I)) j
    rw [hj]
    exact sub_self _
  have hx : B *ᵥ (x ∘ I) + p = x := by dsimp [p]; abel
  have hmin : ∀ a : n → L, ‖p‖ ≤ ‖x + A *ᵥ a‖ := by
    intro a
    have he : x + A *ᵥ a = B *ᵥ ((x ∘ I) + C *ᵥ a) + p := by
      rw [_root_.Matrix.mulVec_add,
        _root_.Matrix.mulVec_mulVec a B C, hBA, add_right_comm, hx]
    rw [he, split_norm_eq B I hid hB _ p hp]
    exact le_max_right _ _
  refine ⟨hp, ?_, hmin, ?_⟩
  · have hz := hmin 0
    simpa using hz
  · refine ⟨-(C⁻¹ *ᵥ (x ∘ I)), ?_⟩
    change x + A *ᵥ (-(C⁻¹ *ᵥ (x ∘ I))) = x - B *ᵥ (x ∘ I)
    rw [_root_.Matrix.mulVec_neg]
    simp only [B, _root_.Matrix.mulVec_mulVec, sub_eq_add_neg]

end ArakelovGeometry.Matrix
