/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Normed.Field.Ultra
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Valued Vandermonde support isometries

The first rows of the literal Vandermonde matrix preserve the coordinate
maximum on each support when the residue prime exceeds the ambient rank.
The finite argument works without completeness.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace ArakelovGeometry.VandermondeUltrametric

variable {k : Type*} [NormedField k]

/-- Integral scalar entries contract in every non-Archimedean field. -/
theorem norm_intCast_le_one [IsUltrametricDist k] (a : ℤ) : ‖(a : k)‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_zsmul_le (1 : k) a

/-- An entrywise integral bound implies contraction for the coordinate maximum. -/
theorem norm_mulVec_le [IsUltrametricDist k] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ k) (hA : ∀ i j, ‖A i j‖ ≤ 1) (x : κ → k) :
    ‖A.mulVec x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  have h : ‖∑ j, A i j * x j‖₊ ≤ ‖x‖₊ := by
    apply IsUltrametricDist.nnnorm_sum_le_of_forall_le
    intro j _
    rw [nnnorm_mul]
    have hij : ‖A i j‖₊ ≤ 1 := by exact_mod_cast hA i j
    calc
      _ ≤ 1 * ‖x j‖₊ := mul_le_mul_of_nonneg_right hij zero_le
      _ ≤ ‖x‖₊ := by simpa using (show ‖x j‖₊ ≤ ‖x‖₊ from norm_le_pi_norm x j)
  exact h

/-- The actual inverse of an integral matrix has bounded entries when its determinant is a unit. -/
theorem norm_inv_entry_le_one [IsUltrametricDist k] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (hdet : ‖(A.map (Int.castRingHom k)).det‖ = 1) (i j : ι) :
    ‖(A.map (Int.castRingHom k))⁻¹ i j‖ ≤ 1 := by
  have he : (A.map (Int.castRingHom k)).adjugate =
      A.adjugate.map (Int.castRingHom k) :=
    ((Int.castRingHom k).map_adjugate A).symm
  have hc : ‖(A.map (Int.castRingHom k)).adjugate i j‖ ≤ 1 := by
    rw [he]
    exact norm_intCast_le_one (A.adjugate i j)
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply,
    smul_eq_mul, norm_mul, norm_inv, hdet, inv_one, one_mul] using hc

/-- Integral matrix and integral adjugate inverse give contractions in both directions. -/
theorem norm_integral_mulVec [IsUltrametricDist k] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (hdet : ‖(A.map (Int.castRingHom k)).det‖ = 1) (x : ι → k) :
    ‖(A.map (Int.castRingHom k)).mulVec x‖ = ‖x‖ := by
  let B := A.map (Int.castRingHom k)
  have hb : ∀ i j, ‖B i j‖ ≤ 1 := fun i j => norm_intCast_le_one (A i j)
  have hi : ∀ i j, ‖B⁻¹ i j‖ ≤ 1 := norm_inv_entry_le_one A hdet
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr (fun hz => by
    have hh : ‖B.det‖ = 1 := hdet
    rw [hz, norm_zero] at hh
    exact zero_ne_one hh)
  apply le_antisymm (norm_mulVec_le B hb x)
  have h := norm_mulVec_le B⁻¹ hi (B.mulVec x)
  simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hu, Matrix.one_mulVec] using h

section PadicExtension

variable {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] k]

/-- Every normed field extension of Qp is non-Archimedean. -/
theorem isUltrametricDist_extension (p : ℕ) [Fact p.Prime]
    [NormedAlgebra ℚ_[p] k] : IsUltrametricDist k := by
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one
  intro m
  have h := Padic.norm_int_le_one (p := p) (m : ℤ)
  have he : ‖algebraMap ℚ_[p] k (m : ℚ_[p])‖ = ‖(m : ℚ_[p])‖ :=
    norm_algebraMap' _ _
  simpa only [map_natCast, ← he, Int.cast_natCast] using h

/-- A positive integer smaller than the residue prime is a unit in every valued extension. -/
theorem norm_natCast_eq_one {m : ℕ} (hm : 0 < m) (hmp : m < p) :
    ‖(m : k)‖ = 1 := by
  have hcop : p.Coprime m := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hm hmp)
  have h := (Padic.norm_natCast_eq_one_iff (p := p) (n := m)).mpr hcop
  simpa only [map_natCast, norm_algebraMap'] using
    (show ‖algebraMap ℚ_[p] k (m : ℚ_[p])‖ = 1 by rw [norm_algebraMap', h])

/-- Distinct nodes have a unit difference, regardless of enumeration order. -/
theorem norm_node_sub_eq_one {n : ℕ} (hnp : n < p)
    (a b : Fin n) (hab : a ≠ b) :
    ‖((a.val + 1 : ℕ) : k) - ((b.val + 1 : ℕ) : k)‖ = 1 := by
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases lt_or_gt_of_ne hab' with h | h
  · rw [norm_sub_rev]
    have he : (((b.val - a.val : ℕ) : k)) =
        ((b.val + 1 : ℕ) : k) - ((a.val + 1 : ℕ) : k) := by
      rw [Nat.cast_sub h.le]
      push_cast
      ring
    rw [← he]
    exact norm_natCast_eq_one (Nat.sub_pos_of_lt h)
      (lt_of_le_of_lt (Nat.sub_le _ _) (b.isLt.trans hnp))
  · have he : (((a.val - b.val : ℕ) : k)) =
        ((a.val + 1 : ℕ) : k) - ((b.val + 1 : ℕ) : k) := by
      rw [Nat.cast_sub h.le]
      push_cast
      ring
    rw [← he]
    exact norm_natCast_eq_one (Nat.sub_pos_of_lt h)
      (lt_of_le_of_lt (Nat.sub_le _ _) (a.isLt.trans hnp))

/-- The literal first-row-prefix block on an enumerated coordinate support. -/
def block {n t : ℕ} (s : Fin t → Fin n) : Matrix (Fin t) (Fin t) k :=
  fun i j => ((s j).val + 1 : k) ^ i.val

/-- The same block over the integers, used to produce its integral adjugate. -/
def integralBlock {n t : ℕ} (s : Fin t → Fin n) : Matrix (Fin t) (Fin t) ℤ :=
  fun i j => ((s j).val + 1 : ℤ) ^ i.val

@[simp]
theorem integralBlock_map {n t : ℕ} (s : Fin t → Fin n) :
    (integralBlock s).map (Int.castRingHom k) = block (k := k) s := by
  ext i j
  simp [integralBlock, block]

/-- The determinant is the Vandermonde product of unit differences, including ranks zero and one. -/
theorem norm_det_block {n t : ℕ} (hnp : n < p) (s : Fin t → Fin n)
    (hs : Function.Injective s) : ‖(block (k := k) s).det‖ = 1 := by
  have he : block (k := k) s =
      (Matrix.vandermonde (fun j => ((s j).val + 1 : k))).transpose := rfl
  rw [he, Matrix.det_transpose, Matrix.det_vandermonde, norm_prod]
  apply Finset.prod_eq_one
  intro i _
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro j hj
  have hji : j ≠ i := ne_of_gt (Finset.mem_Ioi.mp hj)
  simpa only [Nat.cast_add, Nat.cast_one] using
    norm_node_sub_eq_one (k := k) hnp (s j) (s i) (fun h => hji (hs h))

/-- Every support block preserves the maximum over every valued extension of Qp. -/
theorem norm_block_mulVec {n t : ℕ} (hnp : n < p) (s : Fin t → Fin n)
    (hs : Function.Injective s) (x : Fin t → k) :
    ‖(block (k := k) s).mulVec x‖ = ‖x‖ := by
  let := isUltrametricDist_extension (k := k) (p := p)
  have hd : ‖((integralBlock s).map (Int.castRingHom k)).det‖ = 1 := by
    rw [integralBlock_map]
    exact norm_det_block hnp s hs
  simpa only [integralBlock_map] using norm_integral_mulVec (integralBlock s) hd x

/-- Both the literal support matrix and its actual inverse have bounded entries. -/
theorem block_and_inverse_entries_le_one {n t : ℕ} (hnp : n < p)
    (s : Fin t → Fin n) (hs : Function.Injective s) (i j : Fin t) :
    ‖block (k := k) s i j‖ ≤ 1 ∧ ‖(block (k := k) s)⁻¹ i j‖ ≤ 1 := by
  let := isUltrametricDist_extension (k := k) (p := p)
  constructor
  · rw [← integralBlock_map]
    exact norm_intCast_le_one (k := k) (integralBlock s i j)
  · have hd : ‖((integralBlock s).map (Int.castRingHom k)).det‖ = 1 := by
      rw [integralBlock_map]
      exact norm_det_block hnp s hs
    simpa only [integralBlock_map] using norm_inv_entry_le_one (integralBlock s) hd i j

end PadicExtension

end ArakelovGeometry.VandermondeUltrametric
