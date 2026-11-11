/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.LinearAlgebra.LaurentSeries.CartanDecomposition
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Cartan decomposition over an arbitrary DVR fraction field

The existing PID matrix diagonalization is retained and specialized to a DVR;
no completeness or coefficient-field hypothesis enters. This supplies the two
matrix factorizations needed by the binary instability direction used on Bost
p31, rather than the full finite-family Hilbert–Mumford equivalence of CM 5.2.10.
The actual orbit parameter map, its geometric hypotheses, the A2 integral
representation bridge, and descent from the DVR residue field remain downstream.
-/

@[expose] public section
noncomputable section

open Module Matrix

namespace ArakelovGeometry.DVRCartan

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R L : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
variable {π : R} (hπ : Irreducible π)
include hπ

omit [Fintype ι] [DecidableEq ι] in
/-- Specializing finite denominator clearing to a DVR gives an integral multiple
by a uniformizer power. Bost p31 uses this before each binary Cartan factorization;
it needs no completion. The orbit and A2 representation/descent bridges remain. -/
theorem exists_integral_matrix [Finite ι] (g : Matrix ι ι L) :
    ∃ (m : ℕ) (A : Matrix ι ι R),
      A.map (algebraMap R L) = (algebraMap R L π) ^ m • g := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors R) (fun p : ι × ι ↦ g p.1 p.2)
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero b.property) hπ
  choose A hA using hb
  refine ⟨m, fun i j ↦ (↑u⁻¹ : R) * A (i, j), ?_⟩
  ext i j
  change algebraMap R L ((↑u⁻¹ : R) * A (i, j)) = _
  rw [map_mul, hA (i, j)]
  simp only [Algebra.smul_def, hu, map_mul, map_pow]
  rw [← mul_assoc, ← mul_assoc, ← map_mul]
  simp

/-- Specialization of PID diagonalization to an integral multiple of a fraction-field
matrix, retaining actual integral invertible factors. This is the intermediate
Bost p31 matrix input; orbit, A2 action and residue descent remain downstream. -/
theorem exists_integral_diagonal (g : GL ι L) :
    ∃ (m : ℕ) (P Q : GL ι R) (d : ι → R),
      (∀ i, d i ≠ 0) ∧
      (algebraMap R L π) ^ m • (g : Matrix ι ι L) =
        (P : Matrix ι ι R).map (algebraMap R L) *
          diagonal (fun i ↦ algebraMap R L (d i)) *
          (Q : Matrix ι ι R).map (algebraMap R L) := by
  obtain ⟨m, A, hA⟩ := exists_integral_matrix hπ (g : Matrix ι ι L)
  have hx : algebraMap R L π ≠ 0 :=
    (IsFractionRing.injective R L).ne hπ.ne_zero
  have hdet : A.det ≠ 0 := by
    intro h
    have h' := congrArg Matrix.det hA
    change ((algebraMap R L).mapMatrix A).det = _ at h'
    rw [← RingHom.map_det, h, map_zero, Matrix.det_smul] at h'
    exact (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hx))
      (GeneralLinearGroup.det g).ne_zero) h'.symm
  obtain ⟨P, Q, d, hd, h⟩ := LaurentCartan.exists_matrix_diagonal A
    (Matrix.mulVec_injective_of_det_ne_zero hdet)
  refine ⟨m, P, Q, d, hd, ?_⟩
  simpa only [Matrix.map_mul, ← diagonal_map (map_zero (algebraMap R L))] using
    hA.symm.trans (congrArg (fun B : Matrix ι ι R ↦ B.map (algebraMap R L)) h)

/-- Cartan factorization for a general DVR fraction field, extending the local
Laurent-series result with no completion assumption. Bost p31 needs this only
for its two SL factors; actual action/weight and residue descent bridges remain. -/
theorem exists_cartan (g : GL ι L) :
    ∃ (P Q : GL ι R) (a : ι → ℤ),
      (g : Matrix ι ι L) =
        (P : Matrix ι ι R).map (algebraMap R L) *
          diagonal (fun i ↦ (algebraMap R L π) ^ a i) *
          (Q : Matrix ι ι R).map (algebraMap R L) := by
  obtain ⟨m, P, Q, d, hd, h⟩ := exists_integral_diagonal hπ g
  choose k u hk using fun i ↦
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hd i) hπ
  let U : GL ι R :=
    ⟨diagonal (fun i ↦ (u i : R)), diagonal (fun i ↦ ((u i)⁻¹ : Rˣ)),
      by simp [diagonal_mul_diagonal], by simp [diagonal_mul_diagonal]⟩
  let φ := algebraMap R L
  let x : L := φ π
  have hx : x ≠ 0 := (IsFractionRing.injective R L).ne hπ.ne_zero
  refine ⟨P * U, Q, fun i ↦ (k i : ℤ) - m, ?_⟩
  apply smul_right_injective (M := Matrix ι ι L) (pow_ne_zero m hx)
  change x ^ m • (g : Matrix ι ι L) = x ^ m •
    (((P * U : GL ι R) : Matrix ι ι R).map φ *
      diagonal (fun i ↦ x ^ ((k i : ℤ) - m)) * (Q : Matrix ι ι R).map φ)
  rw [h, Units.val_mul, Matrix.map_mul]
  rw [← smul_mul_assoc, ← mul_smul_comm]
  apply congrArg (fun B : Matrix ι ι L ↦ B * (Q : Matrix ι ι R).map φ)
  rw [Matrix.mul_assoc]
  apply congrArg (fun B : Matrix ι ι L ↦ (P : Matrix ι ι R).map φ * B)
  change diagonal (fun i ↦ φ (d i)) =
    (diagonal (fun i ↦ (u i : R))).map φ *
      (x ^ m • diagonal (fun i ↦ x ^ ((k i : ℤ) - m)))
  rw [diagonal_map (map_zero φ), ← diagonal_smul, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [hk i, map_mul, map_pow]
  dsimp only [x]
  rw [Pi.smul_apply, smul_eq_mul, ← zpow_natCast (φ π) m, ← zpow_add₀ hx]
  simp [x]

end ArakelovGeometry.DVRCartan
