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
The actual A2 coordinate-weight consumer is proved in `InvariantTheory.DVRWeights`.
The orbit parameter map, its geometric and ground-field hypotheses, primitivity
of the initial determinant vector, and residue-field descent remain downstream.
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
it needs no completion. The orbit, primitive-vector and residue-descent bridges remain. -/
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
Bost p31 matrix input; orbit, primitive-vector and residue descent remain downstream. -/
theorem exists_integral_diagonal (g : GL ι L) :
    ∃ (m : ℕ) (P Q : GL ι R) (d : ι → R),
      (∀ i, d i ≠ 0) ∧
      (algebraMap R L π) ^ m • (g : Matrix ι ι L) =
        (P : Matrix ι ι R).map (algebraMap R L) *
          diagonal (fun i ↦ algebraMap R L (d i)) *
          (Q : Matrix ι ι R).map (algebraMap R L) := by
  obtain ⟨m, A, hA⟩ := exists_integral_matrix hπ (g : Matrix ι ι L)
  have hx : algebraMap R L π ≠ 0 :=
    by simpa only [map_zero] using (IsFractionRing.injective R L).ne hπ.ne_zero
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
for its two SL factors; `InvariantTheory.DVRWeights` supplies the actual action
consumer. The orbit, primitive-vector and residue-descent bridges remain. -/
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
  have hx : x ≠ 0 := by simpa only [map_zero] using (IsFractionRing.injective R L).ne hπ.ne_zero
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

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- A pure uniformizer power which is an integral unit has exponent zero.
This extends the Laurent coefficient argument to any DVR, exactly as needed
for determinant-one weights in Bost p31. The orbit, primitive-vector and
residue-descent bridges remain. -/
theorem exponent_eq_zero_of_eq_unit (a : ℤ) (u : Rˣ)
    (h : (algebraMap R L π) ^ a = algebraMap R L (u : R)) : a = 0 := by
  let φ := algebraMap R L
  let x : L := φ π
  have hx : x ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R L).ne hπ.ne_zero
  have hn (n : ℕ) (v : Rˣ) (hv : x ^ n = φ (v : R)) : n = 0 := by
    have heq : π ^ n = (v : R) := (IsFractionRing.injective R L) (by
      simpa only [map_pow] using hv)
    exact (isUnit_pow_iff_of_not_isUnit hπ.not_isUnit).mp (heq.symm ▸ v.isUnit)
  cases a with
  | ofNat n =>
    have hz := hn n u (by simpa using h)
    simp [hz]
  | negSucc n =>
    have hi : x ^ (n + 1) = φ (↑u⁻¹ : R) := by
      apply mul_left_cancel₀ (u.isUnit.map φ).ne_zero
      simp only [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
      change φ (u : R) * x ^ (n + 1) = 1
      rw [← h]
      simp [x, φ, zpow_negSucc, pow_ne_zero _ hx]
    have hz := hn (n + 1) u⁻¹ hi
    omega

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- Every DVR Cartan factorization of a determinant-one matrix has zero total exponent.
This retains the Laurent producer over an arbitrary DVR and supplies the normalized
binary weights for Bost p31. The A2 coordinate consumer is in
`InvariantTheory.DVRWeights`; orbit, primitive-vector and residue descent remain. -/
theorem sum_exponents_eq_zero (P Q : GL ι R) (a : ι → ℤ)
    (h : ((P : Matrix ι ι R).map (algebraMap R L) *
      diagonal (fun i ↦ (algebraMap R L π) ^ a i) *
      (Q : Matrix ι ι R).map (algebraMap R L)).det = 1) :
    ∑ i, a i = 0 := by
  let φ := algebraMap R L
  let x : L := φ π
  let u := GeneralLinearGroup.det P * GeneralLinearGroup.det Q
  have hx : x ≠ 0 := by simpa only [map_zero] using (IsFractionRing.injective R L).ne hπ.ne_zero
  have hprod : φ (u : R) * x ^ (∑ i, a i) = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at h
    change (φ.mapMatrix (P : Matrix ι ι R)).det * (∏ i, x ^ a i) *
      (φ.mapMatrix (Q : Matrix ι ι R)).det = 1 at h
    rw [← φ.map_det, ← φ.map_det] at h
    have hs (s : Finset ι) : (∏ i ∈ s, x ^ a i) = x ^ (∑ i ∈ s, a i) := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih => simp [hi, ih, zpow_add₀ hx]
    rw [hs] at h
    simpa [u, map_mul, mul_assoc, mul_left_comm, mul_comm] using h
  apply exponent_eq_zero_of_eq_unit (L := L) hπ (∑ i, a i) u⁻¹
  apply mul_left_cancel₀ (u.isUnit.map φ).ne_zero
  rw [hprod, ← map_mul]
  simp

/-- Determinant-one matrices over a DVR fraction field admit integral special-linear
outer factors and zero-sum integer exponents, including dimension zero. This extends
the Laurent statement without completion and suffices for the two matrix factors
in Bost p31. `InvariantTheory.DVRWeights` proves the actual A2 coordinate-weight
consumer; the orbit-map, primitive-vector and residue-descent bridges remain. -/
theorem exists_specialLinear_cartan (g : GL ι L)
    (hg : (g : Matrix ι ι L).det = 1) :
    ∃ (P Q : SpecialLinearGroup ι R) (a : ι → ℤ),
      (∑ i, a i = 0) ∧ (g : Matrix ι ι L) =
        (P : Matrix ι ι R).map (algebraMap R L) *
          diagonal (fun i ↦ (algebraMap R L π) ^ a i) *
          (Q : Matrix ι ι R).map (algebraMap R L) := by
  obtain ⟨P, Q, a, h⟩ := exists_cartan hπ g
  have ha : ∑ i, a i = 0 := sum_exponents_eq_zero hπ P Q a (h ▸ hg)
  let φ := algebraMap R L
  let x : L := φ π
  have hx : x ≠ 0 := by simpa only [map_zero] using (IsFractionRing.injective R L).ne hπ.ne_zero
  have hD : (diagonal (fun i ↦ x ^ a i)).det = 1 := by
    rw [det_diagonal]
    have hs (s : Finset ι) : (∏ i ∈ s, x ^ a i) = x ^ (∑ i ∈ s, a i) := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih => simp [hi, ih, zpow_add₀ hx]
    rw [hs, ha, zpow_zero]
  have hpq : (P : Matrix ι ι R).det * (Q : Matrix ι ι R).det = 1 := by
    apply IsFractionRing.injective R L
    have hh := congrArg Matrix.det h
    rw [hg, det_mul, det_mul, hD, mul_one] at hh
    simpa only [map_mul, map_one, RingHom.map_det, RingHom.mapMatrix_apply] using hh.symm
  cases isEmpty_or_nonempty ι with
  | inl he =>
    exact ⟨1, 1, a, ha, Subsingleton.elim _ _⟩
  | inr he =>
    obtain ⟨i₀⟩ := he
    let u := GeneralLinearGroup.det P
    let s : ι → Rˣ := fun i ↦ if i = i₀ then u⁻¹ else 1
    let S : Matrix ι ι R := diagonal (fun i ↦ (s i : R))
    let T : Matrix ι ι R := diagonal (fun i ↦ ((s i)⁻¹ : Rˣ))
    have hS : S.det = (u⁻¹ : Rˣ) := by simp [S, s, apply_ite]
    have hT : T.det = (u : R) := by simp [T, s, apply_ite]
    have hp : ((P : Matrix ι ι R) * S).det = 1 := by
      rw [det_mul, hS]
      exact u.val_inv
    have hq : (T * (Q : Matrix ι ι R)).det = 1 := by
      rw [det_mul, hT]
      exact hpq
    refine ⟨⟨(P : Matrix ι ι R) * S, hp⟩,
      ⟨T * (Q : Matrix ι ι R), hq⟩, a, ha, ?_⟩
    change (g : Matrix ι ι L) =
      ((P : Matrix ι ι R) * S).map φ * diagonal (fun i ↦ x ^ a i) *
        (T * (Q : Matrix ι ι R)).map φ
    rw [h, Matrix.map_mul, Matrix.map_mul]
    have hmid : S.map φ * diagonal (fun i ↦ x ^ a i) * T.map φ =
        diagonal (fun i ↦ x ^ a i) := by
      dsimp only [S, T]
      rw [diagonal_map (map_zero φ), diagonal_map (map_zero φ),
        diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      rw [mul_right_comm, ← map_mul]
      simp
    calc
      _ = (P : Matrix ι ι R).map φ *
          (S.map φ * diagonal (fun i ↦ x ^ a i) * T.map φ) *
          (Q : Matrix ι ι R).map φ := by rw [hmid]
      _ = _ := by simp only [Matrix.mul_assoc]

end ArakelovGeometry.DVRCartan
