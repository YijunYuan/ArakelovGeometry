/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Determinants and lengths of full-rank inclusions over a DVR

Smith coordinates identify the actual quotient of a full-rank submodule
with the product of its principal cyclic quotients. Its module length is
the additive valuation of the determinant of the inclusion.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.DVRDeterminantIndex

open Module IsDiscreteValuationRing IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The length of a nonzero principal cyclic quotient is its additive valuation. -/
theorem length_quotient_span (a : R) (ha : a ≠ 0) :
    Module.length R (R ⧸ Ideal.span {a}) = addVal R a := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hπ
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    ← hπ.maximalIdeal_eq, length_quotient_pow_maximalIdeal, addVal_def' u hπ]

variable {ι M : Type*} [Fintype ι] [AddCommGroup M] [Module R M]

omit [Fintype ι] [IsDomain R] [IsDiscreteValuationRing R] in
theorem diagonal_coordinates [Finite ι] (N : Submodule R M) (b : Basis ι R M)
    (c : Basis ι R N) (a : ι → R) (h : ∀ i, (c i : M) = a i • b i)
    (x : N) (i : ι) : b.repr (x : M) i = c.repr x i * a i := by
  classical
  let := Fintype.ofFinite ι
  have hx := congrArg (fun y : N => b.repr (y : M) i) (c.sum_repr x)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, h, map_sum, map_smul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, Basis.repr_self_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    using hx.symm

omit [Fintype ι] [IsDomain R] [IsDiscreteValuationRing R] in
theorem diagonal_map [Finite ι] (N : Submodule R M) (b : Basis ι R M)
    (c : Basis ι R N) (a : ι → R) (h : ∀ i, (c i : M) = a i • b i) :
    N.map b.equivFun.toLinearMap =
      Submodule.pi Set.univ (fun i => (Ideal.span {a i} : Submodule R R)) := by
  classical
  let := Fintype.ofFinite ι
  ext y
  simp only [Submodule.mem_map, Submodule.mem_pi, Set.mem_univ, forall_const,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    change a i ∣ b.repr x i
    rw [diagonal_coordinates N b c a h ⟨x, hx⟩ i]
    exact dvd_mul_left _ _
  · intro hy
    choose r hr using hy
    let x : N := ∑ i, r i • c i
    refine ⟨(x : M), x.property, ?_⟩
    ext i
    change b.repr (x : M) i = y i
    rw [diagonal_coordinates N b c a h x i]
    have hrepr : c.repr x i = r i := by
      simp [x, map_sum, Finsupp.finsetSum_apply, Finsupp.single_apply]
    rw [hrepr, mul_comm, ← hr i]

omit [Fintype ι] [IsDomain R] [IsDiscreteValuationRing R] in
/-- Coordinate residues identify the original quotient, including rank zero. -/
def diagonalQuotientEquiv [Finite ι] (N : Submodule R M) (b : Basis ι R M)
    (c : Basis ι R N) (a : ι → R) (h : ∀ i, (c i : M) = a i • b i) :
    (M ⧸ N) ≃ₗ[R] (∀ i, R ⧸ Ideal.span {a i}) := by
  classical
  let := Fintype.ofFinite ι
  exact (Submodule.Quotient.equiv N _ b.equivFun (diagonal_map N b c a h)).trans
    (Submodule.quotientPi _)

/-- In diagonal bases, quotient length adds the actual nonzero invariant factors. -/
theorem length_quotient_diagonal (N : Submodule R M) (b : Basis ι R M)
    (c : Basis ι R N) (a : ι → R) (h : ∀ i, (c i : M) = a i • b i) :
    Module.length R (M ⧸ N) = ∑ i, addVal R (a i) := by
  rw [(diagonalQuotientEquiv N b c a h).length_eq, Module.length_pi_of_fintype]
  apply Finset.sum_congr rfl
  intro i _
  apply length_quotient_span
  intro hi
  apply c.ne_zero i
  apply Subtype.val_injective
  simp [h i, hi]

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem diagonal_inclusion_matrix [DecidableEq ι] (N : Submodule R M)
    (b : Basis ι R M) (c : Basis ι R N) (a : ι → R)
    (h : ∀ i, (c i : M) = a i • b i) :
    LinearMap.toMatrix c b N.subtype = Matrix.diagonal a := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [LinearMap.toMatrix_apply, h]
  · simp [LinearMap.toMatrix_apply, h, hij]

/-- The determinant valuation reads the actual quotient length in diagonal bases. -/
theorem length_quotient_eq_addVal_diagonal_det [DecidableEq ι]
    (N : Submodule R M) (b : Basis ι R M) (c : Basis ι R N) (a : ι → R)
    (h : ∀ i, (c i : M) = a i • b i) :
    Module.length R (M ⧸ N) =
      addVal R (LinearMap.toMatrix c b N.subtype).det := by
  rw [length_quotient_diagonal N b c a h, diagonal_inclusion_matrix N b c a h,
    Matrix.det_diagonal]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs => simp [hi, hs]

theorem addVal_basis_toMatrix_det [DecidableEq ι] (b b' : Basis ι R M) :
    addVal R (b.toMatrix b').det = 0 :=
  addVal_eq_zero_iff.mpr (by simpa only [← Basis.det_apply] using b.isUnit_det b')

/-- A full-rank inclusion has quotient length equal to its determinant valuation
in arbitrary bases of the original two modules. -/
theorem length_quotient_eq_addVal_det [DecidableEq ι] (N : Submodule R M)
    (b : Basis ι R M) (c : Basis ι R N) :
    Module.length R (M ⧸ N) =
      addVal R (LinearMap.toMatrix c b N.subtype).det := by
  have hrank : Module.finrank R N = Module.finrank R M := by
    rw [Module.finrank_eq_card_basis c, Module.finrank_eq_card_basis b]
  let b' := N.smithNormalFormTopBasis b hrank
  let c' := N.smithNormalFormBotBasis b hrank
  let a := N.smithNormalFormCoeffs b hrank
  have hdiag : ∀ i, (c' i : M) = a i • b' i :=
    Submodule.smithNormalFormBotBasis_def b hrank
  have hlen := length_quotient_eq_addVal_diagonal_det N b' c' a hdiag
  have hmat := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix c c' b b' N.subtype
  have hv := congrArg (fun A : Matrix ι ι R => addVal R A.det) hmat
  simp only [Matrix.det_mul, addVal_mul, addVal_basis_toMatrix_det, zero_add, add_zero] at hv
  exact hlen.trans hv

end ArakelovGeometry.DVRDeterminantIndex
