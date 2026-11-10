/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.LinearAlgebra.StdBasis

/-! # Block coordinates for products of a full real lattice -/

@[expose] public section

noncomputable section
open MeasureTheory Module

namespace ArakelovGeometry.NumberFieldPrincipalBasisProductCovolume

variable {ι J : Type*} [Fintype ι] [Fintype J]

/-- Reorder the finite product into its real block coordinates. -/
def blockCoordinates : (ι → J → ℝ) ≃ₗ[ℝ] (J × ι → ℝ) where
  toFun z p := z p.2 p.1
  invFun z i j := z (j, i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The indices of the product basis, in the order of the real blocks. -/
def blockIndexEquiv : (Σ _ : ι, J) ≃ J × ι where
  toFun p := (p.2, p.1)
  invFun p := ⟨p.2, p.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A real basis for the product of copies of a real lattice basis. -/
def blockBasis (c : Basis J ℝ (J → ℝ)) : Basis (J × ι) ℝ (J × ι → ℝ) :=
  ((Pi.basis (fun _ : ι => c)).reindex blockIndexEquiv).map blockCoordinates

omit [Fintype J] in
theorem blockBasis_apply [DecidableEq ι] (c : Basis J ℝ (J → ℝ)) (p q : J × ι) :
    blockBasis (ι := ι) c p q = if p.2 = q.2 then c p.1 q.1 else 0 := by
  classical
  by_cases h : p.2 = q.2 <;>
    simp [blockBasis, blockCoordinates, blockIndexEquiv, eq_comm, h]

omit [Fintype J] in
theorem blockBasis_repr (c : Basis J ℝ (J → ℝ)) (z : J × ι → ℝ) (p : J × ι) :
    (blockBasis (ι := ι) c).repr z p = c.repr (fun j => z (j, p.2)) p.1 := by
  rw [blockBasis, Basis.map_repr, LinearEquiv.trans_apply,
    Basis.repr_reindex_apply, Pi.basis_repr]
  rfl

/-- A literal integer span, with one lattice block for every finite index. -/
def productLattice (c : Basis J ℝ (J → ℝ)) : Submodule ℤ (J × ι → ℝ) :=
  Submodule.span ℤ (Set.range (blockBasis (ι := ι) c))

omit [Fintype J] in
theorem mem_productLattice (c : Basis J ℝ (J → ℝ)) (z : J × ι → ℝ) :
    z ∈ productLattice (ι := ι) c ↔
      ∀ i, (fun j => z (j, i)) ∈ Submodule.span ℤ (Set.range c) := by
  rw [productLattice, (blockBasis c).mem_span_iff_repr_mem ℤ]
  simp_rw [blockBasis_repr, c.mem_span_iff_repr_mem ℤ]
  exact ⟨fun h i j => h (j, i), fun h p => h p.2 p.1⟩

omit [Fintype J] in
theorem blockBasis_matrix [DecidableEq ι] (c : Basis J ℝ (J → ℝ)) :
    Matrix.of (blockBasis (ι := ι) c) =
      Matrix.blockDiagonal (fun _ : ι => Matrix.of c) := by
  classical
  ext p q
  exact blockBasis_apply c p q

theorem covolume_span_basis [DecidableEq J] (c : Basis J ℝ (J → ℝ)) :
    ZLattice.covolume (Submodule.span ℤ (Set.range c)) volume =
      |(Matrix.of c).det| := by
  classical
  rw [ZLattice.covolume_eq_det _ (c.restrictScalars ℤ)]
  congr 2
  ext j k
  simp

/-- The covolume product is proved by the determinant of the actual block basis. -/
theorem productCovolume (c : Basis J ℝ (J → ℝ)) :
    ZLattice.covolume (productLattice (ι := ι) c) volume =
      ZLattice.covolume (Submodule.span ℤ (Set.range c)) volume ^ Fintype.card ι := by
  classical
  rw [productLattice, covolume_span_basis, blockBasis_matrix, Matrix.det_blockDiagonal,
    covolume_span_basis, Finset.abs_prod]
  simp

end ArakelovGeometry.NumberFieldPrincipalBasisProductCovolume
