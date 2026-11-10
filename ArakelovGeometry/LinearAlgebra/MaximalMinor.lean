/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic

/-!
# Maximal row minors

A full-column-rank rectangular matrix has a nonzero maximal row minor for any
absolute value. Normalizing by that minor gives identity rows and coefficients
of absolute value at most one, including the empty-column case.
-/

noncomputable section

open Module
open scoped Matrix

namespace ArakelovGeometry

namespace Matrix

variable {K m n : Type*} [Field K] [Fintype m] [Fintype n] [DecidableEq n]

omit [Fintype m] in
/-- A genuine full-column-rank matrix contains a square nonsingular row minor. -/
theorem exists_row_minor_det_ne_zero [Finite m] (A : Matrix m n K)
    (hA : LinearIndependent K A.col) :
    ∃ I : n → m, (A.submatrix I id).det ≠ 0 := by
  classical
  let := Fintype.ofFinite m
  have hrank : A.rank = Fintype.card n := by
    simpa using LinearIndependent.rank_matrix (M := Aᵀ) hA
  have hspan : Submodule.span K (Set.range A.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← A.rank_eq_finrank_span_row, hrank, Module.finrank_fintype_fun_eq_card]
  obtain ⟨f, hf, _, hli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.row)
  have hdim : finrank K (Submodule.span K (Set.range A.row)) = Fintype.card n := by
    rw [hspan, finrank_top, Module.finrank_fintype_fun_eq_card]
  let e : n ≃ Fin (finrank K (Submodule.span K (Set.range A.row))) :=
    (Fintype.equivFin n).trans (finCongr hdim.symm)
  choose I hI using fun j : n ↦ hf (e j)
  refine ⟨I, ?_⟩
  have hrows : LinearIndependent K (A.submatrix I id).row := by
    have heq : (A.submatrix I id).row = f ∘ e := funext hI
    rw [heq]
    exact hli.comp e e.injective
  exact ((_root_.Matrix.isUnit_iff_isUnit_det _).mp
    (_root_.Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero

omit [Fintype m] in
/-- Selecting an actual largest minor produces bounded normalization coefficients. -/
theorem exists_maximal_row_minor_normalization [Finite m] (A : Matrix m n K)
    (hA : LinearIndependent K A.col) (v : AbsoluteValue K ℝ) :
    ∃ I : n → m, Function.Injective I ∧ (A.submatrix I id).det ≠ 0 ∧
      (∀ J : n → m, v (A.submatrix J id).det ≤ v (A.submatrix I id).det) ∧
      (A * (A.submatrix I id)⁻¹).submatrix I id = 1 ∧
      ∀ i j, v ((A * (A.submatrix I id)⁻¹) i j) ≤ 1 := by
  classical
  let := Fintype.ofFinite m
  obtain ⟨I₀, hI₀⟩ := exists_row_minor_det_ne_zero A hA
  have hn : (Finset.univ : Finset (n → m)).Nonempty := ⟨I₀, Finset.mem_univ _⟩
  obtain ⟨I, _, hmax⟩ := Finset.univ.exists_max_image
    (fun J : n → m ↦ v (A.submatrix J id).det) hn
  have hpos : 0 < v (A.submatrix I id).det :=
    (v.pos hI₀).trans_le (hmax I₀ (Finset.mem_univ _))
  have hdet : (A.submatrix I id).det ≠ 0 := v.pos_iff.mp hpos
  have hinj : Function.Injective I := by
    intro i j hij
    by_contra hne
    apply hdet
    apply _root_.Matrix.det_zero_of_row_eq hne
    funext k
    change A (I i) k = A (I j) k
    rw [hij]
  let C := A.submatrix I id
  have hunit : IsUnit C.det := isUnit_iff_ne_zero.mpr hdet
  have hid : (A * C⁻¹).submatrix I id = 1 := by
    ext i j
    exact congrFun (congrFun (_root_.Matrix.mul_nonsing_inv C hunit) i) j
  refine ⟨I, hinj, hdet, fun J ↦ hmax J (Finset.mem_univ _), hid, ?_⟩
  intro i j
  have hcramer : C.det * ((A * C⁻¹) i j) =
      (A.submatrix (Function.update I j i) id).det := by
    have heq : C.updateRow j (A i) = A.submatrix (Function.update I j i) id := by
      ext k l
      by_cases hk : k = j <;> simp [C, hk, _root_.Matrix.updateRow, Function.update]
    have hc := congrFun
      (_root_.Matrix.det_smul_inv_vecMul_eq_cramer_transpose C (A i) hunit) j
    simpa [_root_.Matrix.cramer_transpose_apply, heq, _root_.Matrix.vecMul, dotProduct,
      _root_.Matrix.mul_apply, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hc
  have hb : v C.det * v ((A * C⁻¹) i j) ≤ v C.det := by
    rw [← v.map_mul, hcramer]
    exact hmax _ (Finset.mem_univ _)
  exact (mul_le_mul_iff_right₀ hpos).mp (by simpa [mul_comm] using hb)

end Matrix

end ArakelovGeometry
