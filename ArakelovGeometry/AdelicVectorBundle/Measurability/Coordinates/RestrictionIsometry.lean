/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Subquotient.Restriction.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Rational
import ArakelovGeometry.LinearAlgebra.MeasurableMaximalMinor
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Selected-minor isometries on actual completed coordinate subspaces

A ground-field maximizing minor gives an exact norm formula on every vector
of the actual completed restricted subspace. Its finite measurable selection
will supply determinant and operator regularity without scalar countability.
-/

@[expose] public section

open scoped TensorProduct Matrix
noncomputable section
namespace ArakelovGeometry

namespace Matrix
variable {L m n : Type*} [NormedField L] [IsUltrametricDist L]
  [Fintype m] [Fintype n] [DecidableEq n]

/-- A prescribed normalized minor identifies the actual column-space maximum
norm with its selected coordinates. The selected minor need not be re-chosen. -/
theorem mulVec_norm_eq_selected_coordinates (A : Matrix m n L) (I : n → m)
    (hd : (A.submatrix I id).det ≠ 0)
    (hid : (A * (A.submatrix I id)⁻¹).submatrix I id = 1)
    (hB : ∀ i j, ‖(A * (A.submatrix I id)⁻¹) i j‖ ≤ 1) (a : n → L) :
    ‖A *ᵥ a‖ = ‖(A *ᵥ a) ∘ I‖ := by
  let C := A.submatrix I id
  let B := A * C⁻¹
  have hBA : B * C = A := by
    rw [_root_.Matrix.mul_assoc, _root_.Matrix.nonsing_inv_mul C (IsUnit.mk0 _ hd),
      _root_.Matrix.mul_one]
  have hpivot (v : n → L) : (B *ᵥ v) ∘ I = v := by
    have h : B.submatrix I id *ᵥ v = v := by rw [hid, _root_.Matrix.one_mulVec]
    exact h
  have hnorm (v : n → L) : ‖B *ᵥ v‖ = ‖v‖ := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
      intro i
      change ‖∑ j, B i j * v j‖ ≤ ‖v‖
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg v)
      intro j _
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hB i j) (norm_nonneg (v j))).trans
        (by simpa only [one_mul] using norm_le_pi_norm v j)
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro j
      rw [← congrFun (hpivot v) j]
      exact norm_le_pi_norm (B *ᵥ v) (I j)
  rw [← hBA, ← _root_.Matrix.mulVec_mulVec, hnorm, hpivot]

end Matrix

namespace NormFamily
variable {K E m n : Type*} [Field K] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E]
  [Fintype m] [Fintype n] [DecidableEq n]

/-- A ground-field selected minor computes the restricted coordinate norm on
every vector of the actual completed subspace, including dimension zero. -/
theorem ofBasis_restrict_norm_eq_selected_coordinates (b : Module.Basis m K E)
    (F : Submodule K E) (c : Module.Basis n K F) (I : n → m)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) :
    let A : Matrix m n K := fun i j ↦ b.equivFun (c j).val i
    (A.submatrix I id).det ≠ 0 →
    (A * (A.submatrix I id)⁻¹).submatrix I id = 1 →
    (∀ i j, (S.ϕ ω) ((A * (A.submatrix I id)⁻¹) i j) ≤ 1) →
    ∀ z : (S.ϕ ω).Completion ⊗[K] F,
      ((ofBasis S E b).restrict F).norm ω z =
        ‖((b.baseChange (S.ϕ ω).Completion).equivFun
          (F.subtype.baseChange (S.ϕ ω).Completion z)) ∘ I‖ := by
  classical
  intro A hd hid hB z
  let L := (S.ϕ ω).Completion
  let f := algebraMap K L
  let C := A.submatrix I id
  let A' := A.map f
  have hCi : (C.map f)⁻¹ = C⁻¹.map f := by
    apply _root_.Matrix.inv_eq_left_inv
    rw [← _root_.Matrix.map_mul,
      _root_.Matrix.nonsing_inv_mul C (IsUnit.mk0 _ hd)]
    exact _root_.Matrix.map_one f f.map_zero f.map_one
  have hsub : A'.submatrix I id = C.map f := rfl
  have hmap : A' * (A'.submatrix I id)⁻¹ = (A * C⁻¹).map f := by
    rw [hsub, hCi]
    exact _root_.Matrix.map_mul.symm
  have hdet : (A'.submatrix I id).det ≠ 0 := by
    rw [hsub]
    change (f.mapMatrix C).det ≠ 0
    rw [← f.map_det]
    exact (map_ne_zero f).mpr hd
  have hid' : (A' * (A'.submatrix I id)⁻¹).submatrix I id = 1 := by
    rw [hmap, _root_.Matrix.submatrix_map, hid]
    exact _root_.Matrix.map_one f f.map_zero f.map_one
  have hB' : ∀ i j, ‖(A' * (A'.submatrix I id)⁻¹) i j‖ ≤ 1 := by
    intro i j
    rw [hmap]
    change ‖algebraMap K L ((A * C⁻¹) i j)‖ ≤ 1
    rw [S.norm_algebraMap_eq_absValue]
    exact hB i j
  let : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (S.norm_add_le_max_of_finite ω hω)
  let e := (b.baseChange L).equivFun
  let d := c.baseChange L
  let k := F.subtype.baseChange L
  have hecol (j : n) : e (k (d j)) = fun i ↦ f (A i j) := by
    ext i
    change (b.baseChange L).equivFun
      (F.subtype.baseChange L ((c.baseChange L) j)) i = f (A i j)
    rw [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul]
    exact basis_equivFun_one_tmul b ω (c j).val i
  have heA (a : n → L) : e (k (d.equivFun.symm a)) = A' *ᵥ a := by
    rw [← d.sum_equivFun (d.equivFun.symm a), LinearEquiv.apply_symm_apply]
    ext i
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      hecol, _root_.Matrix.mulVec, dotProduct, A', _root_.Matrix.map_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  have he : e (k z) = A' *ᵥ d.equivFun z := by
    simpa only [LinearEquiv.symm_apply_apply] using heA (d.equivFun z)
  change (ofBasis S E b).norm ω (k z) = ‖e (k z) ∘ I‖
  rw [ofBasis_norm, he]
  exact Matrix.mulVec_norm_eq_selected_coordinates A' I hdet hid' hB' _

/-- One finite measurable maximal-minor partition gives exact selected-coordinate
isometries on all actual completed restrictions, without field countability. -/
theorem exists_measurable_ofBasis_restrict_selected_coordinates
    (b : Module.Basis m K E) (F : Submodule K E) (c : Module.Basis n K F)
    (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    ∃ I : S.Ω → n → m, (∀ J, MeasurableSet {ω | I ω = J}) ∧
      ∀ ω, Function.Injective (I ω) ∧
        (_root_.Matrix.submatrix (fun i j ↦ b.equivFun (c j).val i) (I ω) id).det ≠ 0 ∧
        ∀ z : (S.ϕ ω).Completion ⊗[K] F,
          ((ofBasis S E b).restrict F).norm ω z =
            ‖((b.baseChange (S.ϕ ω).Completion).equivFun
              (F.subtype.baseChange (S.ϕ ω).Completion z)) ∘ I ω‖ := by
  classical
  let A : Matrix m n K := fun i j ↦ b.equivFun (c j).val i
  have hA : LinearIndependent K A.col :=
    (c.linearIndependent.map' F.subtype
      (LinearMap.ker_eq_bot.mpr (Submodule.subtype_injective _))).map'
        b.equivFun.toLinearMap (LinearMap.ker_eq_bot.mpr b.equivFun.injective)
  obtain ⟨I, hI, hnorm⟩ := Matrix.exists_measurable_maximal_minor A hA S.ϕ S.measurable_absValue
  refine ⟨I, hI, ?_⟩
  intro ω
  obtain ⟨hi, hd, _, hid, hB⟩ := hnorm ω
  exact ⟨hi, hd, ofBasis_restrict_norm_eq_selected_coordinates b F c (I ω) ω (hS ω) hd hid hB⟩

end NormFamily
end ArakelovGeometry
