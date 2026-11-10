/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.GeometricCoordinateRestrictionIsometry

/-!
# Rational selected-coordinate bases on actual completed subspaces

The inverse of a nonsingular ground minor constructs a rational basis. Actual
completed basis coordinates are the selected ambient coordinates; the produced
minor norm identity therefore gives the original completed restriction norm.
-/

open scoped TensorProduct Matrix
noncomputable section
namespace ArakelovGeometry

variable {K E m n : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype m] [Fintype n] [DecidableEq n]

/-- The nonsingular ground minor gives the rational selected-coordinate
equivalence; its inverse uses the actual rational subspace basis. -/
def selectedSubspaceCoordinatesEquiv (b : Module.Basis m K E)
    (F : Submodule K E) (c : Module.Basis n K F) (I : n → m)
    (hd : (_root_.Matrix.submatrix (fun i j ↦ b.equivFun (c j).val i) I id).det ≠ 0) :
    F ≃ₗ[K] (n → K) := by
  let C : Matrix n n K := fun i j ↦ b.equivFun (c j).val (I i)
  exact
    { (_root_.Matrix.mulVecLin C).comp c.equivFun.toLinearMap with
      invFun := fun a ↦ c.equivFun.symm (C⁻¹ *ᵥ a)
      left_inv := by
        intro z
        change c.equivFun.symm (C⁻¹ *ᵥ (C *ᵥ c.equivFun z)) = z
        rw [_root_.Matrix.mulVec_mulVec,
          _root_.Matrix.nonsing_inv_mul C (IsUnit.mk0 _ hd), _root_.Matrix.one_mulVec]
        exact c.equivFun.symm_apply_apply z
      right_inv := by
        intro a
        change C *ᵥ c.equivFun (c.equivFun.symm (C⁻¹ *ᵥ a)) = a
        rw [LinearEquiv.apply_symm_apply, _root_.Matrix.mulVec_mulVec,
          _root_.Matrix.mul_nonsing_inv C (IsUnit.mk0 _ hd), _root_.Matrix.one_mulVec] }

/-- The constructed equivalence is exactly the selected ambient coordinates,
rather than an additional coordinate model of the original subspace. -/
theorem selectedSubspaceCoordinatesEquiv_apply (b : Module.Basis m K E)
    (F : Submodule K E) (c : Module.Basis n K F) (I : n → m)
    (hd : (_root_.Matrix.submatrix (fun i j ↦ b.equivFun (c j).val i) I id).det ≠ 0)
    (z : F) : selectedSubspaceCoordinatesEquiv b F c I hd z = b.equivFun z.val ∘ I := by
  change (fun i j ↦ b.equivFun (c j).val (I i) : Matrix n n K) *ᵥ c.equivFun z = _
  have hz : z.val = ∑ j, c.equivFun z j • (c j).val := by
    simpa only [map_sum, map_smul, Submodule.subtype_apply] using
      congrArg F.subtype (c.sum_equivFun z).symm
  rw [hz, map_sum]
  ext i
  simp only [_root_.Matrix.mulVec, dotProduct, Function.comp_apply, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

/-- The normalized rational basis is produced by the selected-coordinate
equivalence, for any nonsingular minor and including rank zero. -/
def selectedSubspaceBasis (b : Module.Basis m K E) (F : Submodule K E)
    (c : Module.Basis n K F) (I : n → m)
    (hd : (_root_.Matrix.submatrix (fun i j ↦ b.equivFun (c j).val i) I id).det ≠ 0) :
    Module.Basis n K F := Module.Basis.ofEquivFun (selectedSubspaceCoordinatesEquiv b F c I hd)

/-- Each rational coordinate of the produced basis is the selected ambient
coordinate. This computes the actual scalar extension of the basis. -/
theorem selectedSubspaceBasis_repr_apply (b : Module.Basis m K E) (F : Submodule K E)
    (c : Module.Basis n K F) (I : n → m)
    (hd : (_root_.Matrix.submatrix (fun i j ↦ b.equivFun (c j).val i) I id).det ≠ 0)
    (z : F) (j : n) : (selectedSubspaceBasis b F c I hd).repr z j = b.equivFun z.val (I j) := by
  rw [selectedSubspaceBasis, Module.Basis.ofEquivFun_repr_apply,
    selectedSubspaceCoordinatesEquiv_apply]
  rfl

namespace NormFamily
variable {S : AdelicStructure K}

/-- The actual completed coordinates of the produced rational basis equal
the selected ambient completed coordinates on every scalar tensor. -/
theorem selectedSubspaceBasis_completed_coordinates (b : Module.Basis m K E)
    (F : Submodule K E) (c : Module.Basis n K F) (I : n → m)
    (hd : (_root_.Matrix.submatrix (fun i j ↦ b.equivFun (c j).val i) I id).det ≠ 0)
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] F) :
    ((selectedSubspaceBasis b F c I hd).baseChange (S.ϕ ω).Completion).equivFun z =
      ((b.baseChange (S.ϕ ω).Completion).equivFun
        (F.subtype.baseChange (S.ϕ ω).Completion z)) ∘ I := by
  induction z using TensorProduct.induction_on with
  | zero => ext j; simp
  | tmul a z =>
    ext j
    rw [LinearMap.baseChange_tmul]
    simp only [Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul,
      Function.comp_apply, selectedSubspaceBasis_repr_apply]
    rfl
  | add z w hz hw =>
    ext j
    simp only [map_add, Pi.add_apply, Function.comp_apply] at *
    exact congrFun hz j ▸ congrFun hw j ▸ rfl

/-- A prescribed normalized maximal minor produces the actual completed
restriction norm as the coordinate norm of an explicit rational basis. -/
theorem ofBasis_restrict_norm_eq_selectedSubspaceBasis (b : Module.Basis m K E)
    (F : Submodule K E) (c : Module.Basis n K F) (I : n → m)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) :
    let A : Matrix m n K := fun i j ↦ b.equivFun (c j).val i
    ∀ (hd : (A.submatrix I id).det ≠ 0),
      (A * (A.submatrix I id)⁻¹).submatrix I id = 1 →
      (∀ i j, (S.ϕ ω) ((A * (A.submatrix I id)⁻¹) i j) ≤ 1) →
      ∀ z : (S.ϕ ω).Completion ⊗[K] F,
        ((ofBasis S E b).restrict F).norm ω z =
          ‖((selectedSubspaceBasis b F c I hd).baseChange (S.ϕ ω).Completion).equivFun z‖ := by
  intro A hd hid hB z
  rw [selectedSubspaceBasis_completed_coordinates]
  exact ofBasis_restrict_norm_eq_selected_coordinates b F c I ω hω hd hid hB z

end NormFamily
end ArakelovGeometry
