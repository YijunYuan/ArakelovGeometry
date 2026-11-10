/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.DeterminantTensor
public import ArakelovGeometry.Analysis.IntervalDeterminant
public import ArakelovGeometry.Analysis.TensorOperator

/-!
# Six actual interval tensors and their projective exterior cost

The six pure tensors below belong to the ordinary tensor product of the
interval plane and interval three-space. Their actual tensor-basis coordinate
determinant is two. A normalized single-wedge presentation consequently gives
the genuine projective exterior quotient length of the standard generator an
upper bound of one half. No determinant-isometry hypothesis is used.
-/

@[expose] public section

open scoped TensorProduct
open Module

namespace ArakelovGeometry

noncomputable section

/-- Plane factors of the six pure tensors, in their stated order. -/
def intervalSixTensorLeft (i : Fin 6) : Fin 2 → ℝ :=
  match i.val with
  | 0 => ![1, 0]
  | 1 => ![1, 0]
  | 2 => ![0, 1]
  | 3 => ![0, 1]
  | _ => ![1, 1]

/-- Three-space factors of the six pure tensors, in their stated order. -/
def intervalSixTensorRight (i : Fin 6) : Fin 3 → ℝ :=
  match i.val with
  | 0 => ![1, 0, 0]
  | 1 => ![0, 0, 1]
  | 2 => ![0, 1, 0]
  | 3 => ![1, 1, 1]
  | 4 => ![1, 1, 0]
  | _ => ![0, 1, 1]

/-- The six vectors in the actual ordinary tensor product. -/
def intervalSixTensor (i : Fin 6) : (Fin 2 → ℝ) ⊗[ℝ] (Fin 3 → ℝ) :=
  intervalSixTensorLeft i ⊗ₜ[ℝ] intervalSixTensorRight i

/-- Every displayed plane factor has the produced interval norm one. -/
theorem intervalSixTensorLeft_norm (i : Fin 6) :
    intervalSeminorm₂ (intervalSixTensorLeft i) = 1 := by
  fin_cases i <;> norm_num [intervalSixTensorLeft, intervalSeminorm₂_apply]

/-- Every displayed three-space factor has the produced interval norm one. -/
theorem intervalSixTensorRight_norm (i : Fin 6) :
    intervalSeminorm₃ (intervalSixTensorRight i) = 1 := by
  fin_cases i <;> norm_num [intervalSixTensorRight, intervalSeminorm₃_apply,
    Matrix.cons_val_two]

/-- The canonical tensor basis, ordered by the plane coordinate first. -/
def intervalTensorBasis : Basis (Fin 6) ℝ ((Fin 2 → ℝ) ⊗[ℝ] (Fin 3 → ℝ)) :=
  ((Pi.basisFun ℝ (Fin 2)).tensorProduct (Pi.basisFun ℝ (Fin 3))).reindex
    finProdFinEquiv

/-- The displayed matrix has the actual six tensor coordinates as columns. -/
def intervalSixTensorMatrix : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 1, 1;
     0, 1, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 0, 1]

/-- This is an identity for canonical tensor coordinates, rather than a
separate numerical matrix model. -/
theorem intervalSixTensor_coordinate (i j : Fin 6) :
    intervalTensorBasis.repr (intervalSixTensor j) i = intervalSixTensorMatrix i j := by
  unfold intervalTensorBasis intervalSixTensor
  rw [Basis.repr_reindex_apply]
  change ((Pi.basisFun ℝ (Fin 2)).tensorProduct (Pi.basisFun ℝ (Fin 3))).repr
      (intervalSixTensorLeft j ⊗ₜ[ℝ] intervalSixTensorRight j)
      (((finProdFinEquiv : Fin 2 × Fin 3 ≃ Fin 6).symm i).1,
        ((finProdFinEquiv : Fin 2 × Fin 3 ≃ Fin 6).symm i).2) = _
  rw [Basis.tensorProduct_repr_tmul_apply]
  fin_cases i <;> fin_cases j
  all_goals
    first
    | change (1 : ℝ) * 1 = 1
    | change (1 : ℝ) * 0 = 0
    | change (0 : ℝ) * 1 = 0
    | change (0 : ℝ) * 0 = 0
    norm_num

private theorem det_sparse_first_column {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1))
    (h : ∀ j, j ≠ i → A j 0 = 0) :
    A.det = (-1) ^ (i : ℕ) * A i 0 * (A.submatrix i.succAbove Fin.succ).det := by
  rw [Matrix.det_succ_column_zero]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rw [h j hji, mul_zero, zero_mul]
  · simp

/-- Sparse cofactor expansion gives the exact determinant two. -/
theorem intervalSixTensorMatrix_det : intervalSixTensorMatrix.det = 2 := by
  let A₅ := intervalSixTensorMatrix.submatrix (0 : Fin 6).succAbove Fin.succ
  let A₄ := A₅.submatrix (1 : Fin 5).succAbove Fin.succ
  let A₃ := A₄.submatrix (2 : Fin 4).succAbove Fin.succ
  have h₆ := det_sparse_first_column intervalSixTensorMatrix 0 (by
    intro j hj
    fin_cases j <;> first | contradiction | rfl)
  rw [h₆]
  change (1 : ℝ) * 1 * A₅.det = 2
  simp only [one_mul]
  have h₅ := det_sparse_first_column A₅ 1 (by
    intro j hj
    fin_cases j <;> first | contradiction | rfl)
  rw [h₅]
  change (-1 : ℝ) ^ 1 * 1 * A₄.det = 2
  norm_num only [pow_one, mul_one, neg_one_mul]
  have h₄ := det_sparse_first_column A₄ 2 (by
    intro j hj
    fin_cases j <;> first | contradiction | rfl)
  rw [h₄]
  change -((-1 : ℝ) ^ 2 * 1 * A₃.det) = 2
  norm_num only [mul_one, one_mul]
  rw [Matrix.det_fin_three]
  change -(0 * 1 * 1 - 0 * 0 * 0 - 1 * 1 * 1 + 1 * 0 * 1 +
    1 * 1 * 0 - 1 * 1 * 1 : ℝ) = 2
  norm_num

/-- The determinant of the six actual tensors in the canonical ordered basis. -/
theorem intervalSixTensor_basis_det : intervalTensorBasis.det intervalSixTensor = 2 := by
  rw [Basis.det_apply]
  have hm : intervalTensorBasis.toMatrix intervalSixTensor = intervalSixTensorMatrix := by
    ext i j
    exact intervalSixTensor_coordinate i j
  rw [hm, intervalSixTensorMatrix_det]

/-- The six actual tensors have wedge twice the standard tensor determinant vector. -/
theorem intervalSixTensor_wedge :
    exteriorPower.ιMulti ℝ 6 intervalSixTensor =
      (2 : ℝ) • exteriorPower.ιMulti ℝ 6 intervalTensorBasis := by
  apply (determinantCoordinateEquiv intervalTensorBasis).injective
  rw [map_smul, determinantCoordinateEquiv_ιMulti, determinantCoordinateEquiv_ιMulti,
    intervalSixTensor_basis_det, Basis.det_self, smul_eq_mul, mul_one]

/-- Scaling only the first actual tensor produces the standard determinant wedge. -/
def intervalSixTensorNormalized : Fin 6 → ((Fin 2 → ℝ) ⊗[ℝ] (Fin 3 → ℝ)) :=
  Function.update intervalSixTensor 0 ((1 / 2 : ℝ) • intervalSixTensor 0)

/-- The normalized tuple is an actual single-wedge presentation of the standard generator. -/
theorem intervalSixTensorNormalized_wedge :
    exteriorPower.ιMulti ℝ 6 intervalSixTensorNormalized =
      exteriorPower.ιMulti ℝ 6 intervalTensorBasis := by
  unfold intervalSixTensorNormalized
  rw [AlternatingMap.map_update_smul, Function.update_eq_self, intervalSixTensor_wedge,
    smul_smul]
  norm_num

/-- The plane and three-space factors of the interval tensor example. -/
abbrev IntervalTensorFactors : Unit ⊕ Unit → Type
  | .inl _ => Fin 2 → ℝ
  | .inr _ => Fin 3 → ℝ

local instance intervalWitnessPlaneSeminormed : SeminormedAddCommGroup (Fin 2 → ℝ) :=
  intervalNorm₂.toNormedAddCommGroup.toSeminormedAddCommGroup

local instance intervalWitnessThreeSpaceSeminormed : SeminormedAddCommGroup (Fin 3 → ℝ) :=
  intervalNorm₃.toNormedAddCommGroup.toSeminormedAddCommGroup

local instance intervalWitnessPlaneNormedSpace : NormedSpace ℝ (Fin 2 → ℝ) :=
  ⟨fun a x => by
    change intervalSeminorm₂ (a • x) ≤ ‖a‖ * intervalSeminorm₂ x
    exact (map_smul_eq_mul intervalSeminorm₂ a x).le⟩

local instance intervalWitnessThreeSpaceNormedSpace : NormedSpace ℝ (Fin 3 → ℝ) :=
  ⟨fun a x => by
    change intervalSeminorm₃ (a • x) ≤ ‖a‖ * intervalSeminorm₃ x
    exact (map_smul_eq_mul intervalSeminorm₃ a x).le⟩

local instance intervalTensorFactorsSeminormed (i : Unit ⊕ Unit) :
    SeminormedAddCommGroup (IntervalTensorFactors i) :=
  match i with
  | .inl _ => intervalNorm₂.toNormedAddCommGroup.toSeminormedAddCommGroup
  | .inr _ => intervalNorm₃.toNormedAddCommGroup.toSeminormedAddCommGroup

local instance intervalTensorFactorsNormedSpace (i : Unit ⊕ Unit) :
    NormedSpace ℝ (IntervalTensorFactors i) := by
  cases i <;> exact inferInstance

/-- The genuine projective seminorm on the ordinary plane-by-three-space tensor,
transported through the accepted canonical binary tensor equivalence. -/
def intervalTensorProjectiveSeminorm : Seminorm ℝ ((Fin 2 → ℝ) ⊗[ℝ] (Fin 3 → ℝ)) :=
  (PiTensorProduct.projectiveSeminorm (𝕜 := ℝ) (E := IntervalTensorFactors)).comp
    (binaryTensorEquiv ℝ IntervalTensorFactors).symm.toLinearMap

/-- One actual pure-tensor presentation bounds its genuine projective seminorm. -/
theorem intervalTensorProjectiveSeminorm_tmul_le (x : Fin 2 → ℝ) (y : Fin 3 → ℝ) :
    intervalTensorProjectiveSeminorm (x ⊗ₜ[ℝ] y) ≤
      intervalSeminorm₂ x * intervalSeminorm₃ y := by
  let v : ∀ i, IntervalTensorFactors i := fun i => match i with
    | .inl _ => x
    | .inr _ => y
  have hv : (binaryTensorEquiv ℝ IntervalTensorFactors).symm (x ⊗ₜ[ℝ] y) =
      PiTensorProduct.tprod ℝ v := by
    apply (binaryTensorEquiv ℝ IntervalTensorFactors).injective
    simp only [LinearEquiv.apply_symm_apply, binaryTensorEquiv_tprod]
    rfl
  change PiTensorProduct.projectiveSeminorm
    ((binaryTensorEquiv ℝ IntervalTensorFactors).symm (x ⊗ₜ[ℝ] y)) ≤ _
  rw [hv]
  have h := PiTensorProduct.projectiveSeminorm_tprod_le
    (𝕜 := ℝ) (E := IntervalTensorFactors) v
  change PiTensorProduct.projectiveSeminorm (PiTensorProduct.tprod ℝ v) ≤
    ∏ i, ‖v i‖ at h
  rw [Fintype.prod_sum_type, Fintype.prod_unique, Fintype.prod_unique] at h
  exact h

/-- All six actual pure tensors have genuine projective seminorm at most one. -/
theorem intervalSixTensor_projective_le_one (i : Fin 6) :
    intervalTensorProjectiveSeminorm (intervalSixTensor i) ≤ 1 := by
  have h := intervalTensorProjectiveSeminorm_tmul_le
    (intervalSixTensorLeft i) (intervalSixTensorRight i)
  rw [intervalSixTensorLeft_norm, intervalSixTensorRight_norm, one_mul] at h
  exact h

/-- The normalized actual tuple has projective product cost at most one half. -/
theorem intervalSixTensorNormalized_projective_prod_le :
    (∏ i, intervalTensorProjectiveSeminorm (intervalSixTensorNormalized i)) ≤ 1 / 2 := by
  have h (i : Fin 6) : intervalTensorProjectiveSeminorm (intervalSixTensorNormalized i) ≤
      if i = 0 then 1 / 2 else 1 := by
    by_cases hi : i = 0
    · subst i
      simp only [intervalSixTensorNormalized, Function.update_self, map_smul_eq_mul,
        Real.norm_eq_abs]
      norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact mul_le_of_le_one_right (by norm_num) (intervalSixTensor_projective_le_one 0)
    · simpa only [intervalSixTensorNormalized, Function.update_of_ne hi, ite_eq_right hi] using
        intervalSixTensor_projective_le_one i
  calc
    _ ≤ ∏ i : Fin 6, if i = 0 then (1 / 2 : ℝ) else 1 :=
      Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _) (fun i _ => h i)
    _ = 1 / 2 := by norm_num [Fin.prod_univ_six]

local instance intervalWitnessTensorSeminormed :
    SeminormedAddCommGroup ((Fin 2 → ℝ) ⊗[ℝ] (Fin 3 → ℝ)) :=
  intervalTensorProjectiveSeminorm.toAddGroupSeminorm.toSeminormedAddCommGroup

local instance intervalWitnessTensorNormedSpace :
    NormedSpace ℝ ((Fin 2 → ℝ) ⊗[ℝ] (Fin 3 → ℝ)) :=
  ⟨fun a x => by
    change intervalTensorProjectiveSeminorm (a • x) ≤ ‖a‖ * intervalTensorProjectiveSeminorm x
    exact (map_smul_eq_mul intervalTensorProjectiveSeminorm a x).le⟩

/-- The genuine sixfold projective tensor quotient length on the actual
top exterior power of the ordinary binary tensor product. -/
def intervalTensorProjectiveExteriorLength
    (η : ⋀[ℝ]^6 ((Fin 2 → ℝ) ⊗[ℝ] (Fin 3 → ℝ))) : ℝ :=
  sInf {c : ℝ | ∃ z : ⨂[ℝ] (_ : Fin 6), ((Fin 2 → ℝ) ⊗[ℝ] (Fin 3 → ℝ)),
    PiTensorProduct.lift (exteriorPower.ιMulti ℝ 6).toMultilinearMap z = η ∧
      PiTensorProduct.projectiveSeminorm z = c}

/-- An explicit actual tensor lift bounds the standard tensor determinant
generator's genuine projective exterior quotient length by one half. -/
theorem intervalTensorProjectiveExteriorLength_basis_le_half :
    intervalTensorProjectiveExteriorLength
      (exteriorPower.ιMulti ℝ 6 intervalTensorBasis) ≤ 1 / 2 := by
  let z := PiTensorProduct.tprod ℝ intervalSixTensorNormalized
  have hz : PiTensorProduct.lift (exteriorPower.ιMulti ℝ 6).toMultilinearMap z =
      exteriorPower.ιMulti ℝ 6 intervalTensorBasis := by
    rw [PiTensorProduct.lift.tprod]
    exact intervalSixTensorNormalized_wedge
  have hcost : PiTensorProduct.projectiveSeminorm z ≤ (1 / 2 : ℝ) := by
    calc
      _ ≤ ∏ i, intervalTensorProjectiveSeminorm (intervalSixTensorNormalized i) :=
        PiTensorProduct.projectiveSeminorm_tprod_le (𝕜 := ℝ) intervalSixTensorNormalized
      _ ≤ 1 / 2 := intervalSixTensorNormalized_projective_prod_le
  have hbelow : BddBelow {c : ℝ |
      ∃ w : ⨂[ℝ] (_ : Fin 6), ((Fin 2 → ℝ) ⊗[ℝ] (Fin 3 → ℝ)),
        PiTensorProduct.lift (exteriorPower.ιMulti ℝ 6).toMultilinearMap w =
            exteriorPower.ιMulti ℝ 6 intervalTensorBasis ∧
          PiTensorProduct.projectiveSeminorm w = c} := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, _, rfl⟩
    exact apply_nonneg _ _
  exact (csInf_le hbelow ⟨z, hz, rfl⟩).trans hcost

/-- The bounded exterior generator is nonzero in the actual exterior power. -/
theorem intervalTensorBasis_wedge_ne_zero :
    exteriorPower.ιMulti ℝ 6 intervalTensorBasis ≠ 0 := by
  intro h
  have he := congrArg (determinantCoordinateEquiv intervalTensorBasis) h
  simp only [determinantCoordinateEquiv_ιMulti, Basis.det_self, map_zero] at he
  exact one_ne_zero he

/-- The accepted canonical determinant representation sends the standard
factor determinant tensors to this same ordinary tensor determinant generator. -/
theorem intervalTensor_determinantTensorEquiv_basis :
    determinantTensorEquivOfBases (Pi.basisFun ℝ (Fin 2)) (Pi.basisFun ℝ (Fin 3))
      ((⨂ₜ[ℝ] (_ : Fin 3), exteriorPower.ιMulti ℝ 2 (Pi.basisFun ℝ (Fin 2))) ⊗ₜ[ℝ]
        (⨂ₜ[ℝ] (_ : Fin 2), exteriorPower.ιMulti ℝ 3 (Pi.basisFun ℝ (Fin 3)))) =
      exteriorPower.ιMulti ℝ 6 intervalTensorBasis := by
  rw [determinantTensorEquivOfBases_ιMulti]
  congr 1
  funext i
  simp only [intervalTensorBasis, Basis.reindex_apply, Basis.tensorProduct_apply']

/-- The one-half exterior cost applies to the actual image under the canonical
determinant tensor representation, without any isometry assumption. -/
theorem intervalTensorProjectiveExteriorLength_determinantTensorEquiv_le_half :
    intervalTensorProjectiveExteriorLength
      (determinantTensorEquivOfBases (Pi.basisFun ℝ (Fin 2)) (Pi.basisFun ℝ (Fin 3))
        ((⨂ₜ[ℝ] (_ : Fin 3), exteriorPower.ιMulti ℝ 2 (Pi.basisFun ℝ (Fin 2))) ⊗ₜ[ℝ]
          (⨂ₜ[ℝ] (_ : Fin 2), exteriorPower.ιMulti ℝ 3 (Pi.basisFun ℝ (Fin 3))))) ≤
      1 / 2 := by
  rw [intervalTensor_determinantTensorEquiv_basis]
  exact intervalTensorProjectiveExteriorLength_basis_le_half

end

end ArakelovGeometry
