/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Interval.Norms
public import ArakelovGeometry.AdelicVectorBundle.Tensor.PairNorm
public import ArakelovGeometry.Analysis.Examples.Interval.TensorDeterminant

/-!
# Six actual rational tensors for the interval degree counterexample

The displayed rational vectors have the actual tensor-coordinate determinant
two. Their completed real mixed tensor norms are bounded by one.
-/

@[expose] public section

open scoped TensorProduct
open Module

noncomputable section
namespace ArakelovGeometry

/-- Rational plane factors of the six witness tensors. -/
def rationalIntervalSixTensorLeft (i : Fin 6) : Fin 2 → ℚ :=
  match i.val with
  | 0 => ![1, 0]
  | 1 => ![1, 0]
  | 2 => ![0, 1]
  | 3 => ![0, 1]
  | _ => ![1, 1]

/-- Rational three-space factors of the six witness tensors. -/
def rationalIntervalSixTensorRight (i : Fin 6) : Fin 3 → ℚ :=
  match i.val with
  | 0 => ![1, 0, 0]
  | 1 => ![0, 0, 1]
  | 2 => ![0, 1, 0]
  | 3 => ![1, 1, 1]
  | 4 => ![1, 1, 0]
  | _ => ![0, 1, 1]

/-- The six vectors in the ordinary rational tensor product. -/
def rationalIntervalSixTensor (i : Fin 6) : (Fin 2 → ℚ) ⊗[ℚ] (Fin 3 → ℚ) :=
  rationalIntervalSixTensorLeft i ⊗ₜ[ℚ] rationalIntervalSixTensorRight i

/-- The actual rational tensor basis with the stated coordinate ordering. -/
def rationalIntervalTensorBasis :
    Basis (Fin 6) ℚ ((Fin 2 → ℚ) ⊗[ℚ] (Fin 3 → ℚ)) :=
  ((Pi.basisFun ℚ (Fin 2)).tensorProduct (Pi.basisFun ℚ (Fin 3))).reindex
    finProdFinEquiv

/-- Rational tensor coordinates cast to the actual proved real witness matrix. -/
theorem rationalIntervalSixTensor_coordinate (i j : Fin 6) :
    (rationalIntervalTensorBasis.repr (rationalIntervalSixTensor j) i : ℝ) =
      intervalSixTensorMatrix i j := by
  unfold rationalIntervalTensorBasis rationalIntervalSixTensor
  rw [Basis.repr_reindex_apply]
  change (((Pi.basisFun ℚ (Fin 2)).tensorProduct (Pi.basisFun ℚ (Fin 3))).repr
      (rationalIntervalSixTensorLeft j ⊗ₜ[ℚ] rationalIntervalSixTensorRight j)
      (((finProdFinEquiv : Fin 2 × Fin 3 ≃ Fin 6).symm i).1,
        ((finProdFinEquiv : Fin 2 × Fin 3 ≃ Fin 6).symm i).2) : ℝ) = _
  rw [Basis.tensorProduct_repr_tmul_apply]
  fin_cases i <;> fin_cases j
  all_goals
    first
    | change (((1 : ℚ) * 1 : ℚ) : ℝ) = 1
    | change (((1 : ℚ) * 0 : ℚ) : ℝ) = 0
    | change (((0 : ℚ) * 1 : ℚ) : ℝ) = 0
    | change (((0 : ℚ) * 0 : ℚ) : ℝ) = 0
    norm_num

/-- The actual rational tensor determinant is two, by injective scalar transport. -/
theorem rationalIntervalSixTensor_basis_det :
    rationalIntervalTensorBasis.det rationalIntervalSixTensor = 2 := by
  apply Rat.cast_injective (α := ℝ)
  rw [Rat.cast_ofNat, Basis.det_apply]
  have hm : (rationalIntervalTensorBasis.toMatrix rationalIntervalSixTensor).map
      (Rat.castHom ℝ) = intervalSixTensorMatrix := by
    ext i j
    exact rationalIntervalSixTensor_coordinate i j
  have he := (Rat.castHom ℝ).map_det
    (rationalIntervalTensorBasis.toMatrix rationalIntervalSixTensor)
  change ((rationalIntervalTensorBasis.toMatrix rationalIntervalSixTensor).det : ℝ) =
    ((rationalIntervalTensorBasis.toMatrix rationalIntervalSixTensor).map (Rat.castHom ℝ)).det at he
  rw [hm, intervalSixTensorMatrix_det] at he
  exact he

/-- The actual rational witness wedge is twice the rational tensor basis wedge. -/
theorem rationalIntervalSixTensor_wedge :
    exteriorPower.ιMulti ℚ 6 rationalIntervalSixTensor =
      (2 : ℚ) • exteriorPower.ιMulti ℚ 6 rationalIntervalTensorBasis := by
  apply (determinantCoordinateEquiv rationalIntervalTensorBasis).injective
  rw [map_smul, determinantCoordinateEquiv_ιMulti, determinantCoordinateEquiv_ιMulti,
    rationalIntervalSixTensor_basis_det, Basis.det_self, smul_eq_mul, mul_one]

/-- Every rational left factor has actual completed real interval norm one. -/
theorem rationalIntervalSixTensorLeft_norm_infinite (i : Fin 6) :
    rationalIntervalPlaneFamily.norm (.inr ())
      ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ] rationalIntervalSixTensorLeft i) = 1 := by
  change intervalSeminorm₂ (rationalRealCompletedCoordinates 2
    ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ] rationalIntervalSixTensorLeft i)) = 1
  have he : (fun j => (rationalIntervalSixTensorLeft i j : ℝ)) = intervalSixTensorLeft i := by
    fin_cases i <;> ext j <;> fin_cases j <;> norm_num
      [rationalIntervalSixTensorLeft, intervalSixTensorLeft]
  exact (congrArg intervalSeminorm₂ (rationalRealCompletedCoordinates_rational 2
    (rationalIntervalSixTensorLeft i))).trans (by rw [he, intervalSixTensorLeft_norm])

/-- Every rational right factor has actual completed real interval norm one. -/
theorem rationalIntervalSixTensorRight_norm_infinite (i : Fin 6) :
    rationalIntervalThreeFamily.norm (.inr ())
      ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ] rationalIntervalSixTensorRight i) = 1 := by
  change intervalSeminorm₃ (rationalRealCompletedCoordinates 3
    ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ] rationalIntervalSixTensorRight i)) = 1
  have he : (fun j => (rationalIntervalSixTensorRight i j : ℝ)) = intervalSixTensorRight i := by
    fin_cases i <;> ext j <;> fin_cases j <;> norm_num
      [rationalIntervalSixTensorRight, intervalSixTensorRight]
  exact (congrArg intervalSeminorm₃ (rationalRealCompletedCoordinates_rational 3
    (rationalIntervalSixTensorRight i))).trans (by rw [he, intervalSixTensorRight_norm])

/-- The genuine completed mixed tensor family bounds all six original tensors. -/
theorem rationalIntervalSixTensor_mixed_norm_infinite_le_one (i : Fin 6) :
    (rationalIntervalPlaneFamily.mixedTensorPair rationalIntervalThreeFamily).norm (.inr ())
      ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ] rationalIntervalSixTensor i) ≤ 1 := by
  let C := (AdelicStructure.rationalAdelicStructure.ϕ (.inr ())).Completion
  let D := TensorProduct.AlgebraTensorModule.distribBaseChange ℚ C
    (Fin 2 → ℚ) (Fin 3 → ℚ)
  have he : D ((1 : C) ⊗ₜ[ℚ] rationalIntervalSixTensor i) =
      ((1 : C) ⊗ₜ[ℚ] rationalIntervalSixTensorLeft i) ⊗ₜ[C]
        ((1 : C) ⊗ₜ[ℚ] rationalIntervalSixTensorRight i) := by
    simp only [D, rationalIntervalSixTensor,
      TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
  have h := rationalIntervalPlaneFamily.mixedTensorPair_norm_tmul_completed_le
    rationalIntervalThreeFamily (.inr ())
    ((1 : C) ⊗ₜ[ℚ] rationalIntervalSixTensorLeft i)
    ((1 : C) ⊗ₜ[ℚ] rationalIntervalSixTensorRight i)
  have hz : D.symm
      (((1 : C) ⊗ₜ[ℚ] rationalIntervalSixTensorLeft i) ⊗ₜ[C]
        ((1 : C) ⊗ₜ[ℚ] rationalIntervalSixTensorRight i)) =
      (1 : C) ⊗ₜ[ℚ] rationalIntervalSixTensor i := by
    rw [← he, LinearEquiv.symm_apply_apply]
  rw [hz] at h
  exact h.trans_eq ((congrArg₂ (fun a b : ℝ => a * b)
    (rationalIntervalSixTensorLeft_norm_infinite i)
    (rationalIntervalSixTensorRight_norm_infinite i)).trans (one_mul 1))

end ArakelovGeometry
