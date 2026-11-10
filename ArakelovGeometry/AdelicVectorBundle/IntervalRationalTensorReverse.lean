/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.IntervalRationalTensorGlobalDegree
import ArakelovGeometry.Analysis.DeterminantPairing

/-! # The actual three-by-two interval tensor witness -/

open scoped TensorProduct
open Module MeasureTheory

noncomputable section
namespace ArakelovGeometry
open AdelicStructure

/-- The actual rational interval plane is strongly adelic. -/
theorem rationalIntervalPlaneBundle_isStronglyAdelic :
    rationalIntervalPlaneBundle.IsStronglyAdelic :=
  (rationalIntervalPlaneFamily.isStronglyDominated_iff_isDominated_of_ultrametric
    (rationalRealModifiedFamily_isUltrametric 2 intervalSeminorm₂
      intervalSeminorm₂_eq_zero_iff) rationalAdelicStructure_isRCLike).mpr
    rationalIntervalPlaneFamily_isDominated

/-- The actual rational interval three-space is strongly adelic. -/
theorem rationalIntervalThreeBundle_isStronglyAdelic :
    rationalIntervalThreeBundle.IsStronglyAdelic :=
  (rationalIntervalThreeFamily.isStronglyDominated_iff_isDominated_of_ultrametric
    (rationalRealModifiedFamily_isUltrametric 3 intervalSeminorm₃
      intervalSeminorm₃_eq_zero_iff) rationalAdelicStructure_isRCLike).mpr
    rationalIntervalThreeFamily_isDominated

/-- The actual mixed tensor in the three-by-two order of the original example. -/
def rationalIntervalReverseTensorBundle :
    AdelicVectorBundle rationalAdelicStructure ((Fin 3 → ℚ) ⊗[ℚ] (Fin 2 → ℚ)) :=
  rationalIntervalThreeBundle.mixedTensorPair rationalIntervalPlaneBundle
    (Or.inl inferInstance) rationalAdelicStructure_isRCLike

theorem rationalIntervalReverseTensorBundle_toNormFamily :
    rationalIntervalReverseTensorBundle.toNormFamily =
      rationalIntervalThreeFamily.mixedTensorPair rationalIntervalPlaneFamily := rfl

theorem rationalIntervalReverseTensorBundle_isStronglyAdelic :
    rationalIntervalReverseTensorBundle.IsStronglyAdelic :=
  rationalIntervalThreeBundle.mixedTensorPair_isStronglyAdelic rationalIntervalPlaneBundle
    (Or.inl inferInstance) rationalAdelicStructure_isRCLike

/-- Exact three-dimensional factors of the displayed original six-tuple. -/
def rationalIntervalReverseSixTensorLeft (i : Fin 6) : Fin 3 → ℚ :=
  match i.val with
  | 0 => ![1, 1, 0]
  | 1 => ![0, 1, 1]
  | 2 => ![1, 1, 1]
  | 3 => ![1, 0, 0]
  | 4 => ![0, 1, 0]
  | _ => ![0, 0, 1]

/-- Exact plane factors of the displayed original six-tuple. -/
def rationalIntervalReverseSixTensorRight (i : Fin 6) : Fin 2 → ℚ :=
  match i.val with
  | 0 => ![1, 1]
  | 1 => ![1, 1]
  | 2 => ![1, 0]
  | 3 => ![0, 1]
  | 4 => ![1, 0]
  | _ => ![0, 1]

def rationalIntervalReverseSixTensor (i : Fin 6) :
    (Fin 3 → ℚ) ⊗[ℚ] (Fin 2 → ℚ) :=
  rationalIntervalReverseSixTensorLeft i ⊗ₜ[ℚ] rationalIntervalReverseSixTensorRight i

def rationalIntervalReverseTensorBasis :
    Basis (Fin 6) ℚ ((Fin 3 → ℚ) ⊗[ℚ] (Fin 2 → ℚ)) :=
  ((Pi.basisFun ℚ (Fin 3)).tensorProduct (Pi.basisFun ℚ (Fin 2))).reindex finProdFinEquiv

/-- The even row permutation identifying the two proved witness matrices. -/
def rationalIntervalReverseRowPermutation : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 4, 1, 5, 2]
  invFun := ![1, 3, 5, 0, 2, 4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The even column permutation identifying the two proved witness matrices. -/
def rationalIntervalReverseColumnPermutation : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 3, 0, 2, 1]
  invFun := ![3, 5, 4, 2, 0, 1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Actual rational coordinates agree with the reindexed accepted real matrix. -/
theorem rationalIntervalReverseSixTensor_coordinate (i j : Fin 6) :
    (rationalIntervalReverseTensorBasis.repr (rationalIntervalReverseSixTensor j) i : ℝ) =
      intervalSixTensorMatrix (rationalIntervalReverseRowPermutation i)
        (rationalIntervalReverseColumnPermutation j) := by
  unfold rationalIntervalReverseTensorBasis rationalIntervalReverseSixTensor
  rw [Basis.repr_reindex_apply, Basis.tensorProduct_repr_tmul_apply]
  fin_cases i <;> fin_cases j
  all_goals
    first
    | change (((1 : ℚ) * 1 : ℚ) : ℝ) = 1
    | change (((1 : ℚ) * 0 : ℚ) : ℝ) = 0
    | change (((0 : ℚ) * 1 : ℚ) : ℝ) = 0
    | change (((0 : ℚ) * 0 : ℚ) : ℝ) = 0
    norm_num

/-- The exact original three-by-two ordered tuple has determinant two. -/
theorem rationalIntervalReverseSixTensor_basis_det :
    rationalIntervalReverseTensorBasis.det rationalIntervalReverseSixTensor = 2 := by
  apply Rat.cast_injective (α := ℝ)
  rw [Rat.cast_ofNat, Basis.det_apply]
  have hm : (rationalIntervalReverseTensorBasis.toMatrix rationalIntervalReverseSixTensor).map
      (Rat.castHom ℝ) = intervalSixTensorMatrix.reindex
        rationalIntervalReverseRowPermutation.symm
        rationalIntervalReverseColumnPermutation.symm := by
    ext i j
    exact rationalIntervalReverseSixTensor_coordinate i j
  have he := (Rat.castHom ℝ).map_det
    (rationalIntervalReverseTensorBasis.toMatrix rationalIntervalReverseSixTensor)
  change ((rationalIntervalReverseTensorBasis.toMatrix rationalIntervalReverseSixTensor).det : ℝ) =
    ((rationalIntervalReverseTensorBasis.toMatrix rationalIntervalReverseSixTensor).map
      (Rat.castHom ℝ)).det at he
  rw [hm, Matrix.det_reindex, intervalSixTensorMatrix_det] at he
  have hs : Equiv.Perm.sign
      (rationalIntervalReverseColumnPermutation.symm.trans
        rationalIntervalReverseRowPermutation) = 1 := by decide
  simpa only [Equiv.symm_symm, hs, Int.cast_one, Units.val_one, one_mul] using he

/-- The literal reversed witness wedge is twice the standard tensor wedge. -/
theorem rationalIntervalReverseSixTensor_wedge :
    exteriorPower.ιMulti ℚ 6 rationalIntervalReverseSixTensor =
      (2 : ℚ) • exteriorPower.ιMulti ℚ 6 rationalIntervalReverseTensorBasis := by
  apply (determinantCoordinateEquiv rationalIntervalReverseTensorBasis).injective
  rw [map_smul, determinantCoordinateEquiv_ιMulti, determinantCoordinateEquiv_ιMulti,
    rationalIntervalReverseSixTensor_basis_det, Basis.det_self, smul_eq_mul, mul_one]

/-- Every displayed three-space factor retains its actual infinite norm one. -/
theorem rationalIntervalReverseSixTensorLeft_norm_infinite (i : Fin 6) :
    rationalIntervalThreeFamily.norm (.inr ())
      ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ]
        rationalIntervalReverseSixTensorLeft i) = 1 := by
  have he : rationalIntervalReverseSixTensorLeft i =
      rationalIntervalSixTensorRight (rationalIntervalReverseColumnPermutation i) := by
    fin_cases i <;> rfl
  rw [he]
  exact rationalIntervalSixTensorRight_norm_infinite _

/-- Every displayed plane factor retains its actual infinite norm one. -/
theorem rationalIntervalReverseSixTensorRight_norm_infinite (i : Fin 6) :
    rationalIntervalPlaneFamily.norm (.inr ())
      ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ]
        rationalIntervalReverseSixTensorRight i) = 1 := by
  have he : rationalIntervalReverseSixTensorRight i =
      rationalIntervalSixTensorLeft (![4, 4, 0, 2, 0, 2] i) := by
    fin_cases i <;> rfl
  rw [he]
  exact rationalIntervalSixTensorLeft_norm_infinite _

/-- The exact displayed six tensors have actual completed mixed norm at most one. -/
theorem rationalIntervalReverseSixTensor_mixed_norm_infinite_le_one (i : Fin 6) :
    (rationalIntervalThreeFamily.mixedTensorPair rationalIntervalPlaneFamily).norm (.inr ())
      ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ]
        rationalIntervalReverseSixTensor i) ≤ 1 := by
  let C := Rat.AbsoluteValue.real.Completion
  let D := TensorProduct.AlgebraTensorModule.distribBaseChange ℚ C
    (Fin 3 → ℚ) (Fin 2 → ℚ)
  have he : D ((1 : C) ⊗ₜ[ℚ] rationalIntervalReverseSixTensor i) =
      ((1 : C) ⊗ₜ[ℚ] rationalIntervalReverseSixTensorLeft i) ⊗ₜ[C]
        ((1 : C) ⊗ₜ[ℚ] rationalIntervalReverseSixTensorRight i) := by
    simp only [rationalIntervalReverseSixTensor, D,
      TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
  have h := rationalIntervalThreeFamily.mixedTensorPair_norm_tmul_completed_le
    rationalIntervalPlaneFamily (.inr ())
    ((1 : C) ⊗ₜ[ℚ] rationalIntervalReverseSixTensorLeft i)
    ((1 : C) ⊗ₜ[ℚ] rationalIntervalReverseSixTensorRight i)
  change (rationalIntervalThreeFamily.mixedTensorPair rationalIntervalPlaneFamily).norm (.inr ())
    (D.symm (((1 : C) ⊗ₜ[ℚ] rationalIntervalReverseSixTensorLeft i) ⊗ₜ[C]
      ((1 : C) ⊗ₜ[ℚ] rationalIntervalReverseSixTensorRight i))) ≤
    rationalIntervalThreeFamily.norm (.inr ())
      ((1 : C) ⊗ₜ[ℚ] rationalIntervalReverseSixTensorLeft i) *
    rationalIntervalPlaneFamily.norm (.inr ())
      ((1 : C) ⊗ₜ[ℚ] rationalIntervalReverseSixTensorRight i) at h
  rw [← he, LinearEquiv.symm_apply_apply,
    rationalIntervalReverseSixTensorLeft_norm_infinite,
    rationalIntervalReverseSixTensorRight_norm_infinite, one_mul] at h
  exact h

private abbrev RationalIntervalReverseTensor := (Fin 3 → ℚ) ⊗[ℚ] (Fin 2 → ℚ)

private def rationalIntervalReverseTensorRankEquiv :
    Fin 6 ≃ Fin (Module.finrank ℚ RationalIntervalReverseTensor) :=
  finCongr (by rw [← finrank_mul_eq_tensor]; simp)

private def rationalIntervalReverseTensorRankBasis :
    Basis (Fin (Module.finrank ℚ RationalIntervalReverseTensor)) ℚ RationalIntervalReverseTensor :=
  rationalIntervalReverseTensorBasis.reindex rationalIntervalReverseTensorRankEquiv

/-- The genuine rational determinant generator in the three-by-two space. -/
def rationalIntervalReverseTensorDeterminantVector :
    ⋀[ℚ]^(Module.finrank ℚ RationalIntervalReverseTensor) RationalIntervalReverseTensor :=
  exteriorPower.ιMulti ℚ _ rationalIntervalReverseTensorRankBasis

theorem rationalIntervalReverseTensorDeterminantVector_ne_zero :
    rationalIntervalReverseTensorDeterminantVector ≠ 0 := by
  intro hz
  have he := congrArg (determinantCoordinateEquiv rationalIntervalReverseTensorRankBasis) hz
  rw [rationalIntervalReverseTensorDeterminantVector, determinantCoordinateEquiv_ιMulti,
    Basis.det_self, map_zero] at he
  exact one_ne_zero he

private theorem rationalIntervalReverseSixTensor_rank_wedge :
    exteriorPower.ιMulti ℚ (Module.finrank ℚ RationalIntervalReverseTensor)
      (rationalIntervalReverseSixTensor ∘ rationalIntervalReverseTensorRankEquiv.symm) =
      (2 : ℚ) • rationalIntervalReverseTensorDeterminantVector := by
  apply (determinantCoordinateEquiv rationalIntervalReverseTensorRankBasis).injective
  rw [map_smul, rationalIntervalReverseTensorDeterminantVector,
    determinantCoordinateEquiv_ιMulti, determinantCoordinateEquiv_ιMulti,
    Basis.det_self, smul_eq_mul, mul_one, rationalIntervalReverseTensorRankBasis,
    Basis.det_reindex]
  have he : (rationalIntervalReverseSixTensor ∘ rationalIntervalReverseTensorRankEquiv.symm) ∘
      rationalIntervalReverseTensorRankEquiv = rationalIntervalReverseSixTensor := by
    funext i
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [he, rationalIntervalReverseSixTensor_basis_det]

/-- The standard determinant of the literal reversed tensor has infinite length at most half. -/
theorem rationalIntervalReverseTensorFamily_determinant_norm_infinite_le_half :
    (rationalIntervalThreeFamily.mixedTensorPair rationalIntervalPlaneFamily).determinant.norm
      (.inr ()) ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ]
        rationalIntervalReverseTensorDeterminantVector) ≤ 1 / 2 := by
  let C := Rat.AbsoluteValue.real.Completion
  let ξ := rationalIntervalThreeFamily.mixedTensorPair rationalIntervalPlaneFamily
  let x : Fin (Module.finrank ℚ RationalIntervalReverseTensor) → RationalIntervalReverseTensor :=
    rationalIntervalReverseSixTensor ∘ rationalIntervalReverseTensorRankEquiv.symm
  have h := ξ.determinant_norm_ιMulti_le (.inr ()) (fun i => (1 : C) ⊗ₜ[ℚ] x i)
  have hw := rationalIntervalReverseSixTensor_rank_wedge
  change exteriorPower.ιMulti ℚ _ x = (2 : ℚ) • rationalIntervalReverseTensorDeterminantVector at hw
  change ξ.determinant.norm (.inr ())
    ((exteriorBaseChangeEquiv ℚ C RationalIntervalReverseTensor _).symm
      (exteriorPower.ιMulti C _ (fun i => (1 : C) ⊗ₜ[ℚ] x i))) ≤
    ∏ i, ξ.norm (.inr ()) ((1 : C) ⊗ₜ[ℚ] x i) at h
  rw [exteriorBaseChangeEquiv_symm_ιMulti_tmul, Finset.prod_const_one, hw] at h
  have he : (1 : C) ⊗ₜ[ℚ] ((2 : ℚ) • rationalIntervalReverseTensorDeterminantVector) =
      (2 : C) • ((1 : C) ⊗ₜ[ℚ] rationalIntervalReverseTensorDeterminantVector) := by
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, TensorProduct.smul_tmul']
    simp only [map_ofNat, smul_eq_mul, mul_one]
  have hs := ξ.determinant.norm_smul (.inr ()) (2 : C)
    ((1 : C) ⊗ₜ[ℚ] rationalIntervalReverseTensorDeterminantVector)
  have hscaled := ((congrArg (ξ.determinant.norm (.inr ())) he).trans hs).symm.trans_le h
  have htwo : ‖(2 : C)‖ = 2 :=
    (rationalRealCompletionEquiv_norm (2 : C)).symm.trans
      ((congrArg norm (show rationalRealCompletionEquiv (2 : C) = (2 : ℝ)
        from map_ofNat _ 2)).trans (by norm_num))
  have hnorm := (congrArg (fun a : ℝ => a * ξ.determinant.norm (.inr ())
    ((1 : C) ⊗ₜ[ℚ] rationalIntervalReverseTensorDeterminantVector)) htwo).symm.trans_le hscaled
  have hprod : (∏ i, ξ.norm (.inr ()) ((1 : C) ⊗ₜ[ℚ] x i)) ≤ 1 := by
    calc
      _ ≤ ∏ _ : Fin (Module.finrank ℚ RationalIntervalReverseTensor), (1 : ℝ) :=
        Finset.prod_le_prod (fun i _ => ξ.norm_nonneg _ _)
          (fun i _ => rationalIntervalReverseSixTensor_mixed_norm_infinite_le_one
            (rationalIntervalReverseTensorRankEquiv.symm i))
      _ = 1 := by simp
  linarith

private abbrev ReverseTensorIndices : Unit ⊕ Unit → Type
  | .inl _ => Fin 3
  | .inr _ => Fin 2

private def reverseTensorBasisIndex (i : Fin 6) : ∀ j, ReverseTensorIndices j :=
  fun j => match j with
  | .inl _ => ((finProdFinEquiv : Fin 3 × Fin 2 ≃ Fin 6).symm i).1
  | .inr _ => ((finProdFinEquiv : Fin 3 × Fin 2 ≃ Fin 6).symm i).2

private theorem reverseTensorBasisIndex_injective : Function.Injective reverseTensorBasisIndex := by
  intro i j h
  apply (finProdFinEquiv : Fin 3 × Fin 2 ≃ Fin 6).symm.injective
  exact Prod.ext (congrFun h (.inl ())) (congrFun h (.inr ()))

/-- Every genuine completed tensor coordinate is bounded by the actual finite mixed norm. -/
theorem rationalIntervalReverseTensorFamily_coordinate_norm_le_prime (q : Nat.Primes)
    (i : Fin 6)
    (z : (rationalAdelicStructure.ϕ (.inl q)).Completion ⊗[ℚ] RationalIntervalReverseTensor) :
    ‖(rationalIntervalReverseTensorBasis.baseChange
      (rationalAdelicStructure.ϕ (.inl q)).Completion).equivFun z i‖ ≤
      (rationalIntervalThreeFamily.mixedTensorPair rationalIntervalPlaneFamily).norm
        (.inl q) z := by
  classical
  let C := (rationalAdelicStructure.ϕ (.inl q)).Completion
  let ξ := NormFamily.tensorPairFactors rationalIntervalThreeFamily rationalIntervalPlaneFamily
  let b : ∀ j, Basis (ReverseTensorIndices j) ℚ
      (BinaryTensorFactors (Fin 3 → ℚ) (Fin 2 → ℚ) j) := fun j => match j with
    | .inl _ => Pi.basisFun ℚ (Fin 3)
    | .inr _ => Pi.basisFun ℚ (Fin 2)
  let : ∀ j, Fintype (ReverseTensorIndices j) := fun j => by cases j <;> infer_instance
  let : ∀ j, DecidableEq (ReverseTensorIndices j) := fun j => by cases j <;> infer_instance
  let B := binaryTensorEquiv ℚ (BinaryTensorFactors (Fin 3 → ℚ) (Fin 2 → ℚ))
  let bπ := Basis.piTensorProduct b
  let t := B.symm.toLinearMap.baseChange C z
  have hb (k : Fin 6) : B.symm (rationalIntervalReverseTensorBasis k) =
      bπ (reverseTensorBasisIndex k) := by
    apply B.injective
    simp only [LinearEquiv.apply_symm_apply, bπ, Basis.piTensorProduct_apply,
      B, binaryTensorEquiv_tprod]
    simp only [rationalIntervalReverseTensorBasis, Basis.reindex_apply,
      Basis.tensorProduct_apply', reverseTensorBasisIndex, b]
  have hc : (bπ.baseChange C).coord (reverseTensorBasisIndex i) ∘ₗ
      B.symm.toLinearMap.baseChange C =
        (rationalIntervalReverseTensorBasis.baseChange C).coord i := by
    apply (rationalIntervalReverseTensorBasis.baseChange C).ext
    intro k
    rw [LinearMap.comp_apply, Basis.baseChange_apply, LinearMap.baseChange_tmul]
    simp only [LinearEquiv.coe_coe, hb]
    rw [← Basis.baseChange_apply, ← Basis.baseChange_apply]
    simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply,
      reverseTensorBasisIndex_injective.eq_iff]
  have hd (j : Unit ⊕ Unit) (k : ReverseTensorIndices j) :
      (ξ j).dual.norm (.inl q) ((1 : C) ⊗ₜ[ℚ] (b j).dualBasis k) ≤ 1 := by
    cases j with
    | inl u =>
      cases u
      apply rationalIntervalThreeFamily.dual_norm_le _ _ zero_le_one
      intro x
      rw [NormFamily.dualBaseChange_one_dualBasis_apply, one_mul,
        rationalIntervalThreeFamily_norm_prime]
      exact norm_le_pi_norm _ k
    | inr u =>
      cases u
      apply rationalIntervalPlaneFamily.dual_norm_le _ _ zero_le_one
      intro x
      rw [NormFamily.dualBaseChange_one_dualBasis_apply, one_mul,
        rationalIntervalPlaneFamily_norm_prime]
      exact norm_le_pi_norm _ k
  have h := NormFamily.norm_tensor_coordinate_le_injective b ξ (.inl q)
    (reverseTensorBasisIndex i) t
  have he := LinearMap.congr_fun hc z
  change (bπ.baseChange C).equivFun t (reverseTensorBasisIndex i) =
    (rationalIntervalReverseTensorBasis.baseChange C).equivFun z i at he
  rw [he] at h
  have hp : (∏ j, (ξ j).dual.norm (.inl q)
      ((1 : C) ⊗ₜ[ℚ] (b j).dualBasis (reverseTensorBasisIndex i j))) ≤ 1 := by
    calc
      _ ≤ ∏ _ : Unit ⊕ Unit, (1 : ℝ) :=
        Finset.prod_le_prod (fun j _ => (ξ j).dual.norm_nonneg _ _)
          (fun j _ => hd j _)
      _ = 1 := by simp
  have hm : (NormFamily.injectiveTensor ξ).norm (.inl q) t =
      (rationalIntervalThreeFamily.mixedTensorPair rationalIntervalPlaneFamily).norm
        (.inl q) z := by
    rw [NormFamily.mixedTensorPair_norm_of_mem_Ωfin _ _ _
      (rationalAdelicStructure_prime_mem_fin q)]
    rfl
  exact h.trans (by
    rw [← hm]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp
      ((NormFamily.injectiveTensor ξ).norm_nonneg (.inl q) t))

/-- Completed standard tensor basis vectors have finite mixed norm at most one. -/
theorem rationalIntervalReverseTensorFamily_norm_basis_prime_le_one
    (q : Nat.Primes) (i : Fin 6) :
    (rationalIntervalThreeFamily.mixedTensorPair rationalIntervalPlaneFamily).norm (.inl q)
      ((1 : (rationalAdelicStructure.ϕ (.inl q)).Completion) ⊗ₜ[ℚ]
        rationalIntervalReverseTensorBasis i) ≤ 1 := by
  let C := (rationalAdelicStructure.ϕ (.inl q)).Completion
  let j := (finProdFinEquiv : Fin 3 × Fin 2 ≃ Fin 6).symm i
  let D := TensorProduct.AlgebraTensorModule.distribBaseChange ℚ C
    (Fin 3 → ℚ) (Fin 2 → ℚ)
  have hb : rationalIntervalReverseTensorBasis i =
      Pi.basisFun ℚ (Fin 3) j.1 ⊗ₜ[ℚ] Pi.basisFun ℚ (Fin 2) j.2 := by
    simp only [rationalIntervalReverseTensorBasis, Basis.reindex_apply,
      Basis.tensorProduct_apply', j]
  have he : D ((1 : C) ⊗ₜ[ℚ] rationalIntervalReverseTensorBasis i) =
      ((1 : C) ⊗ₜ[ℚ] Pi.basisFun ℚ (Fin 3) j.1) ⊗ₜ[C]
        ((1 : C) ⊗ₜ[ℚ] Pi.basisFun ℚ (Fin 2) j.2) := by
    simp only [hb, D, TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
  have h := rationalIntervalThreeFamily.mixedTensorPair_norm_tmul_completed_le
    rationalIntervalPlaneFamily (.inl q)
    ((1 : C) ⊗ₜ[ℚ] Pi.basisFun ℚ (Fin 3) j.1)
    ((1 : C) ⊗ₜ[ℚ] Pi.basisFun ℚ (Fin 2) j.2)
  have hz : D.symm (((1 : C) ⊗ₜ[ℚ] Pi.basisFun ℚ (Fin 3) j.1) ⊗ₜ[C]
      ((1 : C) ⊗ₜ[ℚ] Pi.basisFun ℚ (Fin 2) j.2)) =
      (1 : C) ⊗ₜ[ℚ] rationalIntervalReverseTensorBasis i := by
    rw [← he, LinearEquiv.symm_apply_apply]
  rw [hz] at h
  have hl : rationalIntervalThreeFamily.norm (.inl q)
      ((1 : C) ⊗ₜ[ℚ] Pi.basisFun ℚ (Fin 3) j.1) = 1 :=
    (NormFamily.ofBasis_norm_tmul_basis (S := rationalAdelicStructure)
      (E := Fin 3 → ℚ) (Pi.basisFun ℚ (Fin 3)) (.inl q) 1 j.1).trans norm_one
  have hr : rationalIntervalPlaneFamily.norm (.inl q)
      ((1 : C) ⊗ₜ[ℚ] Pi.basisFun ℚ (Fin 2) j.2) = 1 :=
    (NormFamily.ofBasis_norm_tmul_basis (S := rationalAdelicStructure)
      (E := Fin 2 → ℚ) (Pi.basisFun ℚ (Fin 2)) (.inl q) 1 j.2).trans norm_one
  simpa only [hl, hr, one_mul] using h

/-- The actual finite mixed tensor determinant length is exactly one at every prime. -/
theorem rationalIntervalReverseTensorFamily_determinant_norm_prime (q : Nat.Primes) :
    (rationalIntervalThreeFamily.mixedTensorPair rationalIntervalPlaneFamily).determinant.norm
      (.inl q) ((1 : (rationalAdelicStructure.ϕ (.inl q)).Completion) ⊗ₜ[ℚ]
        rationalIntervalReverseTensorDeterminantVector) = 1 := by
  classical
  let C := (rationalAdelicStructure.ϕ (.inl q)).Completion
  let : IsUltrametricDist C := AbsoluteValue.isUltrametricDist_completion _
    (rationalAdelicStructure_prime_mem_fin q)
  let ξ := rationalIntervalThreeFamily.mixedTensorPair rationalIntervalPlaneFamily
  let e := rationalIntervalReverseTensorRankEquiv
  let b := rationalIntervalReverseTensorRankBasis
  let B := b.baseChange C
  have hB : B = (rationalIntervalReverseTensorBasis.baseChange C).reindex e := by
    ext i
    simp only [B, b, e, rationalIntervalReverseTensorRankBasis,
      Basis.baseChange_apply, Basis.reindex_apply]
  have hb (i : Fin (Module.finrank ℚ RationalIntervalReverseTensor)) :
      ξ.norm (.inl q) (B i) ≤ 1 := by
    rw [hB, Basis.reindex_apply, Basis.baseChange_apply]
    exact rationalIntervalReverseTensorFamily_norm_basis_prime_le_one q _
  have hd (v : Fin (Module.finrank ℚ RationalIntervalReverseTensor) →
      C ⊗[ℚ] RationalIntervalReverseTensor) :
      ‖B.det v‖ ≤ ∏ i, ξ.norm (.inl q) (v i) := by
    rw [hB, Basis.det_reindex, Basis.det_apply]
    have h := norm_det_le_prod_of_entry_le
      ((rationalIntervalReverseTensorBasis.baseChange C).toMatrix (v ∘ e))
      (fun _ => (1 : ℝ)) (fun j => ξ.norm (.inl q) (v (e j))) (fun i j => ?_)
    · rw [Finset.prod_const_one, one_mul,
        e.prod_comp (fun j => ξ.norm (.inl q) (v j))] at h
      exact h
    · rw [one_mul, Basis.toMatrix_apply]
      exact rationalIntervalReverseTensorFamily_coordinate_norm_le_prime q i (v (e j))
  have hvol := NormFamily.determinant_norm_completedBasis_eq_one_of_det_bound ξ
    (by rw [← finrank_mul_eq_tensor]; simp) (.inl q) B hb hd
  have he : ⇑B = fun i => (1 : C) ⊗ₜ[ℚ] b i := by
    ext i
    exact Basis.baseChange_apply _ _ _
  rw [he, exteriorBaseChangeEquiv_symm_ιMulti_tmul, Finset.prod_const_one] at hvol
  exact hvol

/-- The reversed determinant logarithm obeys the actual infinite-place indicator bound. -/
theorem rationalIntervalReverseTensorBundle_determinant_logNorm_le
    (ω : rationalAdelicStructure.Ω) :
    rationalIntervalReverseTensorBundle.toNormFamily.determinant.logNorm
      rationalIntervalReverseTensorDeterminantVector ω ≤
    rationalAdelicStructure.Ωinf.indicator (fun _ => -Real.log 2) ω := by
  have hp := rationalIntervalReverseTensorBundle.toNormFamily.determinant.norm_rational_pos ω
    rationalIntervalReverseTensorDeterminantVector_ne_zero
  cases ω with
  | inl q =>
      have hq : Sum.inl q ∉ rationalAdelicStructure.Ωinf :=
        fun h => h (rationalAdelicStructure_prime_mem_fin q)
      rw [Set.indicator_of_notMem hq]
      change Real.log ((rationalIntervalThreeFamily.mixedTensorPair
        rationalIntervalPlaneFamily).determinant.norm (.inl q) _) ≤ 0
      rw [rationalIntervalReverseTensorFamily_determinant_norm_prime, Real.log_one]
  | inr u =>
      cases u
      rw [Set.indicator_of_mem rationalAdelicStructure_infinite_mem_inf]
      exact (Real.log_le_log hp
        rationalIntervalReverseTensorFamily_determinant_norm_infinite_le_half).trans_eq
          (by rw [one_div, Real.log_inv])

/-- The actual three-by-two tensor has native degree at least `log 2`. -/
theorem rationalIntervalReverseTensorBundle_log_two_le_degree :
    Real.log 2 ≤ rationalIntervalReverseTensorBundle.degree
      (Or.inl inferInstance) rationalAdelicStructure_isRCLike := by
  let hS : DiscreteMeasurableSpace rationalAdelicStructure.Ω ∨
      rationalAdelicStructure.HasCommonCountableDenseSubfield := Or.inl inferInstance
  let D := rationalAdelicStructure.Ωinf.indicator (fun _ => -Real.log 2)
  have hf : Integrable
      (rationalIntervalReverseTensorBundle.toNormFamily.determinant.logNorm
        rationalIntervalReverseTensorDeterminantVector) rationalAdelicStructure.v :=
    (rationalIntervalReverseTensorBundle.determinantOfMeasurableBase hS
      rationalAdelicStructure_isRCLike).integrable_logNorm _
  have hD : Integrable D rationalAdelicStructure.v :=
    (integrable_indicator_iff rationalAdelicStructure.measurableSet_Ωinf).mpr
      (integrableOn_const (by rw [rationalAdelicStructure_v_Ωinf]; exact ENNReal.one_ne_top))
  have h := integral_mono hf hD rationalIntervalReverseTensorBundle_determinant_logNorm_le
  change (∫ ω, rationalIntervalReverseTensorBundle.toNormFamily.determinant.logNorm
    rationalIntervalReverseTensorDeterminantVector ω ∂rationalAdelicStructure.v) ≤
    ∫ ω, rationalAdelicStructure.Ωinf.indicator (fun _ => -Real.log 2) ω
      ∂rationalAdelicStructure.v at h
  rw [integral_indicator_const _ rationalAdelicStructure.measurableSet_Ωinf,
    Measure.real_def, rationalAdelicStructure_v_Ωinf, ENNReal.toReal_one, one_smul] at h
  rw [rationalIntervalReverseTensorBundle.degree_eq_neg_integral hS
    rationalAdelicStructure_isRCLike
      ⟨rationalIntervalReverseTensorDeterminantVector,
        rationalIntervalReverseTensorDeterminantVector_ne_zero⟩]
  linarith

theorem rationalIntervalReverseTensorBundle_degree_pos :
    0 < rationalIntervalReverseTensorBundle.degree
      (Or.inl inferInstance) rationalAdelicStructure_isRCLike :=
  (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
    rationalIntervalReverseTensorBundle_log_two_le_degree

/-- The exact reversed strongly adelic factors violate the dimension-weighted equality. -/
theorem rationalIntervalReverseTensorBundle_degree_strict :
    2 * rationalIntervalThreeBundle.degree (Or.inl inferInstance)
      rationalAdelicStructure_isRCLike +
      3 * rationalIntervalPlaneBundle.degree (Or.inl inferInstance)
        rationalAdelicStructure_isRCLike <
    rationalIntervalReverseTensorBundle.degree (Or.inl inferInstance)
      rationalAdelicStructure_isRCLike := by
  simpa only [rationalIntervalThreeBundle_degree_eq_zero,
    rationalIntervalPlaneBundle_degree_eq_zero, mul_zero, add_zero] using
      rationalIntervalReverseTensorBundle_degree_pos

/-- All actual global extras of the original three-by-two interval example hold together. -/
theorem rationalIntervalReverseTensorBundle_counterexample :
    rationalIntervalThreeBundle.IsStronglyAdelic ∧
    rationalIntervalPlaneBundle.IsStronglyAdelic ∧
    rationalIntervalThreeBundle.degree (Or.inl inferInstance)
      rationalAdelicStructure_isRCLike = 0 ∧
    rationalIntervalPlaneBundle.degree (Or.inl inferInstance)
      rationalAdelicStructure_isRCLike = 0 ∧
    (∀ ω : rationalAdelicStructure.Ω,
      rationalIntervalThreeFamily.determinant.norm ω
        ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ]
          rationalStandardDeterminantVector 3) = 1 ∧
      rationalIntervalPlaneFamily.determinant.norm ω
        ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ]
          rationalStandardDeterminantVector 2) = 1) ∧
    Real.log 2 ≤ rationalIntervalReverseTensorBundle.degree
      (Or.inl inferInstance) rationalAdelicStructure_isRCLike :=
  ⟨rationalIntervalThreeBundle_isStronglyAdelic, rationalIntervalPlaneBundle_isStronglyAdelic,
    rationalIntervalThreeBundle_degree_eq_zero, rationalIntervalPlaneBundle_degree_eq_zero,
    fun ω => ⟨rationalIntervalThreeFamily_determinant_norm_standard ω,
      rationalIntervalPlaneFamily_determinant_norm_standard ω⟩,
    rationalIntervalReverseTensorBundle_log_two_le_degree⟩

end ArakelovGeometry
