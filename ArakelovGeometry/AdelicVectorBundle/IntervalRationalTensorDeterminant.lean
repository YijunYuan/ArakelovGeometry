/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.IntervalRationalTensorWitness

/-!
# Actual determinant lengths for the rational interval mixed tensor

The rational tensor basis generator is an actual top exterior vector. The
six rational witnesses give its real completed determinant length at most one half.
-/

@[expose] public section

open scoped TensorProduct
open Module MeasureTheory

noncomputable section
namespace ArakelovGeometry
open AdelicStructure

/-- The rational tensor product of the interval plane and interval three-space. -/
abbrev RationalIntervalTensor := (Fin 2 → ℚ) ⊗[ℚ] (Fin 3 → ℚ)

/-- Identify the six tensor coordinates with the rank of the rational tensor space. -/
def rationalIntervalTensorRankEquiv :
    Fin 6 ≃ Fin (Module.finrank ℚ RationalIntervalTensor) :=
  finCongr (by rw [← finrank_mul_eq_tensor]; simp)

/-- The tensor basis indexed by the rank of the rational tensor space. -/
def rationalIntervalTensorRankBasis :
    Basis (Fin (Module.finrank ℚ RationalIntervalTensor)) ℚ RationalIntervalTensor :=
  rationalIntervalTensorBasis.reindex rationalIntervalTensorRankEquiv

/-- The actual top exterior generator of the standard rational tensor basis. -/
def rationalIntervalTensorDeterminantVector :
    ⋀[ℚ]^(Module.finrank ℚ RationalIntervalTensor) RationalIntervalTensor :=
  exteriorPower.ιMulti ℚ _ rationalIntervalTensorRankBasis

/-- The actual rational tensor determinant generator is nonzero. -/
theorem rationalIntervalTensorDeterminantVector_ne_zero :
    rationalIntervalTensorDeterminantVector ≠ 0 := by
  intro hz
  have he := congrArg (determinantCoordinateEquiv rationalIntervalTensorRankBasis) hz
  rw [rationalIntervalTensorDeterminantVector, determinantCoordinateEquiv_ιMulti,
    Basis.det_self, map_zero] at he
  exact one_ne_zero he

private theorem rationalIntervalSixTensor_rank_wedge :
    exteriorPower.ιMulti ℚ (Module.finrank ℚ RationalIntervalTensor)
      (rationalIntervalSixTensor ∘ rationalIntervalTensorRankEquiv.symm) =
      (2 : ℚ) • rationalIntervalTensorDeterminantVector := by
  apply (determinantCoordinateEquiv rationalIntervalTensorRankBasis).injective
  rw [map_smul, rationalIntervalTensorDeterminantVector,
    determinantCoordinateEquiv_ιMulti, determinantCoordinateEquiv_ιMulti,
    Basis.det_self, smul_eq_mul, mul_one, rationalIntervalTensorRankBasis, Basis.det_reindex]
  have he : (rationalIntervalSixTensor ∘ rationalIntervalTensorRankEquiv.symm) ∘
      rationalIntervalTensorRankEquiv = rationalIntervalSixTensor := by
    funext i
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [he, rationalIntervalSixTensor_basis_det]

/-- The genuine real completed mixed determinant length is at most one half. -/
theorem rationalIntervalTensorFamily_determinant_norm_infinite_le_half :
    (rationalIntervalPlaneFamily.mixedTensorPair rationalIntervalThreeFamily).determinant.norm
      (.inr ()) ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ]
        rationalIntervalTensorDeterminantVector) ≤ 1 / 2 := by
  let C := Rat.AbsoluteValue.real.Completion
  let ξ := rationalIntervalPlaneFamily.mixedTensorPair rationalIntervalThreeFamily
  let x : Fin (Module.finrank ℚ RationalIntervalTensor) → RationalIntervalTensor :=
    rationalIntervalSixTensor ∘ rationalIntervalTensorRankEquiv.symm
  have h := ξ.determinant_norm_ιMulti_le (.inr ()) (fun i => (1 : C) ⊗ₜ[ℚ] x i)
  have hw := rationalIntervalSixTensor_rank_wedge
  change exteriorPower.ιMulti ℚ _ x = (2 : ℚ) • rationalIntervalTensorDeterminantVector at hw
  change ξ.determinant.norm (.inr ())
    ((exteriorBaseChangeEquiv ℚ C RationalIntervalTensor _).symm
      (exteriorPower.ιMulti C _ (fun i => (1 : C) ⊗ₜ[ℚ] x i))) ≤
    ∏ i, ξ.norm (.inr ()) ((1 : C) ⊗ₜ[ℚ] x i) at h
  rw [exteriorBaseChangeEquiv_symm_ιMulti_tmul, Finset.prod_const_one, hw] at h
  have he : (1 : C) ⊗ₜ[ℚ] ((2 : ℚ) • rationalIntervalTensorDeterminantVector) =
      (2 : C) • ((1 : C) ⊗ₜ[ℚ] rationalIntervalTensorDeterminantVector) := by
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, TensorProduct.smul_tmul']
    simp only [map_ofNat, smul_eq_mul, mul_one]
  have hs := ξ.determinant.norm_smul (.inr ()) (2 : C)
    ((1 : C) ⊗ₜ[ℚ] rationalIntervalTensorDeterminantVector)
  have hscaled := ((congrArg (ξ.determinant.norm (.inr ())) he).trans hs).symm.trans_le h
  have htwo : ‖(2 : C)‖ = 2 :=
    (rationalRealCompletionEquiv_norm (2 : C)).symm.trans
      ((congrArg norm (show rationalRealCompletionEquiv (2 : C) = (2 : ℝ)
        from map_ofNat _ 2)).trans (by norm_num))
  have hnorm := (congrArg (fun a : ℝ => a * ξ.determinant.norm (.inr ())
    ((1 : C) ⊗ₜ[ℚ] rationalIntervalTensorDeterminantVector)) htwo).symm.trans_le hscaled
  have hprod : (∏ i, ξ.norm (.inr ()) ((1 : C) ⊗ₜ[ℚ] x i)) ≤ 1 := by
    calc
      _ ≤ ∏ _ : Fin (Module.finrank ℚ RationalIntervalTensor), (1 : ℝ) :=
        Finset.prod_le_prod₀ (fun i _ => ξ.norm_nonneg _ _)
          (fun i _ => rationalIntervalSixTensor_mixed_norm_infinite_le_one
            (rationalIntervalTensorRankEquiv.symm i))
      _ = 1 := by simp
  linarith

end ArakelovGeometry
