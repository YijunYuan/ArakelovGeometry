/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Tensor.Pair
public import ArakelovGeometry.AdelicVectorBundle.Degree.Basic
public import ArakelovGeometry.AdelicVectorBundle.Examples.Interval.TensorDeterminant
import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.AdelicVectorBundle.Examples.Interval.Degrees

/-!
# A strict global degree inequality for the rational interval tensor

The actual mixed tensor bundle has degree at least `Real.log 2`, while both
factor degrees vanish. This gives a global counterexample to the unrestricted
mixed tensor degree equality printed in Proposition 4.3.19.
-/

@[expose] public section

open scoped TensorProduct
open Module MeasureTheory

noncomputable section
namespace ArakelovGeometry
open AdelicStructure

/-- The actual global mixed tensor bundle of the rational interval factors. -/
def rationalIntervalTensorBundle :
    AdelicVectorBundle rationalAdelicStructure ((Fin 2 → ℚ) ⊗[ℚ] (Fin 3 → ℚ)) :=
  rationalIntervalPlaneBundle.mixedTensorPair rationalIntervalThreeBundle
    (Or.inl inferInstance) rationalAdelicStructure_isRCLike

@[simp]
theorem rationalIntervalTensorBundle_toNormFamily :
    rationalIntervalTensorBundle.toNormFamily =
      rationalIntervalPlaneFamily.mixedTensorPair rationalIntervalThreeFamily := rfl

private theorem rationalIntervalPlaneFamily_norm_basis_le_one
    (ω : rationalAdelicStructure.Ω) (i : Fin 2) :
    rationalIntervalPlaneFamily.norm ω
      ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ] (Pi.basisFun ℚ (Fin 2) i)) ≤ 1 := by
  cases ω with
  | inl q =>
      exact (NormFamily.ofBasis_norm_tmul_basis (S := rationalAdelicStructure)
        (E := Fin 2 → ℚ) (Pi.basisFun ℚ (Fin 2)) (.inl q) 1 i).trans_le norm_one.le
  | inr u =>
      cases u
      fin_cases i
      · have he : Pi.basisFun ℚ (Fin 2) 0 = rationalIntervalSixTensorLeft 0 := by
          ext j
          fin_cases j <;> norm_num [Pi.basisFun_apply, Pi.single_apply,
            rationalIntervalSixTensorLeft, Fin.ext_iff]
        change rationalIntervalPlaneFamily.norm (.inr ())
          ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ] Pi.basisFun ℚ (Fin 2) 0) ≤ 1
        exact (congrArg (fun v : Fin 2 → ℚ => rationalIntervalPlaneFamily.norm (.inr ())
          ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ] v)) he).trans_le
            (rationalIntervalSixTensorLeft_norm_infinite 0).le
      · have he : Pi.basisFun ℚ (Fin 2) 1 = rationalIntervalSixTensorLeft 2 := by
          ext j
          fin_cases j <;> norm_num [Pi.basisFun_apply, Pi.single_apply,
            rationalIntervalSixTensorLeft, Fin.ext_iff]
        change rationalIntervalPlaneFamily.norm (.inr ())
          ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ] Pi.basisFun ℚ (Fin 2) 1) ≤ 1
        exact (congrArg (fun v : Fin 2 → ℚ => rationalIntervalPlaneFamily.norm (.inr ())
          ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ] v)) he).trans_le
            (rationalIntervalSixTensorLeft_norm_infinite 2).le

private theorem rationalIntervalThreeFamily_norm_basis_le_one
    (ω : rationalAdelicStructure.Ω) (i : Fin 3) :
    rationalIntervalThreeFamily.norm ω
      ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ] (Pi.basisFun ℚ (Fin 3) i)) ≤ 1 := by
  cases ω with
  | inl q =>
      exact (NormFamily.ofBasis_norm_tmul_basis (S := rationalAdelicStructure)
        (E := Fin 3 → ℚ) (Pi.basisFun ℚ (Fin 3)) (.inl q) 1 i).trans_le norm_one.le
  | inr u =>
      cases u
      fin_cases i
      · have he : Pi.basisFun ℚ (Fin 3) 0 = rationalIntervalSixTensorRight 0 := by
          ext j
          fin_cases j <;> norm_num [Pi.basisFun_apply, Pi.single_apply,
            rationalIntervalSixTensorRight, Fin.ext_iff]
        change rationalIntervalThreeFamily.norm (.inr ())
          ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ] Pi.basisFun ℚ (Fin 3) 0) ≤ 1
        exact (congrArg (fun v : Fin 3 → ℚ => rationalIntervalThreeFamily.norm (.inr ())
          ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ] v)) he).trans_le
            (rationalIntervalSixTensorRight_norm_infinite 0).le
      · have he : Pi.basisFun ℚ (Fin 3) 1 = rationalIntervalSixTensorRight 2 := by
          ext j
          fin_cases j <;> norm_num [Pi.basisFun_apply, Pi.single_apply,
            rationalIntervalSixTensorRight, Fin.ext_iff]
        change rationalIntervalThreeFamily.norm (.inr ())
          ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ] Pi.basisFun ℚ (Fin 3) 1) ≤ 1
        exact (congrArg (fun v : Fin 3 → ℚ => rationalIntervalThreeFamily.norm (.inr ())
          ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ] v)) he).trans_le
            (rationalIntervalSixTensorRight_norm_infinite 2).le
      · have he : Pi.basisFun ℚ (Fin 3) 2 = rationalIntervalSixTensorRight 1 := by
          ext j
          fin_cases j <;> norm_num [Pi.basisFun_apply, Pi.single_apply,
            rationalIntervalSixTensorRight, Fin.ext_iff]
        change rationalIntervalThreeFamily.norm (.inr ())
          ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ] Pi.basisFun ℚ (Fin 3) 2) ≤ 1
        exact (congrArg (fun v : Fin 3 → ℚ => rationalIntervalThreeFamily.norm (.inr ())
          ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ] v)) he).trans_le
            (rationalIntervalSixTensorRight_norm_infinite 1).le

/-- Every standard rational tensor basis vector has completed mixed norm at most one. -/
theorem rationalIntervalTensorFamily_norm_basis_le_one
    (ω : rationalAdelicStructure.Ω) (i : Fin 6) :
    (rationalIntervalPlaneFamily.mixedTensorPair rationalIntervalThreeFamily).norm ω
      ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ]
        rationalIntervalTensorBasis i) ≤ 1 := by
  let C := (rationalAdelicStructure.ϕ ω).Completion
  let j := (finProdFinEquiv : Fin 2 × Fin 3 ≃ Fin 6).symm i
  let D := TensorProduct.AlgebraTensorModule.distribBaseChange ℚ C (Fin 2 → ℚ) (Fin 3 → ℚ)
  have hb : rationalIntervalTensorBasis i =
      Pi.basisFun ℚ (Fin 2) j.1 ⊗ₜ[ℚ] Pi.basisFun ℚ (Fin 3) j.2 := by
    simp only [rationalIntervalTensorBasis, Basis.reindex_apply, Basis.tensorProduct_apply', j]
  have he : D ((1 : C) ⊗ₜ[ℚ] rationalIntervalTensorBasis i) =
      ((1 : C) ⊗ₜ[ℚ] Pi.basisFun ℚ (Fin 2) j.1) ⊗ₜ[C]
        ((1 : C) ⊗ₜ[ℚ] Pi.basisFun ℚ (Fin 3) j.2) := by
    simp only [hb, D, TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
  have h := rationalIntervalPlaneFamily.mixedTensorPair_norm_tmul_completed_le
    rationalIntervalThreeFamily ω
    ((1 : C) ⊗ₜ[ℚ] Pi.basisFun ℚ (Fin 2) j.1)
    ((1 : C) ⊗ₜ[ℚ] Pi.basisFun ℚ (Fin 3) j.2)
  have hz : D.symm (((1 : C) ⊗ₜ[ℚ] Pi.basisFun ℚ (Fin 2) j.1) ⊗ₜ[C]
      ((1 : C) ⊗ₜ[ℚ] Pi.basisFun ℚ (Fin 3) j.2)) =
      (1 : C) ⊗ₜ[ℚ] rationalIntervalTensorBasis i := by
    rw [← he, LinearEquiv.symm_apply_apply]
  rw [hz] at h
  exact h.trans ((mul_le_mul_of_nonneg_right
    (rationalIntervalPlaneFamily_norm_basis_le_one ω j.1)
    (rationalIntervalThreeFamily.norm_nonneg ω _)).trans
      (by simpa only [one_mul] using rationalIntervalThreeFamily_norm_basis_le_one ω j.2))

/-- The actual standard tensor determinant generator has norm at most one at every place. -/
theorem rationalIntervalTensorFamily_determinant_norm_le_one
    (ω : rationalAdelicStructure.Ω) :
    (rationalIntervalPlaneFamily.mixedTensorPair rationalIntervalThreeFamily).determinant.norm ω
      ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ]
        rationalIntervalTensorDeterminantVector) ≤ 1 := by
  let E := (Fin 2 → ℚ) ⊗[ℚ] (Fin 3 → ℚ)
  let C := (rationalAdelicStructure.ϕ ω).Completion
  let e : Fin 6 ≃ Fin (Module.finrank ℚ E) :=
    finCongr (by rw [← finrank_mul_eq_tensor]; simp)
  let b := rationalIntervalTensorBasis.reindex e
  let ξ := rationalIntervalPlaneFamily.mixedTensorPair rationalIntervalThreeFamily
  have ht : exteriorPower.ιMulti ℚ (Module.finrank ℚ E) b =
      rationalIntervalTensorDeterminantVector := rfl
  have h := ξ.determinant_norm_ιMulti_le ω (fun i => (1 : C) ⊗ₜ[ℚ] b i)
  change ξ.determinant.norm ω
    ((exteriorBaseChangeEquiv ℚ C E _).symm
      (exteriorPower.ιMulti C _ (fun i => (1 : C) ⊗ₜ[ℚ] b i))) ≤
    ∏ i, ξ.norm ω ((1 : C) ⊗ₜ[ℚ] b i) at h
  rw [exteriorBaseChangeEquiv_symm_ιMulti_tmul, Finset.prod_const_one, ht] at h
  apply h.trans
  calc
    _ ≤ ∏ _ : Fin (Module.finrank ℚ E), (1 : ℝ) :=
      Finset.prod_le_prod₀ (fun i _ => ξ.norm_nonneg _ _)
        (fun i _ => by
          rw [show b i = rationalIntervalTensorBasis (e.symm i) from Basis.reindex_apply _ _ _]
          exact rationalIntervalTensorFamily_norm_basis_le_one ω (e.symm i))
    _ = 1 := by simp

/-- The genuine determinant logarithm is bounded by the real-place indicator of `-log 2`. -/
theorem rationalIntervalTensorBundle_determinant_logNorm_le
    (ω : rationalAdelicStructure.Ω) :
    rationalIntervalTensorBundle.toNormFamily.determinant.logNorm
      rationalIntervalTensorDeterminantVector ω ≤
    rationalAdelicStructure.Ωinf.indicator (fun _ => -Real.log 2) ω := by
  have hp := rationalIntervalTensorBundle.toNormFamily.determinant.norm_rational_pos ω
    rationalIntervalTensorDeterminantVector_ne_zero
  cases ω with
  | inl q =>
      have hq : Sum.inl q ∉ rationalAdelicStructure.Ωinf :=
        fun h => h (rationalAdelicStructure_prime_mem_fin q)
      rw [Set.indicator_of_notMem hq]
      exact (Real.log_le_log hp
        (rationalIntervalTensorFamily_determinant_norm_le_one (.inl q))).trans_eq Real.log_one
  | inr u =>
      cases u
      rw [Set.indicator_of_mem rationalAdelicStructure_infinite_mem_inf]
      exact (Real.log_le_log hp
        rationalIntervalTensorFamily_determinant_norm_infinite_le_half).trans_eq
          (by rw [one_div, Real.log_inv])

/-- The degree of the actual rational interval mixed tensor bundle is at least `log 2`. -/
theorem rationalIntervalTensorBundle_log_two_le_degree :
    Real.log 2 ≤ rationalIntervalTensorBundle.degree
      (Or.inl inferInstance) rationalAdelicStructure_isRCLike := by
  let hS : DiscreteMeasurableSpace rationalAdelicStructure.Ω ∨
      rationalAdelicStructure.HasCommonCountableDenseSubfield := Or.inl inferInstance
  let D := rationalAdelicStructure.Ωinf.indicator (fun _ => -Real.log 2)
  have hf : Integrable (rationalIntervalTensorBundle.toNormFamily.determinant.logNorm
      rationalIntervalTensorDeterminantVector) rationalAdelicStructure.v :=
    (rationalIntervalTensorBundle.determinantOfMeasurableBase hS
      rationalAdelicStructure_isRCLike).integrable_logNorm _
  have hD : Integrable D rationalAdelicStructure.v :=
    (integrable_indicator_iff rationalAdelicStructure.measurableSet_Ωinf).mpr
      (integrableOn_const (by rw [rationalAdelicStructure_v_Ωinf]; exact ENNReal.one_ne_top))
  have h := integral_mono hf hD rationalIntervalTensorBundle_determinant_logNorm_le
  change (∫ ω, rationalIntervalTensorBundle.toNormFamily.determinant.logNorm
    rationalIntervalTensorDeterminantVector ω ∂rationalAdelicStructure.v) ≤
    ∫ ω, rationalAdelicStructure.Ωinf.indicator (fun _ => -Real.log 2) ω
      ∂rationalAdelicStructure.v at h
  rw [integral_indicator_const _ rationalAdelicStructure.measurableSet_Ωinf,
    Measure.real_def, rationalAdelicStructure_v_Ωinf, ENNReal.toReal_one, one_smul] at h
  rw [rationalIntervalTensorBundle.degree_eq_neg_integral hS
    rationalAdelicStructure_isRCLike
      ⟨rationalIntervalTensorDeterminantVector, rationalIntervalTensorDeterminantVector_ne_zero⟩]
  linarith

/-- This actual rank-six adelic tensor bundle has strictly positive degree. -/
theorem rationalIntervalTensorBundle_degree_pos :
    0 < rationalIntervalTensorBundle.degree
      (Or.inl inferInstance) rationalAdelicStructure_isRCLike :=
  (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
    rationalIntervalTensorBundle_log_two_le_degree

/-- The actual global mixed tensor degree strictly exceeds the weighted factor degrees. -/
theorem rationalIntervalTensorBundle_degree_strict :
    3 * rationalIntervalPlaneBundle.degree (Or.inl inferInstance)
      rationalAdelicStructure_isRCLike +
      2 * rationalIntervalThreeBundle.degree (Or.inl inferInstance)
        rationalAdelicStructure_isRCLike <
    rationalIntervalTensorBundle.degree (Or.inl inferInstance)
      rationalAdelicStructure_isRCLike := by
  simpa only [rationalIntervalPlaneBundle_degree_eq_zero,
    rationalIntervalThreeBundle_degree_eq_zero, mul_zero, add_zero] using
      rationalIntervalTensorBundle_degree_pos

/-- The unrestricted printed mixed tensor degree equality fails for actual rational bundles. -/
theorem rationalIntervalTensorBundle_degree_ne_weighted_factors :
    rationalIntervalTensorBundle.degree (Or.inl inferInstance) rationalAdelicStructure_isRCLike ≠
    3 * rationalIntervalPlaneBundle.degree (Or.inl inferInstance)
      rationalAdelicStructure_isRCLike +
      2 * rationalIntervalThreeBundle.degree (Or.inl inferInstance)
        rationalAdelicStructure_isRCLike :=
  ne_of_gt rationalIntervalTensorBundle_degree_strict

end ArakelovGeometry
