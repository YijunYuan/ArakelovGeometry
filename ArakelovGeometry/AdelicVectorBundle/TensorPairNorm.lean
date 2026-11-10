/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DeterminantTensorBaseChange
public import ArakelovGeometry.AdelicVectorBundle.TensorPair

/-!
# Actual binary projective and mixed tensor norm families

These are the existing finite tensor norms on the ordinary binary tensor
product, using the same canonical binary equivalence as the accepted
injective pair family. Completed tensor base change remains canonical.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u v w

section Algebra

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  (E F : Type w) [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

/-- Finite tensor base change and binary tensor base change commute with
the existing canonical binary equivalence. -/
theorem tensorBaseChangeEquiv_binary :
    (binaryTensorEquiv L (fun i ↦ L ⊗[K] BinaryTensorFactors E F i)).toLinearMap ∘ₗ
      (tensorBaseChangeEquiv K L (BinaryTensorFactors E F)).toLinearMap =
    (TensorProduct.AlgebraTensorModule.distribBaseChange K L E F).toLinearMap ∘ₗ
      (binaryTensorEquiv K (BinaryTensorFactors E F)).toLinearMap.baseChange L := by
  apply LinearMap.restrictScalars_injective K
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change binaryTensorEquiv L (fun i ↦ L ⊗[K] BinaryTensorFactors E F i)
      (tensorBaseChangeEquiv K L (BinaryTensorFactors E F) (a ⊗ₜ[K] (⨂ₜ[K] i, x i))) =
    TensorProduct.AlgebraTensorModule.distribBaseChange K L E F
      ((binaryTensorEquiv K (BinaryTensorFactors E F)).toLinearMap.baseChange L
        (a ⊗ₜ[K] (⨂ₜ[K] i, x i)))
  simp only [tensorBaseChangeEquiv_tmul_tprod, map_smul, binaryTensorEquiv_tprod,
    LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- A pure tensor of completed vectors corresponds to the canonical finite
pure tensor after the actual completed binary pullback. -/
theorem tensorBaseChangeEquiv_binary_symm_tmul
    (x : L ⊗[K] E) (y : L ⊗[K] F) :
    tensorBaseChangeEquiv K L (BinaryTensorFactors E F)
      ((binaryTensorEquiv K (BinaryTensorFactors E F)).symm.toLinearMap.baseChange L
        ((TensorProduct.AlgebraTensorModule.distribBaseChange K L E F).symm
          (x ⊗ₜ[L] y))) =
      (⨂ₜ[L] i, match i with | .inl _ => x | .inr _ => y) := by
  let A := TensorProduct.AlgebraTensorModule.distribBaseChange K L E F
  let B := (binaryTensorEquiv K (BinaryTensorFactors E F)).baseChange K L _ _
  let P := binaryTensorEquiv L (fun i ↦ L ⊗[K] BinaryTensorFactors E F i)
  have he := DFunLike.congr_fun (tensorBaseChangeEquiv_binary K L E F)
    (B.symm (A.symm (x ⊗ₜ[L] y)))
  apply P.injective
  change P (tensorBaseChangeEquiv K L (BinaryTensorFactors E F)
    (B.symm (A.symm (x ⊗ₜ[L] y)))) =
      P (⨂ₜ[L] i, match i with | .inl _ => x | .inr _ => y)
  change P (tensorBaseChangeEquiv K L (BinaryTensorFactors E F)
    (B.symm (A.symm (x ⊗ₜ[L] y)))) = A (B (B.symm (A.symm (x ⊗ₜ[L] y)))) at he
  simpa only [LinearEquiv.apply_symm_apply, P, binaryTensorEquiv_tprod] using he

end Algebra

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E F : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace NormFamily

/-- The actual projective norm on the ordinary binary tensor product. -/
def projectiveTensorPair (ξ : NormFamily S E) (η : NormFamily S F) :
    NormFamily S (E ⊗[K] F) :=
  (projectiveTensor (tensorPairFactors ξ η)).pullback
    (binaryTensorEquiv K (BinaryTensorFactors E F)).symm.toLinearMap
    (binaryTensorEquiv K (BinaryTensorFactors E F)).symm.injective

/-- The actual mixed norm on the ordinary binary tensor product. -/
def mixedTensorPair (ξ : NormFamily S E) (η : NormFamily S F) :
    NormFamily S (E ⊗[K] F) :=
  (mixedTensor (tensorPairFactors ξ η)).pullback
    (binaryTensorEquiv K (BinaryTensorFactors E F)).symm.toLinearMap
    (binaryTensorEquiv K (BinaryTensorFactors E F)).symm.injective

/-- The completed projective binary tensor contracts pure tensors by the
product of the actual completed factor norms. -/
theorem projectiveTensorPair_norm_tmul_completed_le
    (ξ : NormFamily S E) (η : NormFamily S F) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] E) (y : (S.ϕ ω).Completion ⊗[K] F) :
    (ξ.projectiveTensorPair η).norm ω
      ((TensorProduct.AlgebraTensorModule.distribBaseChange K (S.ϕ ω).Completion E F).symm
        (x ⊗ₜ[(S.ϕ ω).Completion] y)) ≤ ξ.norm ω x * η.norm ω y := by
  let X : ∀ i, (S.ϕ ω).Completion ⊗[K] BinaryTensorFactors E F i :=
    fun i ↦ match i with | .inl _ => x | .inr _ => y
  have hz : (binaryTensorEquiv K (BinaryTensorFactors E F)).symm.toLinearMap.baseChange
      (S.ϕ ω).Completion
      ((TensorProduct.AlgebraTensorModule.distribBaseChange K (S.ϕ ω).Completion E F).symm
        (x ⊗ₜ[(S.ϕ ω).Completion] y)) =
      (tensorBaseChangeEquiv K (S.ϕ ω).Completion (BinaryTensorFactors E F)).symm
        (⨂ₜ[(S.ϕ ω).Completion] i, X i) := by
    apply (tensorBaseChangeEquiv K (S.ϕ ω).Completion (BinaryTensorFactors E F)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact tensorBaseChangeEquiv_binary_symm_tmul K (S.ϕ ω).Completion E F x y
  change (projectiveTensor (tensorPairFactors ξ η)).norm ω _ ≤ _
  rw [hz]
  have hb := projectiveTensor_norm_tprod_le (tensorPairFactors ξ η) ω X
  simpa only [Fintype.prod_sum_type, Fintype.prod_unique, tensorPairFactors, X] using hb

/-- The actual injective binary tensor norm is bounded by the projective one. -/
theorem injectiveTensorPair_norm_le_projectiveTensorPair_norm
    (ξ : NormFamily S E) (η : NormFamily S F) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⊗[K] F)) :
    (ξ.injectiveTensorPair η).norm ω z ≤ (ξ.projectiveTensorPair η).norm ω z :=
  injectiveTensor_norm_le_projectiveTensor_norm (tensorPairFactors ξ η) ω _

/-- The source mixed binary tensor norm is the accepted injective norm at
each non-Archimedean place. -/
theorem mixedTensorPair_norm_of_mem_Ωfin (ξ : NormFamily S E) (η : NormFamily S F)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⊗[K] F)) :
    (ξ.mixedTensorPair η).norm ω z = (ξ.injectiveTensorPair η).norm ω z :=
  mixedTensor_norm_of_mem_Ωfin (tensorPairFactors ξ η) ω hω _

/-- The source mixed binary tensor norm is the actual projective norm at
each Archimedean place. -/
theorem mixedTensorPair_norm_of_not_mem_Ωfin (ξ : NormFamily S E) (η : NormFamily S F)
    (ω : S.Ω) (hω : ω ∉ S.Ωfin)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⊗[K] F)) :
    (ξ.mixedTensorPair η).norm ω z = (ξ.projectiveTensorPair η).norm ω z :=
  mixedTensor_norm_of_not_mem_Ωfin (tensorPairFactors ξ η) ω hω _

/-- The actual mixed binary norm is bounded by the projective one at every place. -/
theorem mixedTensorPair_norm_le_projectiveTensorPair_norm
    (ξ : NormFamily S E) (η : NormFamily S F) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⊗[K] F)) :
    (ξ.mixedTensorPair η).norm ω z ≤ (ξ.projectiveTensorPair η).norm ω z := by
  by_cases hω : ω ∈ S.Ωfin
  · rw [mixedTensorPair_norm_of_mem_Ωfin ξ η ω hω]
    exact injectiveTensorPair_norm_le_projectiveTensorPair_norm ξ η ω z
  · rw [mixedTensorPair_norm_of_not_mem_Ωfin ξ η ω hω]

/-- The actual mixed binary tensor contracts pure completed tensors by
the product of the actual completed factor norms. -/
theorem mixedTensorPair_norm_tmul_completed_le
    (ξ : NormFamily S E) (η : NormFamily S F) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] E) (y : (S.ϕ ω).Completion ⊗[K] F) :
    (ξ.mixedTensorPair η).norm ω
      ((TensorProduct.AlgebraTensorModule.distribBaseChange K (S.ϕ ω).Completion E F).symm
        (x ⊗ₜ[(S.ϕ ω).Completion] y)) ≤ ξ.norm ω x * η.norm ω y :=
  (mixedTensorPair_norm_le_projectiveTensorPair_norm ξ η ω _).trans
    (projectiveTensorPair_norm_tmul_completed_le ξ η ω x y)

/-- Hadamard's bound through the canonical completed tensor determinant map.
All tuples, including singular and empty ones, are retained. -/
theorem projectiveTensorPair_determinant_norm_wedge_le
    (ξ : NormFamily S E) (η : NormFamily S F) (ω : S.Ω)
    (x : Fin (Module.finrank K E) → (S.ϕ ω).Completion ⊗[K] E)
    (y : Fin (Module.finrank K F) → (S.ϕ ω).Completion ⊗[K] F) :
    (ξ.projectiveTensorPair η).determinant.norm ω
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion (E ⊗[K] F)
        (Module.finrank K (E ⊗[K] F))).symm
        (determinantTensorEquivCompleted K (S.ϕ ω).Completion E F
          ((⨂ₜ[(S.ϕ ω).Completion] (_ : Fin (Module.finrank K F)),
            exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K E) x) ⊗ₜ[(S.ϕ ω).Completion]
            (⨂ₜ[(S.ϕ ω).Completion] (_ : Fin (Module.finrank K E)),
              exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K F) y)))) ≤
      (∏ i, ξ.norm ω (x i)) ^ Module.finrank K F *
        (∏ j, η.norm ω (y j)) ^ Module.finrank K E := by
  let e : (Fin (Module.finrank K E) × Fin (Module.finrank K F)) ≃
      Fin (Module.finrank K (E ⊗[K] F)) :=
    finProdFinEquiv.trans (finCongr (finrank_mul_eq_tensor K E F))
  rw [determinantTensorEquivCompleted_ιMulti]
  have hdet := (ξ.projectiveTensorPair η).determinant_norm_ιMulti_le ω
    (fun i ↦ (TensorProduct.AlgebraTensorModule.distribBaseChange K (S.ϕ ω).Completion E F).symm
      (x (e.symm i).1 ⊗ₜ[(S.ϕ ω).Completion] y (e.symm i).2))
  apply hdet.trans
  calc
    _ ≤ ∏ i : Fin (Module.finrank K (E ⊗[K] F)),
        ξ.norm ω (x (e.symm i).1) * η.norm ω (y (e.symm i).2) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact (ξ.projectiveTensorPair η).norm_nonneg ω _
      · intro i hi
        exact projectiveTensorPair_norm_tmul_completed_le ξ η ω _ _
    _ = ∏ ij : Fin (Module.finrank K E) × Fin (Module.finrank K F),
        ξ.norm ω (x ij.1) * η.norm ω (y ij.2) :=
      e.symm.prod_comp (fun ij ↦ ξ.norm ω (x ij.1) * η.norm ω (y ij.2))
    _ = _ := by
      simp only [Fintype.prod_prod_type, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.prod_pow]

end NormFamily

end

end ArakelovGeometry
