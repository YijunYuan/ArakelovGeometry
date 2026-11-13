/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Determinant.Tensor.BaseChange
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Pair
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

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

universe u v w w'

section Algebra

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  (E : Type w) (F : Type w') [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

/-- The completed finite tensor of lifted factors is the ordinary completed binary tensor. -/
def tensorPairFibreEquiv :
    (⨂[L] i, L ⊗[K] LiftedTensorFactors E F i) ≃ₗ[L]
      (L ⊗[K] E) ⊗[L] (L ⊗[K] F) :=
  (binaryTensorEquiv L (fun i ↦ L ⊗[K] LiftedTensorFactors E F i)).trans
    (TensorProduct.congr (ULift.moduleEquiv.baseChange K L _ _)
      (ULift.moduleEquiv.baseChange K L _ _))

@[simp]
theorem tensorPairFibreEquiv_tprod (x : ∀ i, L ⊗[K] LiftedTensorFactors E F i) :
    tensorPairFibreEquiv K L E F (⨂ₜ[L] i, x i) =
      (ULift.moduleEquiv.baseChange K L _ _) (x (.inl ())) ⊗ₜ[L]
        (ULift.moduleEquiv.baseChange K L _ _) (x (.inr ())) := by
  simp [tensorPairFibreEquiv]

/-- Finite and binary tensor base change commute with the canonical lifting equivalence. -/
theorem tensorBaseChangeEquiv_binary :
    (tensorPairFibreEquiv K L E F).toLinearMap ∘ₗ
      (tensorBaseChangeEquiv K L (LiftedTensorFactors E F)).toLinearMap =
    (TensorProduct.AlgebraTensorModule.distribBaseChange K L E F).toLinearMap ∘ₗ
      (tensorPairEquiv K E F).toLinearMap.baseChange L := by
  apply LinearMap.restrictScalars_injective K
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change tensorPairFibreEquiv K L E F
      (tensorBaseChangeEquiv K L (LiftedTensorFactors E F) (a ⊗ₜ[K] (⨂ₜ[K] i, x i))) =
    TensorProduct.AlgebraTensorModule.distribBaseChange K L E F
      ((tensorPairEquiv K E F).toLinearMap.baseChange L (a ⊗ₜ[K] (⨂ₜ[K] i, x i)))
  simp only [LinearEquiv.coe_coe,
    tensorBaseChangeEquiv_tmul_tprod, map_smul, tensorPairFibreEquiv_tprod,
    tensorPairEquiv_tprod, LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

/-- A pure tensor of completed vectors lifts to the corresponding finite pure tensor. -/
theorem tensorBaseChangeEquiv_binary_symm_tmul
    (x : L ⊗[K] E) (y : L ⊗[K] F) :
    tensorBaseChangeEquiv K L (LiftedTensorFactors E F)
      ((tensorPairEquiv K E F).symm.toLinearMap.baseChange L
        ((TensorProduct.AlgebraTensorModule.distribBaseChange K L E F).symm
          (x ⊗ₜ[L] y))) =
      (⨂ₜ[L] i, match i with
        | .inl _ => (ULift.moduleEquiv.baseChange K L _ _).symm x
        | .inr _ => (ULift.moduleEquiv.baseChange K L _ _).symm y) := by
  let A := TensorProduct.AlgebraTensorModule.distribBaseChange K L E F
  let B := (tensorPairEquiv K E F).baseChange K L _ _
  let P := tensorPairFibreEquiv K L E F
  have he := DFunLike.congr_fun (tensorBaseChangeEquiv_binary K L E F)
    (B.symm (A.symm (x ⊗ₜ[L] y)))
  apply P.injective
  change P (tensorBaseChangeEquiv K L (LiftedTensorFactors E F)
    (B.symm (A.symm (x ⊗ₜ[L] y)))) = _
  change P (tensorBaseChangeEquiv K L (LiftedTensorFactors E F)
    (B.symm (A.symm (x ⊗ₜ[L] y)))) = A (B (B.symm (A.symm (x ⊗ₜ[L] y)))) at he
  simpa only [LinearEquiv.apply_symm_apply, P, tensorPairFibreEquiv_tprod] using he

end Algebra

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} {F : Type w'} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace NormFamily

/-- The actual projective norm on the ordinary binary tensor product. -/
def projectiveTensorPair (ξ : NormFamily S E) (η : NormFamily S F) :
    NormFamily S (E ⊗[K] F) :=
  (projectiveTensor (tensorPairFactors ξ η)).pullback
    (tensorPairEquiv K E F).symm.toLinearMap
    (tensorPairEquiv K E F).symm.injective

/-- The actual mixed norm on the ordinary binary tensor product. -/
def mixedTensorPair (ξ : NormFamily S E) (η : NormFamily S F) :
    NormFamily S (E ⊗[K] F) :=
  (mixedTensor (tensorPairFactors ξ η)).pullback
    (tensorPairEquiv K E F).symm.toLinearMap
    (tensorPairEquiv K E F).symm.injective

/-- The completed projective binary tensor contracts pure tensors by the
product of the actual completed factor norms. -/
theorem projectiveTensorPair_norm_tmul_completed_le
    (ξ : NormFamily S E) (η : NormFamily S F) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] E) (y : (S.ϕ ω).Completion ⊗[K] F) :
    (ξ.projectiveTensorPair η).norm ω
      ((TensorProduct.AlgebraTensorModule.distribBaseChange K (S.ϕ ω).Completion E F).symm
        (x ⊗ₜ[(S.ϕ ω).Completion] y)) ≤ ξ.norm ω x * η.norm ω y := by
  let X : ∀ i, (S.ϕ ω).Completion ⊗[K] LiftedTensorFactors E F i :=
    fun i ↦ match i with
      | .inl _ => (ULift.moduleEquiv.baseChange K (S.ϕ ω).Completion _ _).symm x
      | .inr _ => (ULift.moduleEquiv.baseChange K (S.ϕ ω).Completion _ _).symm y
  have hz : (tensorPairEquiv K E F).symm.toLinearMap.baseChange
      (S.ϕ ω).Completion
      ((TensorProduct.AlgebraTensorModule.distribBaseChange K (S.ϕ ω).Completion E F).symm
        (x ⊗ₜ[(S.ϕ ω).Completion] y)) =
      (tensorBaseChangeEquiv K (S.ϕ ω).Completion (LiftedTensorFactors E F)).symm
        (⨂ₜ[(S.ϕ ω).Completion] i, X i) := by
    apply (tensorBaseChangeEquiv K (S.ϕ ω).Completion (LiftedTensorFactors E F)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact tensorBaseChangeEquiv_binary_symm_tmul K (S.ϕ ω).Completion E F x y
  change (projectiveTensor (tensorPairFactors ξ η)).norm ω _ ≤ _
  rw [hz]
  have hb := projectiveTensor_norm_tprod_le (tensorPairFactors ξ η) ω X
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, tensorPairFactors, X,
    pullback_norm] at hb
  change _ ≤ ξ.norm ω ((ULift.moduleEquiv.baseChange K (S.ϕ ω).Completion _ _)
      ((ULift.moduleEquiv.baseChange K (S.ϕ ω).Completion _ _).symm x)) *
    η.norm ω ((ULift.moduleEquiv.baseChange K (S.ϕ ω).Completion _ _)
      ((ULift.moduleEquiv.baseChange K (S.ϕ ω).Completion _ _).symm y)) at hb
  simpa only [LinearEquiv.apply_symm_apply] using hb

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
