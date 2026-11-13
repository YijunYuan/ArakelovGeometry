/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Exterior.BaseChange
public import ArakelovGeometry.AdelicVectorBundle.Subquotient.Quotient.Basic
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Exterior powers of norm families

The exterior-power family is the quotient of the mixed tensor-power family
under the canonical tensor-to-exterior map, on the actual completed fibres.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

attribute [local instance 50] UniformSpace.Completion.instModule

noncomputable section

variable {K : Type*} [Field K] {S : AdelicStructure K}
variable {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ξ : NormFamily S E)

/-- The exterior-power norm family is the quotient of the mixed tensor power. -/
def exteriorPower (n : ℕ) : NormFamily S (⋀[K]^n E) :=
  letI : FiniteDimensional K (⨂[K] (_ : Fin n), E) := by infer_instance
  (mixedTensor (fun _ : Fin n ↦ ξ)).pushforward
    (tensorToExterior K E n) (tensorToExterior_surjective K E n)

/-- The exterior norm is the infimum of the norms of all actual completed
tensor lifts. -/
theorem exteriorPower_norm_eq_sInf (n : ℕ) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^n E)) :
    (ξ.exteriorPower n).norm ω z = sInf
      ((mixedTensor (fun _ : Fin n ↦ ξ)).norm ω ''
        {x | (tensorToExterior K E n).baseChange (S.ϕ ω).Completion x = z}) :=
  (mixedTensor (fun _ : Fin n ↦ ξ)).pushforward_norm_eq_sInf
    (tensorToExterior K E n) (tensorToExterior_surjective K E n) ω z

/-- Canonical scalar extension identifies the completed quotient formula with
the local tensor-to-exterior quotient formula in the source. -/
theorem exteriorPower_norm_eq_sInf_local (n : ℕ) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^n E)) :
    (ξ.exteriorPower n).norm ω z = sInf
      (((mixedTensor (fun _ : Fin n ↦ ξ)).norm ω ∘
        (tensorBaseChangeEquiv K (S.ϕ ω).Completion (fun _ : Fin n ↦ E)).symm) ''
          {x | tensorToExterior (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E) n x =
            exteriorBaseChangeEquiv K (S.ϕ ω).Completion E n z}) := by
  rw [exteriorPower_norm_eq_sInf, Set.image_comp]
  congr 2
  change _ = (tensorBaseChangeEquiv K (S.ϕ ω).Completion (fun _ : Fin n ↦ E)).toEquiv.symm '' _
  rw [(tensorBaseChangeEquiv K (S.ϕ ω).Completion
    (fun _ : Fin n ↦ E)).toEquiv.image_symm_eq_preimage]
  ext x
  change (tensorToExterior K E n).baseChange (S.ϕ ω).Completion x = z ↔ _
  rw [Set.mem_preimage, Set.mem_ofPred_eq, LinearEquiv.coe_toEquiv,
    ← exteriorBaseChangeEquiv_tensorToExterior]
  exact (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E n).injective.eq_iff.symm

/-- Exterior-power quotient maps contract the actual completed tensor norm. -/
theorem exteriorPower_norm_le (n : ℕ) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] (⨂[K] (_ : Fin n), E)) :
    (ξ.exteriorPower n).norm ω ((tensorToExterior K E n).baseChange (S.ϕ ω).Completion x) ≤
      (mixedTensor (fun _ : Fin n ↦ ξ)).norm ω x :=
  (mixedTensor (fun _ : Fin n ↦ ξ)).pushforward_norm_le
    (tensorToExterior K E n) (tensorToExterior_surjective K E n) ω x

/-- Exterior-power norms are ultrametric at every non-Archimedean place. -/
theorem exteriorPower_isUltrametricAtFinitePlaces
    (n : ℕ) : (ξ.exteriorPower n).IsUltrametricAtFinitePlaces :=
  (mixedTensor_isUltrametricAtFinitePlaces (fun _ : Fin n ↦ ξ)).pushforward
    (tensorToExterior K E n) (tensorToExterior_surjective K E n)

/-- Every decomposable exterior tensor is bounded by the product of its
factor norms. -/
theorem exteriorPower_norm_ιMulti_le (n : ℕ) (ω : S.Ω)
    (x : Fin n → (S.ϕ ω).Completion ⊗[K] E) :
    (ξ.exteriorPower n).norm ω
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E n).symm
        (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion n x)) ≤
      ∏ i, ξ.norm ω (x i) := by
  have hx : (tensorToExterior K E n).baseChange (S.ϕ ω).Completion
      ((tensorBaseChangeEquiv K (S.ϕ ω).Completion (fun _ : Fin n ↦ E)).symm
        (⨂ₜ[(S.ϕ ω).Completion] i, x i)) =
        (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E n).symm
          (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion n x) := by
    apply (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E n).injective
    rw [exteriorBaseChangeEquiv_tensorToExterior, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, tensorToExterior_tprod]
  rw [← hx]
  refine (ξ.exteriorPower_norm_le n ω _).trans ?_
  have hπ := projectiveTensor_norm_tprod_le (fun _ : Fin n ↦ ξ) ω x
  by_cases hω : ω ∈ S.Ωfin
  · rw [mixedTensor_norm_of_mem_Ωfin _ ω hω]
    exact (injectiveTensor_norm_le_projectiveTensor_norm _ ω _).trans hπ
  · rw [mixedTensor_norm_of_not_mem_Ωfin _ ω hω]
    exact hπ

/-- Exterior powers above the dimension are the zero space and have zero norm. -/
theorem exteriorPower_norm_eq_zero_of_finrank_lt {n : ℕ} (hn : Module.finrank K E < n)
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^n E)) :
    (ξ.exteriorPower n).norm ω z = 0 := by
  let : Subsingleton (⋀[K]^n E) := (Module.finrank_eq_zero_iff_of_free K _).mp
    (by rw [_root_.exteriorPower.finrank_eq, Nat.choose_eq_zero_of_lt hn])
  exact (ξ.exteriorPower n).norm_eq_zero_of_subsingleton ω z

/-- On a zero vector space every positive exterior power has zero norm. -/
theorem exteriorPower_norm_eq_zero_of_subsingleton [Subsingleton E] {n : ℕ} (hn : 0 < n)
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^n E)) :
    (ξ.exteriorPower n).norm ω z = 0 := by
  apply ξ.exteriorPower_norm_eq_zero_of_finrank_lt
  simpa only [Module.finrank_zero_of_subsingleton] using hn

/-- The degree-zero exterior family is the absolute-value family under the
canonical identification of the completed exterior unit with the scalar field. -/
theorem exteriorPower_norm_zero (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^0 E)) :
    (ξ.exteriorPower 0).norm ω z =
      ‖_root_.exteriorPower.zeroEquiv (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E)
        (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E 0 z)‖ := by
  obtain ⟨x, rfl⟩ := LinearMap.baseChange_surjective (S.ϕ ω).Completion
    (tensorToExterior_surjective K E 0) z
  change ((mixedTensor (fun _ : Fin 0 ↦ ξ)).pushforward _ _).norm ω _ = _
  rw [pushforward_norm_of_injective _ _ _ (tensorToExterior_zero_bijective K E).1,
    mixedTensor_norm_isEmpty, exteriorBaseChangeEquiv_tensorToExterior,
    tensorToExterior_zero]
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

/-- On pure scalar tensors, the degree-zero norm is the usual scalar
absolute value. -/
theorem exteriorPower_zero_norm_tmul (ω : S.Ω) (a : (S.ϕ ω).Completion)
    (z : ⋀[K]^0 E) :
    (ξ.exteriorPower 0).norm ω (a ⊗ₜ[K] z) =
      ‖a * algebraMap K (S.ϕ ω).Completion (_root_.exteriorPower.zeroEquiv K E z)‖ := by
  rw [exteriorPower_norm_zero, exteriorBaseChangeEquiv_zero_tmul]

end

end ArakelovGeometry.NormFamily
