/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Tensor.Hermitian
public import ArakelovGeometry.Analysis.Tensor.HermitianDual
public import ArakelovGeometry.AdelicVectorBundle.Tensor.DualNorm

/-!
# Orthogonal tensor duality on completed fibres

Canonical finite tensor evaluation commutes with scalar extension. The local
orthogonal duality theorem therefore applies to arbitrary vectors in the actual
completed fibres, with the prescribed norms of the factors and their duals.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

section Algebra

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  {ι : Type*} [Finite ι] (E : ι → Type*)
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)]

/-- Finite tensor evaluation commutes with scalar extension on arbitrary vectors. -/
theorem piDualDistrib_baseChange_apply
    (z : L ⊗[K] (⨂[K] i, Module.Dual K (E i)))
    (x : L ⊗[K] (⨂[K] i, E i)) :
    dualBaseChangeEquiv K L (⨂[K] i, E i)
      (PiTensorProduct.dualDistrib.baseChange L z) x =
    PiTensorProduct.dualDistrib
      (PiTensorProduct.congr (fun i ↦ dualBaseChangeEquiv K L (E i))
        (tensorBaseChangeEquiv K L (fun i ↦ Module.Dual K (E i)) z))
      (tensorBaseChangeEquiv K L E x) := by
  let := Fintype.ofFinite ι
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simp only [map_add, LinearMap.add_apply, hz, ht]
  | tmul a f =>
    induction f using PiTensorProduct.induction_on with
    | add f g hf hg => simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, hf, hg]
    | smul_tprod c f =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul b t =>
        induction t using PiTensorProduct.induction_on with
        | add t u ht hu => simp only [TensorProduct.tmul_add, map_add, ht, hu]
        | smul_tprod d t =>
          simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul,
            LinearMap.baseChange_tmul, dualBaseChangeEquiv_tmul_apply_tmul,
            tensorBaseChangeEquiv_tmul_tprod, map_smul, PiTensorProduct.congr_tprod,
            LinearMap.smul_apply, PiTensorProduct.dualDistrib_apply, one_mul,
            map_prod, mul_one]
          ring

end Algebra

namespace NormFamily

universe u v w wι

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {ι : Type wι} [Fintype ι] {E : ι → Type w}
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)]

/-- Canonical evaluation preserves orthogonal norms on every completed tensor
at an archimedean place. -/
theorem orthogonalTensor_dual_norm_of_infinite
    (ξ : ∀ i, NormFamily S (E i))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ∀ i, (ξ i).IsHermitian hN) (ω : S.Ω) (hω : ω ∈ S.Ωinf)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, Module.Dual K (E i))) :
    (orthogonalTensor ξ hN hξ).dual.norm ω
      (PiTensorProduct.dualDistrib.baseChange (S.ϕ ω).Completion z) =
    (orthogonalTensor (fun i ↦ (ξ i).dual) hN (fun i ↦ (hξ i).dual)).norm ω z := by
  let L := (S.ϕ ω).Completion
  let := hN ω hω
  let := IsRCLikeNormedField.rclike L
  let X i := L ⊗[K] E i
  let D i := L ⊗[K] Module.Dual K (E i)
  let : ∀ i, NormedAddCommGroup (X i) := fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (X i) := fun i ↦ (ξ i).fibreNormedSpace ω
  let : ∀ i, InnerProductSpace L (X i) := fun i ↦ (hξ i).fibreInnerProductSpace ω hω
  let : ∀ i, NormedAddCommGroup (D i) := fun i ↦ (ξ i).dual.fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (D i) := fun i ↦ (ξ i).dual.fibreNormedSpace ω
  let : ∀ i, InnerProductSpace L (D i) := fun i ↦ (hξ i).dual.fibreInnerProductSpace ω hω
  let b := fun i ↦ stdOrthonormalBasis L (X i)
  let c := fun i ↦ stdOrthonormalBasis L (D i)
  let e := fun i ↦ dualBaseChangeEquiv K L (E i)
  let t := tensorBaseChangeEquiv K L (fun i ↦ Module.Dual K (E i)) z
  rw [dual_norm_eq_sSup, orthogonalTensor_norm_of_infinite _ _ _ ω hω]
  change _ = ArakelovGeometry.orthogonalTensorSeminorm c t
  rw [ArakelovGeometry.orthogonalTensor_dual_eq_sSup b c e (fun _ _ ↦ rfl)]
  congr 1
  rw [← (tensorBaseChangeEquiv K L E).surjective.range_comp]
  congr 1
  funext x
  rw [piDualDistrib_baseChange_apply, orthogonalTensor_norm_of_infinite _ _ _ ω hω]
  rfl

end NormFamily

end ArakelovGeometry
