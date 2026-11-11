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

section BinaryEvaluation

variable {L : Type*} [Field L] {X : Unit ⊕ Unit → Type*}
  [∀ i, AddCommGroup (X i)] [∀ i, Module L (X i)]

/-- Finite and binary canonical dual evaluations agree on all dual tensors. -/
theorem piDualDistrib_binary_tprod (z : ⨂[L] i, Module.Dual L (X i)) (x : ∀ i, X i) :
    PiTensorProduct.dualDistrib z (⨂ₜ[L] i, x i) =
      dualTensorHom L (X (.inl ())) (Module.Dual L (X (.inr ())))
        (binaryTensorEquiv L (fun i ↦ Module.Dual L (X i)) z) (x (.inl ())) (x (.inr ())) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod a f =>
    simp only [map_smul, LinearMap.smul_apply, PiTensorProduct.dualDistrib_apply,
      binaryTensorEquiv_tprod, dualTensorHom_apply, Fintype.prod_sum_type, Fintype.prod_unique,
      smul_eq_mul]
  | add z t hz ht => simp only [map_add, LinearMap.add_apply, hz, ht]

end BinaryEvaluation

namespace NormFamily

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E F : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- Canonical binary dual distribution is isometric on all completed vectors. -/
theorem orthogonalTensorPair_dual_norm
    (ξ : NormFamily S E) (η : NormFamily S F)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ξ.IsHermitian hN) (hη : η.IsHermitian hN) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (Module.Dual K E ⊗[K] Module.Dual K F)) :
    (ξ.orthogonalTensorPair η hN hξ hη).dual.norm ω
      ((TensorProduct.dualDistrib K E F).baseChange (S.ϕ ω).Completion z) =
    (ξ.dual.orthogonalTensorPair η.dual hN hξ.dual hη.dual).norm ω z := by
  by_cases hω : ω ∈ S.Ωinf
  · let L := (S.ϕ ω).Completion
    let := hN ω hω
    let := IsRCLikeNormedField.rclike L
    let X i := L ⊗[K] BinaryTensorFactors E F i
    let D i := L ⊗[K] BinaryTensorFactors (Module.Dual K E) (Module.Dual K F) i
    let : ∀ i, NormedAddCommGroup (X i) :=
      fun i ↦ (tensorPairFactors ξ η i).fibreNormedAddCommGroup ω
    let : ∀ i, NormedSpace L (X i) := fun i ↦ (tensorPairFactors ξ η i).fibreNormedSpace ω
    let : ∀ i, InnerProductSpace L (X i) :=
      fun i ↦ (hξ.tensorPairFactors hη i).fibreInnerProductSpace ω hω
    let : ∀ i, NormedAddCommGroup (D i) :=
      fun i ↦ (tensorPairFactors ξ.dual η.dual i).fibreNormedAddCommGroup ω
    let : ∀ i, NormedSpace L (D i) :=
      fun i ↦ (tensorPairFactors ξ.dual η.dual i).fibreNormedSpace ω
    let : ∀ i, InnerProductSpace L (D i) :=
      fun i ↦ (hξ.dual.tensorPairFactors hη.dual i).fibreInnerProductSpace ω hω
    let b := fun i ↦ stdOrthonormalBasis L (X i)
    let c := fun i ↦ stdOrthonormalBasis L (D i)
    let e : ∀ i, D i ≃ₗ[L] Module.Dual L (X i) := fun i ↦ match i with
      | .inl _ => dualBaseChangeEquiv K L E
      | .inr _ => dualBaseChangeEquiv K L F
    have he : ∀ i x, ‖x‖ = linearMapOperatorSeminorm (e i x) := by
      rintro (i | i) x <;> rfl
    let B := binaryTensorEquiv K (BinaryTensorFactors E F)
    let BD := binaryTensorEquiv K (BinaryTensorFactors (Module.Dual K E) (Module.Dual K F))
    let A := TensorProduct.AlgebraTensorModule.distribBaseChange K L E F
    let P := binaryTensorEquiv L X
    let T := (B.baseChange K L _ _).symm.trans (tensorBaseChangeEquiv K L (BinaryTensorFactors E F))
    let t := tensorBaseChangeEquiv K L (BinaryTensorFactors (Module.Dual K E) (Module.Dual K F))
      (BD.symm.toLinearMap.baseChange L z)
    let q := PiTensorProduct.congr e t
    let f := dualBaseChangeEquiv K L (E ⊗[K] F) ((TensorProduct.dualDistrib K E F).baseChange L z)
    have hp : binaryTensorEquiv L D t =
        TensorProduct.AlgebraTensorModule.distribBaseChange K L
          (Module.Dual K E) (Module.Dual K F) z := by
      have h := DFunLike.congr_fun
        (tensorBaseChangeEquiv_binary K L (Module.Dual K E) (Module.Dual K F))
        (BD.symm.toLinearMap.baseChange L z)
      change binaryTensorEquiv L D t =
        TensorProduct.AlgebraTensorModule.distribBaseChange K L
          (Module.Dual K E) (Module.Dual K F)
          ((BD.baseChange K L _ _) ((BD.baseChange K L _ _).symm z)) at h
      simpa only [LinearEquiv.apply_symm_apply] using h
    have hp' (x : L ⊗[K] (E ⊗[K] F)) : P (T x) = A x := by
      have h := DFunLike.congr_fun (tensorBaseChangeEquiv_binary K L E F)
        ((B.baseChange K L _ _).symm x)
      change P (T x) = A ((B.baseChange K L _ _) ((B.baseChange K L _ _).symm x)) at h
      simpa only [LinearEquiv.apply_symm_apply] using h
    have hev (s : ⨂[L] i, X i) : PiTensorProduct.dualDistrib q s = f (A.symm (P s)) := by
      induction s using PiTensorProduct.induction_on with
      | smul_tprod a x =>
        simp only [map_smul, piDualDistrib_binary_tprod, P, binaryTensorEquiv_tprod]
        congr 1
        change dualTensorHom L _ _ (binaryTensorEquiv L _ (PiTensorProduct.congr e t)) _ _ = _
        rw [binaryTensorEquiv_congr, hp]
        exact (dualDistrib_baseChange_bilinear_apply K L E F z (x (.inl ())) (x (.inr ()))).symm
      | add s t hs ht => simp only [map_add, hs, ht]
    rw [dual_norm_eq_sSup]
    change _ = (orthogonalTensor (tensorPairFactors ξ.dual η.dual) hN
      (hξ.dual.tensorPairFactors hη.dual)).norm ω _
    rw [orthogonalTensor_norm_of_infinite _ _ _ ω hω]
    change _ = ArakelovGeometry.orthogonalTensorSeminorm c t
    rw [ArakelovGeometry.orthogonalTensor_dual_eq_sSup b c e he]
    congr 1
    rw [← T.surjective.range_comp]
    congr 1
    funext x
    change ‖f x‖ / (ξ.orthogonalTensorPair η hN hξ hη).norm ω x =
      ‖PiTensorProduct.dualDistrib q (T x)‖ / ArakelovGeometry.orthogonalTensorSeminorm b (T x)
    rw [hev, hp', LinearEquiv.symm_apply_apply]
    congr 1
    exact orthogonalTensor_norm_of_infinite _ _ _ ω hω _
  · have hfin : ω ∈ S.Ωfin := not_not.mp hω
    rw [orthogonalTensorPair_norm_of_finite _ _ _ _ _ ω hfin]
    rw [← mixedTensorPair_dual_norm_eq_injective]
    simp only [dual_norm_eq_sSup, orthogonalTensorPair_norm_of_finite _ _ _ _ _ ω hfin,
      mixedTensorPair_norm_of_mem_Ωfin _ _ ω hfin]

/-- Equality of norm families under the canonical algebraic dual isomorphism. -/
theorem orthogonalTensorPair_dual_pullback
    (ξ : NormFamily S E) (η : NormFamily S F)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ξ.IsHermitian hN) (hη : η.IsHermitian hN) :
    (ξ.orthogonalTensorPair η hN hξ hη).dual.pullback (TensorProduct.dualDistrib K E F)
      (by
        simpa only [← TensorProduct.toLinearMap_dualDistribEquiv, LinearEquiv.coe_coe] using
          (TensorProduct.dualDistribEquiv K E F).injective) =
      ξ.dual.orthogonalTensorPair η.dual hN hξ.dual hη.dual := by
  ext ω z
  exact orthogonalTensorPair_dual_norm ξ η hN hξ hη ω z

/-- The canonical binary tensor-dual isometry on the actual completed fibres. -/
def orthogonalTensorPairDualIsometry
    (ξ : NormFamily S E) (η : NormFamily S F)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ξ.IsHermitian hN) (hη : η.IsHermitian hN) (ω : S.Ω) :
    letI := (ξ.dual.orthogonalTensorPair η.dual hN hξ.dual hη.dual).fibreNormedAddCommGroup ω
    letI := (ξ.orthogonalTensorPair η hN hξ hη).dual.fibreNormedAddCommGroup ω
    ((S.ϕ ω).Completion ⊗[K] (Module.Dual K E ⊗[K] Module.Dual K F)) ≃ₗᵢ[(S.ϕ ω).Completion]
      ((S.ϕ ω).Completion ⊗[K] Module.Dual K (E ⊗[K] F)) := by
  letI := (ξ.dual.orthogonalTensorPair η.dual hN hξ.dual hη.dual).fibreNormedAddCommGroup ω
  letI := (ξ.orthogonalTensorPair η hN hξ hη).dual.fibreNormedAddCommGroup ω
  exact { (TensorProduct.dualDistribEquiv K E F).baseChange K (S.ϕ ω).Completion _ _ with
    norm_map' := fun z ↦ by
      change (ξ.orthogonalTensorPair η hN hξ hη).dual.norm ω
        ((TensorProduct.dualDistribEquiv K E F).toLinearMap.baseChange (S.ϕ ω).Completion z) =
        (ξ.dual.orthogonalTensorPair η.dual hN hξ.dual hη.dual).norm ω z
      rw [TensorProduct.toLinearMap_dualDistribEquiv]
      exact orthogonalTensorPair_dual_norm ξ η hN hξ hη ω z }

end NormFamily

end ArakelovGeometry
