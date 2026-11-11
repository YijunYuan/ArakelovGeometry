/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Tensor.Hermitian
public import ArakelovGeometry.Analysis.Tensor.HermitianDual
public import ArakelovGeometry.AdelicVectorBundle.Tensor.DualNorm
import ArakelovGeometry.Analysis.ScalarExtension.Hermitian.Tensor
import Mathlib.Analysis.Normed.Group.Ultra

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

omit [∀ i, FiniteDimensional K (E i)] in
/-- Canonical finite reindexing commutes with the actual tensor base-change map. -/
theorem tensorBaseChangeEquiv_reindex {J : Type*} [Finite J] (e : ι ≃ J)
    (z : L ⊗[K] (⨂[K] i, E i)) :
    tensorBaseChangeEquiv K L (fun j ↦ E (e.symm j))
      ((PiTensorProduct.reindex K E e).toLinearMap.baseChange L z) =
    PiTensorProduct.reindex L (fun i ↦ L ⊗[K] E i) e (tensorBaseChangeEquiv K L E z) := by
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simp only [map_add, hz, ht]
  | tmul a t =>
    induction t using PiTensorProduct.induction_on with
    | add t u ht hu => simp only [TensorProduct.tmul_add, map_add, ht, hu]
    | smul_tprod c x =>
      simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul', LinearMap.baseChange_tmul,
        LinearEquiv.coe_coe, PiTensorProduct.reindex_tprod, tensorBaseChangeEquiv_tmul_tprod,
        map_smul]

end Algebra

section GroupingBaseChange

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  {I J : Type*} [Finite I] [Finite J] (V : I ⊕ J → Type*)
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- Joining two finite groups commutes with canonical scalar extension. -/
theorem tensorBaseChangeEquiv_tmulEquivDep
    (z : L ⊗[K] ((⨂[K] i, V (.inl i)) ⊗[K] (⨂[K] j, V (.inr j)))) :
    tensorBaseChangeEquiv K L V
      ((PiTensorProduct.tmulEquivDep K V).toLinearMap.baseChange L z) =
    PiTensorProduct.tmulEquivDep L (fun i ↦ L ⊗[K] V i)
      (TensorProduct.congr (tensorBaseChangeEquiv K L (fun i ↦ V (.inl i)))
        (tensorBaseChangeEquiv K L (fun j ↦ V (.inr j)))
        (TensorProduct.AlgebraTensorModule.distribBaseChange K L
          (⨂[K] i, V (.inl i)) (⨂[K] j, V (.inr j)) z)) := by
  let f := (tensorBaseChangeEquiv K L V).toLinearMap ∘ₗ
    (PiTensorProduct.tmulEquivDep K V).toLinearMap.baseChange L
  let g := (PiTensorProduct.tmulEquivDep L (fun i ↦ L ⊗[K] V i)).toLinearMap ∘ₗ
    (TensorProduct.congr (tensorBaseChangeEquiv K L (fun i ↦ V (.inl i)))
      (tensorBaseChangeEquiv K L (fun j ↦ V (.inr j)))).toLinearMap ∘ₗ
    (TensorProduct.AlgebraTensorModule.distribBaseChange K L
      (⨂[K] i, V (.inl i)) (⨂[K] j, V (.inr j))).toLinearMap
  have h : f = g := by
    apply LinearMap.restrictScalars_injective K
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply TensorProduct.ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro y
    change tensorBaseChangeEquiv K L V
      ((PiTensorProduct.tmulEquivDep K V).toLinearMap.baseChange L
        (a ⊗ₜ[K] ((⨂ₜ[K] i, x i) ⊗ₜ[K] (⨂ₜ[K] j, y j)))) =
      PiTensorProduct.tmulEquivDep L (fun i ↦ L ⊗[K] V i)
        (TensorProduct.congr (tensorBaseChangeEquiv K L (fun i ↦ V (.inl i)))
          (tensorBaseChangeEquiv K L (fun j ↦ V (.inr j)))
          (TensorProduct.AlgebraTensorModule.distribBaseChange K L
            (⨂[K] i, V (.inl i)) (⨂[K] j, V (.inr j))
            (a ⊗ₜ[K] ((⨂ₜ[K] i, x i) ⊗ₜ[K] (⨂ₜ[K] j, y j)))))
    simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
      PiTensorProduct.tmulEquivDep_apply, tensorBaseChangeEquiv_tmul_tprod,
      TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
      TensorProduct.congr_tmul, TensorProduct.smul_tmul, one_smul]
    rw [TensorProduct.tmul_smul, map_smul, PiTensorProduct.tmulEquivDep_apply]
    congr 2
    funext i
    cases i <;> rfl
  exact LinearMap.congr_fun h z

end GroupingBaseChange

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

/-- Finite tensor duality acts on arbitrary vectors of every completed fibre. -/
theorem orthogonalTensor_dual_norm
    (ξ : ∀ i, NormFamily S (E i))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ∀ i, (ξ i).IsHermitian hN) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, Module.Dual K (E i))) :
    (orthogonalTensor ξ hN hξ).dual.norm ω
      (PiTensorProduct.dualDistrib.baseChange (S.ϕ ω).Completion z) =
    (orthogonalTensor (fun i ↦ (ξ i).dual) hN (fun i ↦ (hξ i).dual)).norm ω z := by
  by_cases hω : ω ∈ S.Ωinf
  · exact orthogonalTensor_dual_norm_of_infinite ξ hN hξ ω hω z
  have hfin : ω ∈ S.Ωfin := not_not.mp hω
  let L := (S.ϕ ω).Completion
  let X i := L ⊗[K] E i
  let D i := L ⊗[K] Module.Dual K (E i)
  let : ∀ i, NormedAddCommGroup (X i) := fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (X i) := fun i ↦ (ξ i).fibreNormedSpace ω
  let : ∀ i, IsUltrametricDist (X i) := fun i ↦
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm ((hξ i).1 ω hfin)
  let : ∀ i, NormedAddCommGroup (D i) := fun i ↦ (ξ i).dual.fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (D i) := fun i ↦ (ξ i).dual.fibreNormedSpace ω
  let : ∀ i, NormedAddCommGroup (Module.Dual L (X i)) :=
    fun i ↦ linearDualNormedAddCommGroup (k := L) (E := X i)
  let : ∀ i, NormedSpace L (Module.Dual L (X i)) :=
    fun i ↦ linearDualNormedSpace (k := L) (E := X i)
  let e : ∀ i, D i ≃ₗᵢ[L] Module.Dual L (X i) := fun i ↦
    { toLinearEquiv := dualBaseChangeEquiv K L (E i), norm_map' := fun _ ↦ rfl }
  let t := tensorBaseChangeEquiv K L (fun i ↦ Module.Dual K (E i)) z
  have hL (a b : L) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
    refine UniformSpace.Completion.induction_on₂ a b ?_ ?_
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · intro x y
      change ‖(↑x : (S.ϕ ω).Completion) + ↑y‖ ≤
        max ‖(↑x : (S.ϕ ω).Completion)‖ ‖(↑y : (S.ϕ ω).Completion)‖
      rw [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe,
        UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
      exact hfin x.ofAbs y.ofAbs
  rw [dual_norm_eq_sSup, orthogonalTensor_norm_of_finite _ _ _ ω hfin]
  change _ = ArakelovGeometry.injectiveTensorSeminorm t
  rw [← injectiveTensorSeminorm_congr_linearIsometryEquiv e t,
    injectiveTensor_dual_eq_sSup_of_ultrametric hL]
  congr 1
  rw [← (tensorBaseChangeEquiv K L E).surjective.range_comp]
  congr 1
  funext x
  rw [piDualDistrib_baseChange_apply, orthogonalTensor_norm_of_finite _ _ _ ω hfin]
  rfl

/-- Canonical finite tensor-dual isometry on the prescribed completed fibres. -/
def orthogonalTensorDualIsometry
    (ξ : ∀ i, NormFamily S (E i))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ∀ i, (ξ i).IsHermitian hN) (ω : S.Ω) :
    letI := (orthogonalTensor (fun i ↦ (ξ i).dual) hN
      (fun i ↦ (hξ i).dual)).fibreNormedAddCommGroup ω
    letI := (orthogonalTensor ξ hN hξ).dual.fibreNormedAddCommGroup ω
    ((S.ϕ ω).Completion ⊗[K] (⨂[K] i, Module.Dual K (E i))) ≃ₗᵢ[(S.ϕ ω).Completion]
      ((S.ϕ ω).Completion ⊗[K] Module.Dual K (⨂[K] i, E i)) := by
  letI := (orthogonalTensor (fun i ↦ (ξ i).dual) hN
    (fun i ↦ (hξ i).dual)).fibreNormedAddCommGroup ω
  letI := (orthogonalTensor ξ hN hξ).dual.fibreNormedAddCommGroup ω
  exact { (PiTensorProduct.dualDistribEquiv (R := K) (M := E)).baseChange K
      (S.ϕ ω).Completion _ _ with
    norm_map' := orthogonalTensor_dual_norm ξ hN hξ ω }

/-- Every canonical finite permutation preserves the actual norm at every place. -/
theorem orthogonalTensor_norm_reindex {J : Type*} [Fintype J]
    (ξ : ∀ i, NormFamily S (E i))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ∀ i, (ξ i).IsHermitian hN) (e : ι ≃ J) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (orthogonalTensor (fun j ↦ ξ (e.symm j)) hN (fun j ↦ hξ (e.symm j))).norm ω
      ((PiTensorProduct.reindex K E e).toLinearMap.baseChange (S.ϕ ω).Completion z) =
      (orthogonalTensor ξ hN hξ).norm ω z := by
  let L := (S.ϕ ω).Completion
  let : ∀ i, NormedAddCommGroup (L ⊗[K] E i) := fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (L ⊗[K] E i) := fun i ↦ (ξ i).fibreNormedSpace ω
  by_cases hω : ω ∈ S.Ωinf
  · let := hN ω hω
    let := IsRCLikeNormedField.rclike L
    let : ∀ i, InnerProductSpace L (L ⊗[K] E i) :=
      fun i ↦ (hξ i).fibreInnerProductSpace ω hω
    rw [orthogonalTensor_norm_of_infinite _ _ _ ω hω,
      orthogonalTensor_norm_of_infinite _ _ _ ω hω]
    change ArakelovGeometry.orthogonalTensorSeminorm
      (fun j ↦ stdOrthonormalBasis L (L ⊗[K] E (e.symm j)))
      (tensorBaseChangeEquiv K L (fun j ↦ E (e.symm j)) _) =
      ArakelovGeometry.orthogonalTensorSeminorm (fun i ↦ stdOrthonormalBasis L (L ⊗[K] E i))
        (tensorBaseChangeEquiv K L E z)
    rw [tensorBaseChangeEquiv_reindex]
    exact ArakelovGeometry.orthogonalTensorSeminorm_reindex
      (fun i ↦ stdOrthonormalBasis L (L ⊗[K] E i)) e (tensorBaseChangeEquiv K L E z)
  · have hfin : ω ∈ S.Ωfin := not_not.mp hω
    rw [orthogonalTensor_norm_of_finite _ _ _ ω hfin,
      orthogonalTensor_norm_of_finite _ _ _ ω hfin]
    change ArakelovGeometry.injectiveTensorSeminorm
      (tensorBaseChangeEquiv K L (fun j ↦ E (e.symm j)) _) =
      ArakelovGeometry.injectiveTensorSeminorm (tensorBaseChangeEquiv K L E z)
    rw [tensorBaseChangeEquiv_reindex]
    exact ArakelovGeometry.injectiveTensorSeminorm_reindex
      (V := fun i ↦ L ⊗[K] E i) e (tensorBaseChangeEquiv K L E z)

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

/-- At an infinite place the actual binary norm is Mathlib's Hilbert tensor
norm after the canonical completed base-change map. -/
theorem orthogonalTensorPair_norm_eq_hilbert
    (ξ : NormFamily S E) (η : NormFamily S F)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ξ.IsHermitian hN) (hη : η.IsHermitian hN) (ω : S.Ω) (hω : ω ∈ S.Ωinf)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⊗[K] F)) :
    let := hN ω hω
    let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    let := ξ.fibreNormedAddCommGroup ω
    let := ξ.fibreNormedSpace ω
    let := hξ.fibreInnerProductSpace ω hω
    let := η.fibreNormedAddCommGroup ω
    let := η.fibreNormedSpace ω
    let := hη.fibreInnerProductSpace ω hω
    (ξ.orthogonalTensorPair η hN hξ hη).norm ω z =
      ‖TensorProduct.AlgebraTensorModule.distribBaseChange K (S.ϕ ω).Completion E F z‖ := by
  let L := (S.ϕ ω).Completion
  let := hN ω hω
  let := IsRCLikeNormedField.rclike L
  let X i := L ⊗[K] BinaryTensorFactors E F i
  let : ∀ i, NormedAddCommGroup (X i) := fun i ↦ (tensorPairFactors ξ η i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (X i) := fun i ↦ (tensorPairFactors ξ η i).fibreNormedSpace ω
  let : ∀ i, InnerProductSpace L (X i) := fun i ↦
    (hξ.tensorPairFactors hη i).fibreInnerProductSpace ω hω
  let B := binaryTensorEquiv K (BinaryTensorFactors E F)
  change (orthogonalTensor (tensorPairFactors ξ η) hN (hξ.tensorPairFactors hη)).norm ω _ = _
  rw [orthogonalTensor_norm_of_infinite _ _ _ ω hω]
  change ArakelovGeometry.orthogonalTensorSeminorm
    (fun i ↦ stdOrthonormalBasis L (X i))
    (tensorBaseChangeEquiv K L (BinaryTensorFactors E F) (B.symm.toLinearMap.baseChange L z)) = _
  rw [orthogonalTensorSeminorm_binary]
  have he := DFunLike.congr_fun (tensorBaseChangeEquiv_binary K L E F)
    (B.symm.toLinearMap.baseChange L z)
  change binaryTensorEquiv L X
    (tensorBaseChangeEquiv K L (BinaryTensorFactors E F) (B.symm.toLinearMap.baseChange L z)) =
    TensorProduct.AlgebraTensorModule.distribBaseChange K L E F
      ((B.baseChange K L _ _) ((B.baseChange K L _ _).symm z)) at he
  congr 1
  simpa only [LinearEquiv.apply_symm_apply] using he

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

namespace NormFamily

section Grouping

universe u v w wι

attribute [-instance] PiTensorProduct.instSeminormedAddCommGroup
  PiTensorProduct.instNormedSpace

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {I J : Type wι} [Fintype I] [Fintype J] {V : I ⊕ J → Type w}
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
  [∀ i, FiniteDimensional K (V i)]

/-- Joining two finite groups is isometric on arbitrary completed archimedean vectors. -/
theorem orthogonalTensor_norm_tmulEquivDep_of_infinite
    (ξ : ∀ i, NormFamily S (V i))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ∀ i, (ξ i).IsHermitian hN) (ω : S.Ω) (hω : ω ∈ S.Ωinf)
    (z : (S.ϕ ω).Completion ⊗[K]
      ((⨂[K] i, V (.inl i)) ⊗[K] (⨂[K] j, V (.inr j)))) :
    (orthogonalTensor ξ hN hξ).norm ω
      ((PiTensorProduct.tmulEquivDep K V).toLinearMap.baseChange (S.ϕ ω).Completion z) =
    ((orthogonalTensor (fun i ↦ ξ (.inl i)) hN (fun i ↦ hξ (.inl i))).orthogonalTensorPair
      (orthogonalTensor (fun j ↦ ξ (.inr j)) hN (fun j ↦ hξ (.inr j))) hN
      (orthogonalTensor_isHermitian _ _ _) (orthogonalTensor_isHermitian _ _ _)).norm ω z := by
  let L := (S.ϕ ω).Completion
  let := hN ω hω
  let := IsRCLikeNormedField.rclike L
  let X i := L ⊗[K] V i
  let : ∀ i, NormedAddCommGroup (X i) := fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (X i) := fun i ↦ (ξ i).fibreNormedSpace ω
  let : ∀ i, InnerProductSpace L (X i) := fun i ↦ (hξ i).fibreInnerProductSpace ω hω
  let b := fun i ↦ stdOrthonormalBasis L (X i)
  let ξl := orthogonalTensor (fun i ↦ ξ (.inl i)) hN (fun i ↦ hξ (.inl i))
  let ξr := orthogonalTensor (fun j ↦ ξ (.inr j)) hN (fun j ↦ hξ (.inr j))
  let hl := orthogonalTensor_isHermitian (fun i ↦ ξ (.inl i)) hN (fun i ↦ hξ (.inl i))
  let hr := orthogonalTensor_isHermitian (fun j ↦ ξ (.inr j)) hN (fun j ↦ hξ (.inr j))
  let := ξl.fibreNormedAddCommGroup ω
  let := ξl.fibreNormedSpace ω
  let := hl.fibreInnerProductSpace ω hω
  let := ξr.fibreNormedAddCommGroup ω
  let := ξr.fibreNormedSpace ω
  let := hr.fibreInnerProductSpace ω hω
  let := orthogonalTensorNormedAddCommGroup (fun i ↦ b (.inl i))
  let := orthogonalTensorNormedSpace (fun i ↦ b (.inl i))
  let := orthogonalTensorInnerProductSpace (fun i ↦ b (.inl i))
  let := orthogonalTensorNormedAddCommGroup (fun j ↦ b (.inr j))
  let := orthogonalTensorNormedSpace (fun j ↦ b (.inr j))
  let := orthogonalTensorInnerProductSpace (fun j ↦ b (.inr j))
  let el : (L ⊗[K] (⨂[K] i, V (.inl i))) ≃ₗᵢ[L] (⨂[L] i, X (.inl i)) :=
    { toLinearEquiv := tensorBaseChangeEquiv K L (fun i ↦ V (.inl i))
      norm_map' := fun x ↦ by
        change ArakelovGeometry.orthogonalTensorSeminorm (fun i ↦ b (.inl i))
          (tensorBaseChangeEquiv K L (fun i ↦ V (.inl i)) x) = ξl.norm ω x
        exact (orthogonalTensor_norm_of_infinite
          (fun i ↦ ξ (.inl i)) hN (fun i ↦ hξ (.inl i)) ω hω x).symm }
  let er : (L ⊗[K] (⨂[K] j, V (.inr j))) ≃ₗᵢ[L] (⨂[L] j, X (.inr j)) :=
    { toLinearEquiv := tensorBaseChangeEquiv K L (fun j ↦ V (.inr j))
      norm_map' := fun x ↦ by
        change ArakelovGeometry.orthogonalTensorSeminorm (fun j ↦ b (.inr j))
          (tensorBaseChangeEquiv K L (fun j ↦ V (.inr j)) x) = ξr.norm ω x
        exact (orthogonalTensor_norm_of_infinite
          (fun j ↦ ξ (.inr j)) hN (fun j ↦ hξ (.inr j)) ω hω x).symm }
  let A := TensorProduct.AlgebraTensorModule.distribBaseChange K L
    (⨂[K] i, V (.inl i)) (⨂[K] j, V (.inr j))
  rw [orthogonalTensor_norm_of_infinite _ _ _ ω hω,
    orthogonalTensorPair_norm_eq_hilbert _ _ _ _ _ ω hω]
  change ArakelovGeometry.orthogonalTensorSeminorm b
    (tensorBaseChangeEquiv K L V _) = ‖A z‖
  rw [tensorBaseChangeEquiv_tmulEquivDep]
  have hg := orthogonalTensorSeminorm_tmulEquivDep_symm b
    (PiTensorProduct.tmulEquivDep L X
      ((TensorProduct.congr el.toLinearEquiv er.toLinearEquiv) (A z)))
  rw [LinearEquiv.symm_apply_apply] at hg
  change ArakelovGeometry.orthogonalTensorSeminorm b
    (PiTensorProduct.tmulEquivDep L X
      ((TensorProduct.congr el.toLinearEquiv er.toLinearEquiv) (A z))) = ‖A z‖
  rw [← hg]
  exact (TensorProduct.congrIsometry el er).norm_map (A z)

end Grouping

end NormFamily

end ArakelovGeometry
