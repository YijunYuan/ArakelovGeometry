/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Tensor.Hermitian.Dual.Basic

/-!
# Grouping orthogonal tensor norms

Canonical grouping and finite reindexing preserve the completed orthogonal
tensor norms at every place, including regrouping of arbitrary tensor powers.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

namespace NormFamily

section Grouping

universe u w wι

attribute [-instance] PiTensorProduct.instSeminormedAddCommGroup
  PiTensorProduct.instNormedSpace

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {I J : Type wι} [Fintype I] [Fintype J] {V : I ⊕ J → Type w}
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
  [∀ i, FiniteDimensional K (V i)]

/-- Joining two finite groups is isometric on arbitrary completed archimedean vectors. -/
theorem orthogonalTensor_norm_tmulEquivDep_of_infinite
    (ξ : ∀ i, NormFamily S (V i))
    [hN : S.IsArchimedeanNormalized]
    [hξ : ∀ i, (ξ i).IsHermitian] (ω : S.Ω) (hω : ω ∈ S.Ωinf)
    (z : (S.ϕ ω).Completion ⊗[K]
      ((⨂[K] i, V (.inl i)) ⊗[K] (⨂[K] j, V (.inr j)))) :
    (orthogonalTensor ξ).norm ω
      ((PiTensorProduct.tmulEquivDep K V).toLinearMap.baseChange (S.ϕ ω).Completion z) =
    ((orthogonalTensor (fun i ↦ ξ (.inl i)) (hξ := (fun i ↦ hξ (.inl i)))).orthogonalTensorPair
      (orthogonalTensor (fun j ↦ ξ (.inr j)) (hξ := (fun j ↦ hξ (.inr j))))).norm ω z := by
  let L := (S.ϕ ω).Completion
  let := hN ω hω
  let := IsRCLikeNormedField.rclike L
  let X i := L ⊗[K] V i
  let : ∀ i, NormedAddCommGroup (X i) := fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (X i) := fun i ↦ (ξ i).fibreNormedSpace ω
  let : ∀ i, InnerProductSpace L (X i) := fun i ↦ (ξ i).fiberInnerProductSpace ω hω
  let b := fun i ↦ stdOrthonormalBasis L (X i)
  let ξl := orthogonalTensor (fun i ↦ ξ (.inl i)) (hξ := (fun i ↦ hξ (.inl i)))
  let ξr := orthogonalTensor (fun j ↦ ξ (.inr j)) (hξ := (fun j ↦ hξ (.inr j)))
  let hl := orthogonalTensor_isHermitian (fun i ↦ ξ (.inl i)) (hξ := (fun i ↦ hξ (.inl i)))
  let hr := orthogonalTensor_isHermitian (fun j ↦ ξ (.inr j)) (hξ := (fun j ↦ hξ (.inr j)))
  let := ξl.fibreNormedAddCommGroup ω
  let := ξl.fibreNormedSpace ω
  let := ξl.fiberInnerProductSpace ω hω
  let := ξr.fibreNormedAddCommGroup ω
  let := ξr.fibreNormedSpace ω
  let := ξr.fiberInnerProductSpace ω hω
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
          (fun i ↦ ξ (.inl i)) (hξ := (fun i ↦ hξ (.inl i))) ω hω x).symm }
  let er : (L ⊗[K] (⨂[K] j, V (.inr j))) ≃ₗᵢ[L] (⨂[L] j, X (.inr j)) :=
    { toLinearEquiv := tensorBaseChangeEquiv K L (fun j ↦ V (.inr j))
      norm_map' := fun x ↦ by
        change ArakelovGeometry.orthogonalTensorSeminorm (fun j ↦ b (.inr j))
          (tensorBaseChangeEquiv K L (fun j ↦ V (.inr j)) x) = ξr.norm ω x
        exact (orthogonalTensor_norm_of_infinite
          (fun j ↦ ξ (.inr j)) (hξ := (fun j ↦ hξ (.inr j))) ω hω x).symm }
  let A := TensorProduct.AlgebraTensorModule.distribBaseChange K L
    (⨂[K] i, V (.inl i)) (⨂[K] j, V (.inr j))
  rw [orthogonalTensor_norm_of_infinite _ ω hω,
    orthogonalTensorPair_norm_eq_hilbert _ _ ω hω]
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

/-- Canonical joining is isometric on all completed vectors at every place. -/
theorem orthogonalTensor_norm_tmulEquivDep
    (ξ : ∀ i, NormFamily S (V i))
    [hN : S.IsArchimedeanNormalized]
    [hξ : ∀ i, (ξ i).IsHermitian] (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      ((⨂[K] i, V (.inl i)) ⊗[K] (⨂[K] j, V (.inr j)))) :
    (orthogonalTensor ξ).norm ω
      ((PiTensorProduct.tmulEquivDep K V).toLinearMap.baseChange (S.ϕ ω).Completion z) =
    ((orthogonalTensor (fun i ↦ ξ (.inl i)) (hξ := (fun i ↦ hξ (.inl i)))).orthogonalTensorPair
      (orthogonalTensor (fun j ↦ ξ (.inr j)) (hξ := (fun j ↦ hξ (.inr j))))).norm ω z := by
  by_cases hω : ω ∈ S.Ωinf
  · exact orthogonalTensor_norm_tmulEquivDep_of_infinite ξ ω hω z
  have hfin : ω ∈ S.Ωfin := not_not.mp hω
  let L := (S.ϕ ω).Completion
  let X i := L ⊗[K] V i
  let : ∀ i, NormedAddCommGroup (X i) := fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (X i) := fun i ↦ (ξ i).fibreNormedSpace ω
  let Pl := ⨂[K] i, V (.inl i)
  let Pr := ⨂[K] j, V (.inr j)
  let ξl := orthogonalTensor (fun i ↦ ξ (.inl i)) (hξ := (fun i ↦ hξ (.inl i)))
  let ξr := orthogonalTensor (fun j ↦ ξ (.inr j)) (hξ := (fun j ↦ hξ (.inr j)))
  let hl := orthogonalTensor_isHermitian (fun i ↦ ξ (.inl i)) (hξ := (fun i ↦ hξ (.inl i)))
  let hr := orthogonalTensor_isHermitian (fun j ↦ ξ (.inr j)) (hξ := (fun j ↦ hξ (.inr j)))
  let τ := ξl.orthogonalTensorPair ξr
  let σ := orthogonalTensor ξ
  let := τ.fibreNormedAddCommGroup ω
  let := τ.fibreNormedSpace ω
  let := σ.fibreNormedAddCommGroup ω
  let := σ.fibreNormedSpace ω
  let T := tensorBaseChangeEquiv K L V
  let Tl := tensorBaseChangeEquiv K L (fun i ↦ V (.inl i))
  let Tr := tensorBaseChangeEquiv K L (fun j ↦ V (.inr j))
  let G := (PiTensorProduct.tmulEquivDep K V).baseChange K L _ _
  let A := TensorProduct.AlgebraTensorModule.distribBaseChange K L Pl Pr
  let Q := G.trans T
  have hc (a : L ⊗[K] Pl) (b : L ⊗[K] Pr) :
      Q (A.symm (a ⊗ₜ[L] b)) = PiTensorProduct.tmulEquivDep L X (Tl a ⊗ₜ[L] Tr b) := by
    change tensorBaseChangeEquiv K L V
      ((PiTensorProduct.tmulEquivDep K V).toLinearMap.baseChange L
        (A.symm (a ⊗ₜ[L] b))) = _
    rw [tensorBaseChangeEquiv_tmulEquivDep]
    change PiTensorProduct.tmulEquivDep L X
      ((TensorProduct.congr Tl Tr) (A (A.symm (a ⊗ₜ[L] b)))) = _
    rw [LinearEquiv.apply_symm_apply, TensorProduct.congr_tmul]
  have hσ (t : L ⊗[K] (⨂[K] i, V i)) :
      σ.norm ω t = ArakelovGeometry.injectiveTensorSeminorm (T t) :=
    orthogonalTensor_norm_of_finite ξ ω hfin t
  have hl' (a : L ⊗[K] Pl) : ξl.norm ω a = ArakelovGeometry.injectiveTensorSeminorm (Tl a) :=
    orthogonalTensor_norm_of_finite _ ω hfin a
  have hr' (b : L ⊗[K] Pr) : ξr.norm ω b = ArakelovGeometry.injectiveTensorSeminorm (Tr b) :=
    orthogonalTensor_norm_of_finite _ ω hfin b
  change σ.norm ω (G z) = τ.norm ω z
  apply le_antisymm
  · let Y i := L ⊗[K] LiftedTensorFactors Pl Pr i
    let : ∀ i, NormedAddCommGroup (Y i) :=
      fun i ↦ (tensorPairFactors ξl ξr i).fibreNormedAddCommGroup ω
    let : ∀ i, NormedSpace L (Y i) :=
      fun i ↦ (tensorPairFactors ξl ξr i).fibreNormedSpace ω
    let B := tensorPairEquiv K Pl Pr
    let P := tensorPairFibreEquiv K L Pl Pr
    let q := tensorBaseChangeEquiv K L (LiftedTensorFactors Pl Pr)
      (B.symm.toLinearMap.baseChange L z)
    have hq : P q = A z := by
      have he := DFunLike.congr_fun (tensorBaseChangeEquiv_binary K L Pl Pr)
        (B.symm.toLinearMap.baseChange L z)
      change P q = A ((B.baseChange K L _ _) ((B.baseChange K L _ _).symm z)) at he
      simpa only [LinearEquiv.apply_symm_apply] using he
    let f := G.toLinearMap ∘ₗ A.symm.toLinearMap ∘ₗ P.toLinearMap
    have hp (x : ∀ i, Y i) : ‖f (⨂ₜ[L] i, x i)‖ ≤ ∏ i, ‖x i‖ := by
      change σ.norm ω (G (A.symm (P (⨂ₜ[L] i, x i)))) ≤ _
      rw [hσ, tensorPairFibreEquiv_tprod]
      change ArakelovGeometry.injectiveTensorSeminorm
        (Q (A.symm (((ULift.moduleEquiv.baseChange K L _ _) (x (.inl ()))) ⊗ₜ[L]
          ((ULift.moduleEquiv.baseChange K L _ _) (x (.inr ())))))) ≤ _
      rw [hc]
      have h := injectiveTensorSeminorm_tmulEquivDep_le (k := L) (V := X)
        (Tl ((ULift.moduleEquiv.baseChange K L _ _) (x (.inl ()))))
        (Tr ((ULift.moduleEquiv.baseChange K L _ _) (x (.inr ()))))
      rw [← hl', ← hr'] at h
      simp only [Fintype.prod_sum_type, Fintype.prod_unique]
      change ArakelovGeometry.injectiveTensorSeminorm _ ≤
        ξl.norm ω ((ULift.moduleEquiv.baseChange K L _ _) (x (.inl ()))) *
          ξr.norm ω ((ULift.moduleEquiv.baseChange K L _ _) (x (.inr ())))
      exact h
    have h := norm_linearMap_le_injective_of_ultrametric_factors f
      (orthogonalTensor_isUltrametricAtFinitePlaces ξ ω hfin) hp q
    change σ.norm ω (G (A.symm (P q))) ≤ ArakelovGeometry.injectiveTensorSeminorm q at h
    rw [hq, LinearEquiv.symm_apply_apply] at h
    change σ.norm ω (G z) ≤ (ξl.orthogonalTensorPair ξr).norm ω z
    rw [orthogonalTensorPair_norm_of_finite _ _ ω hfin]
    exact h
  · let f := Q.symm.toLinearMap
    have hp (x : ∀ i, X i) : ‖f (⨂ₜ[L] i, x i)‖ ≤ ∏ i, ‖x i‖ := by
      have he : f (⨂ₜ[L] i, x i) =
          A.symm (Tl.symm (⨂ₜ[L] i, x (.inl i)) ⊗ₜ[L] Tr.symm (⨂ₜ[L] j, x (.inr j))) := by
        apply Q.injective
        change Q (Q.symm _) = _
        rw [LinearEquiv.apply_symm_apply, hc, LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply, PiTensorProduct.tmulEquivDep_apply]
        congr 1
        funext s
        cases s <;> rfl
      rw [he]
      change τ.norm ω _ ≤ _
      rw [orthogonalTensorPair_norm_tmul_completed ξl ξr ω,
        orthogonalTensor_norm_tprod, orthogonalTensor_norm_tprod]
      simp only [Fintype.prod_sum_type]
      exact le_rfl
    have h := norm_linearMap_le_injective_of_ultrametric_factors f
      ((orthogonalTensorPair_isHermitian ξl ξr).1 ω hfin) hp (Q z)
    change τ.norm ω (Q.symm (Q z)) ≤ ArakelovGeometry.injectiveTensorSeminorm (Q z) at h
    rw [LinearEquiv.symm_apply_apply] at h
    rw [hσ]
    exact h

/-- Joining and then reindexing gives an isometry for any finite rearrangement. -/
theorem orthogonalTensor_norm_regroup {M : Type*} [Fintype M]
    (ξ : ∀ i, NormFamily S (V i))
    [hN : S.IsArchimedeanNormalized]
    [hξ : ∀ i, (ξ i).IsHermitian] (e : I ⊕ J ≃ M) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      ((⨂[K] i, V (.inl i)) ⊗[K] (⨂[K] j, V (.inr j)))) :
    (orthogonalTensor (fun m ↦ ξ (e.symm m)) (hξ := (fun m ↦ hξ (e.symm m)))).norm ω
      ((PiTensorProduct.reindex K V e).toLinearMap.baseChange (S.ϕ ω).Completion
        ((PiTensorProduct.tmulEquivDep K V).toLinearMap.baseChange (S.ϕ ω).Completion z)) =
    ((orthogonalTensor (fun i ↦ ξ (.inl i)) (hξ := (fun i ↦ hξ (.inl i)))).orthogonalTensorPair
      (orthogonalTensor (fun j ↦ ξ (.inr j)) (hξ := (fun j ↦ hξ (.inr j))))).norm ω z := by
  rw [orthogonalTensor_norm_reindex]
  exact orthogonalTensor_norm_tmulEquivDep ξ ω z

end Grouping

/-- Tensor powers regroup through the canonical sum-of-finite-sets equivalence. -/
theorem orthogonalTensorPower_norm_regroup
    {K : Type*} [Field K] {S : AdelicStructure K}
    {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] (m n : ℕ) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      ((⨂[K] _ : Fin m, E) ⊗[K] (⨂[K] _ : Fin n, E))) :
    (orthogonalTensor (fun _ : Fin (m + n) ↦ ξ) (hξ := (fun _ ↦ hξ))).norm ω
      ((PiTensorProduct.reindex K (fun _ : Fin m ⊕ Fin n ↦ E) finSumFinEquiv).toLinearMap.baseChange
        (S.ϕ ω).Completion
        ((PiTensorProduct.tmulEquivDep K (fun _ : Fin m ⊕ Fin n ↦ E)).toLinearMap.baseChange
          (S.ϕ ω).Completion z)) =
    ((orthogonalTensor (fun _ : Fin m ↦ ξ) (hξ := (fun _ ↦ hξ))).orthogonalTensorPair
      (orthogonalTensor (fun _ : Fin n ↦ ξ) (hξ := (fun _ ↦ hξ)))).norm ω z :=
  orthogonalTensor_norm_regroup (fun _ : Fin m ⊕ Fin n ↦ ξ) (hξ := (fun _ ↦ hξ))
    finSumFinEquiv ω z

end NormFamily

end ArakelovGeometry
