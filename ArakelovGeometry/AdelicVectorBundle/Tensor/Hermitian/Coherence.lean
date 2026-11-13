/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Tensor.Hermitian.Grouping

/-!
# Coherence of completed tensor norms and evaluation

The binary commutor and associator preserve completed norms. Finite and binary
dual evaluation commute with reindexing, grouping, associativity and scalar extension.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

section AssociatorBaseChange

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  (E F G : Type*) [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [AddCommGroup G] [Module K G]

/-- The ordinary associator commutes with iterated completed tensor base change. -/
theorem tensorBaseChangeEquiv_assoc (z : L ⊗[K] ((E ⊗[K] F) ⊗[K] G)) :
    TensorProduct.map (LinearMap.id : (L ⊗[K] E) →ₗ[L] (L ⊗[K] E))
      (TensorProduct.AlgebraTensorModule.distribBaseChange K L F G).toLinearMap
      (TensorProduct.AlgebraTensorModule.distribBaseChange K L E (F ⊗[K] G)
        ((TensorProduct.assoc K E F G).toLinearMap.baseChange L z)) =
    TensorProduct.assoc L (L ⊗[K] E) (L ⊗[K] F) (L ⊗[K] G)
      (TensorProduct.map (TensorProduct.AlgebraTensorModule.distribBaseChange K L E F).toLinearMap
        (LinearMap.id : (L ⊗[K] G) →ₗ[L] (L ⊗[K] G))
        (TensorProduct.AlgebraTensorModule.distribBaseChange K L (E ⊗[K] F) G z)) := by
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simp only [map_add, hz, ht]
  | tmul a z =>
    induction z using TensorProduct.inductionOn with
    | add z t hz ht => simp only [TensorProduct.tmul_add, map_add, hz, ht]
    | tmul z w =>
      induction z using TensorProduct.inductionOn with
      | add z t hz ht => simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hz, ht]
      | tmul x y =>
        simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, TensorProduct.assoc_tmul,
          TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.map_tmul,
          LinearMap.id_apply]

/-- Associating three completed pure factors uses the ordinary algebraic associator. -/
theorem tensorBaseChangeEquiv_assoc_symm_tmul
    (x : L ⊗[K] E) (y : L ⊗[K] F) (z : L ⊗[K] G) :
    (TensorProduct.assoc K E F G).toLinearMap.baseChange L
      ((TensorProduct.AlgebraTensorModule.distribBaseChange K L (E ⊗[K] F) G).symm
        ((TensorProduct.AlgebraTensorModule.distribBaseChange K L E F).symm (x ⊗ₜ[L] y) ⊗ₜ[L] z)) =
    (TensorProduct.AlgebraTensorModule.distribBaseChange K L E (F ⊗[K] G)).symm
      (x ⊗ₜ[L] (TensorProduct.AlgebraTensorModule.distribBaseChange K L F G).symm (y ⊗ₜ[L] z)) := by
  apply (TensorProduct.AlgebraTensorModule.distribBaseChange K L E (F ⊗[K] G)).injective
  apply (TensorProduct.congr (LinearEquiv.refl L (L ⊗[K] E))
    (TensorProduct.AlgebraTensorModule.distribBaseChange K L F G)).injective
  change TensorProduct.map LinearMap.id
    (TensorProduct.AlgebraTensorModule.distribBaseChange K L F G).toLinearMap _ = _
  rw [tensorBaseChangeEquiv_assoc]
  simp only [LinearEquiv.apply_symm_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe, TensorProduct.assoc_tmul, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply]

end AssociatorBaseChange

namespace NormFamily

section BinaryCoherence

universe u₁ w₁ wF wG

variable {K : Type u₁} [Field K] {S : AdelicStructure K}
  {E : Type w₁} {F : Type wF} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- At a finite place a pure-tensor bound into an ultrametric target extends
to every completed vector, with the same constant. -/
theorem norm_linearMap_le_orthogonalTensorPair_of_finite
    (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    {W : Type*} [SeminormedAddCommGroup W] [NormedSpace (S.ϕ ω).Completion W]
    (f : ((S.ϕ ω).Completion ⊗[K] (E ⊗[K] F)) →ₗ[(S.ϕ ω).Completion] W)
    (hW : ∀ x y : W, ‖x + y‖ ≤ max ‖x‖ ‖y‖) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x y, ‖f ((TensorProduct.AlgebraTensorModule.distribBaseChange K
      (S.ϕ ω).Completion E F).symm (x ⊗ₜ[(S.ϕ ω).Completion] y))‖ ≤
      C * (ξ.norm ω x * η.norm ω y))
    (z : (S.ϕ ω).Completion ⊗[K] (E ⊗[K] F)) :
    ‖f z‖ ≤ C * (ξ ⊗ʰ η).norm ω z := by
  let L := (S.ϕ ω).Completion
  let X i := L ⊗[K] LiftedTensorFactors E F i
  let : ∀ i, NormedAddCommGroup (X i) := fun i ↦ (tensorPairFactors ξ η i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (X i) := fun i ↦ (tensorPairFactors ξ η i).fibreNormedSpace ω
  let A := TensorProduct.AlgebraTensorModule.distribBaseChange K L E F
  let B := (tensorPairEquiv K E F).baseChange K L _ _
  let P := tensorPairFibreEquiv K L E F
  let t := tensorBaseChangeEquiv K L (LiftedTensorFactors E F) (B.symm z)
  have hp : P t = A z := by
    have he := DFunLike.congr_fun (tensorBaseChangeEquiv_binary K L E F) (B.symm z)
    change P t = A (B (B.symm z)) at he
    simpa only [LinearEquiv.apply_symm_apply] using he
  let g := f ∘ₗ A.symm.toLinearMap ∘ₗ P.toLinearMap
  have hg (x : ∀ i, X i) : ‖g (⨂ₜ[L] i, x i)‖ ≤ C * ∏ i, ‖x i‖ := by
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, P,
      tensorPairFibreEquiv_tprod, Fintype.prod_sum_type, Fintype.prod_unique]
    change ‖f (A.symm (((ULift.moduleEquiv.baseChange K L _ _) (x (.inl ()))) ⊗ₜ[L]
      ((ULift.moduleEquiv.baseChange K L _ _) (x (.inr ())))))‖ ≤
      C * (ξ.norm ω ((ULift.moduleEquiv.baseChange K L _ _) (x (.inl ()))) *
        η.norm ω ((ULift.moduleEquiv.baseChange K L _ _) (x (.inr ()))))
    exact hf _ _
  have h := norm_linearMap_le_mul_injective_of_ultrametric_factors g hW hC hg t
  change ‖f (A.symm (P t))‖ ≤ C * ArakelovGeometry.injectiveTensorSeminorm t at h
  rw [hp, LinearEquiv.symm_apply_apply] at h
  rw [orthogonalTensorPair_norm_of_finite _ _ ω hω]
  exact h

/-- Binary symmetry contracts the actual completed norm at a finite place. -/
theorem orthogonalTensorPair_comm_norm_le_of_finite
    (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⊗[K] F)) :
    (η ⊗ʰ ξ).norm ω
      ((TensorProduct.comm K E F).toLinearMap.baseChange (S.ϕ ω).Completion z) ≤
    (ξ ⊗ʰ η).norm ω z := by
  let L := (S.ϕ ω).Completion
  let τ := η.orthogonalTensorPair ξ
  let := τ.fibreNormedAddCommGroup ω
  let := τ.fibreNormedSpace ω
  have hτ := orthogonalTensorPair_isHermitian η ξ
  have hp (x : L ⊗[K] E) (y : L ⊗[K] F) :
      (TensorProduct.comm K E F).toLinearMap.baseChange L
        ((TensorProduct.AlgebraTensorModule.distribBaseChange K L E F).symm (x ⊗ₜ[L] y)) =
      (TensorProduct.AlgebraTensorModule.distribBaseChange K L F E).symm (y ⊗ₜ[L] x) := by
    apply (TensorProduct.AlgebraTensorModule.distribBaseChange K L F E).injective
    rw [tensorBaseChangeEquiv_comm, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, TensorProduct.comm_tmul]
  have h := norm_linearMap_le_orthogonalTensorPair_of_finite ξ η ω hω
    ((TensorProduct.comm K E F).toLinearMap.baseChange L) (hτ.1 ω hω)
    (C := 1) zero_le_one (fun x y ↦ by
      change τ.norm ω _ ≤ _
      rw [hp, orthogonalTensorPair_norm_tmul_completed, one_mul, mul_comm]) z
  rw [one_mul] at h
  exact h

/-- The canonical binary commutor preserves the norm of every completed vector. -/
theorem orthogonalTensorPair_norm_comm
    (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⊗[K] F)) :
    (η ⊗ʰ ξ).norm ω
      ((TensorProduct.comm K E F).toLinearMap.baseChange (S.ϕ ω).Completion z) =
    (ξ ⊗ʰ η).norm ω z := by
  by_cases hω : ω ∈ S.Ωinf
  · let L := (S.ϕ ω).Completion
    let := hN ω hω
    let := IsRCLikeNormedField.rclike L
    let := ξ.fibreNormedAddCommGroup ω
    let := ξ.fibreNormedSpace ω
    let := ξ.fiberInnerProductSpace ω hω
    let := η.fibreNormedAddCommGroup ω
    let := η.fibreNormedSpace ω
    let := η.fiberInnerProductSpace ω hω
    rw [orthogonalTensorPair_norm_eq_hilbert _ _ ω hω,
      orthogonalTensorPair_norm_eq_hilbert _ _ ω hω, tensorBaseChangeEquiv_comm]
    exact TensorProduct.norm_comm _
  · have hfin : ω ∈ S.Ωfin := not_not.mp hω
    apply le_antisymm (orthogonalTensorPair_comm_norm_le_of_finite ξ η ω hfin z)
    let C := (TensorProduct.comm K E F).baseChange K (S.ϕ ω).Completion _ _
    have h := orthogonalTensorPair_comm_norm_le_of_finite η ξ ω hfin (C z)
    change (ξ ⊗ʰ η).norm ω (C.symm (C z)) ≤ _ at h
    rw [LinearEquiv.symm_apply_apply] at h
    exact h

variable {G : Type wG} [AddCommGroup G] [Module K G] [FiniteDimensional K G]

/-- A bound on completed triple pure tensors extends to all left-associated
vectors at a finite place. -/
theorem norm_linearMap_le_orthogonalTensorPair_left_of_finite
    (ξ : NormFamily S E) (η : NormFamily S F) (ζ : NormFamily S G)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] [hζ : ζ.IsHermitian]
    (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    {W : Type*} [SeminormedAddCommGroup W] [NormedSpace (S.ϕ ω).Completion W]
    (f : ((S.ϕ ω).Completion ⊗[K] ((E ⊗[K] F) ⊗[K] G)) →ₗ[(S.ϕ ω).Completion] W)
    (hW : ∀ x y : W, ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (hf : ∀ x y z, ‖f ((TensorProduct.AlgebraTensorModule.distribBaseChange K
      (S.ϕ ω).Completion (E ⊗[K] F) G).symm
      ((TensorProduct.AlgebraTensorModule.distribBaseChange K (S.ϕ ω).Completion E F).symm
        (x ⊗ₜ[(S.ϕ ω).Completion] y) ⊗ₜ[(S.ϕ ω).Completion] z))‖ ≤
      ξ.norm ω x * η.norm ω y * ζ.norm ω z)
    (t : (S.ϕ ω).Completion ⊗[K] ((E ⊗[K] F) ⊗[K] G)) :
    ‖f t‖ ≤ ((ξ ⊗ʰ η).orthogonalTensorPair ζ).norm ω t := by
  let L := (S.ϕ ω).Completion
  let A := TensorProduct.AlgebraTensorModule.distribBaseChange K L (E ⊗[K] F) G
  have h := norm_linearMap_le_orthogonalTensorPair_of_finite
    (ξ ⊗ʰ η) ζ
     ω hω f hW (C := 1) zero_le_one (fun u z ↦ by
      let g := f ∘ₗ A.symm.toLinearMap ∘ₗ
        (TensorProduct.mk L (L ⊗[K] (E ⊗[K] F)) (L ⊗[K] G)).flip z
      have h := norm_linearMap_le_orthogonalTensorPair_of_finite ξ η ω hω g hW
        (ζ.norm_nonneg ω z) (fun x y ↦ by
          change ‖f (A.symm (_ ⊗ₜ[L] z))‖ ≤ _
          simpa only [mul_comm (ζ.norm ω z)] using hf x y z) u
      rw [one_mul]
      rw [mul_comm (ζ.norm ω z)] at h
      exact h) t
  simpa only [one_mul] using h

/-- A bound on completed triple pure tensors extends to all right-associated
vectors at a finite place. -/
theorem norm_linearMap_le_orthogonalTensorPair_right_of_finite
    (ξ : NormFamily S E) (η : NormFamily S F) (ζ : NormFamily S G)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] [hζ : ζ.IsHermitian]
    (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    {W : Type*} [SeminormedAddCommGroup W] [NormedSpace (S.ϕ ω).Completion W]
    (f : ((S.ϕ ω).Completion ⊗[K] (E ⊗[K] (F ⊗[K] G))) →ₗ[(S.ϕ ω).Completion] W)
    (hW : ∀ x y : W, ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (hf : ∀ x y z, ‖f ((TensorProduct.AlgebraTensorModule.distribBaseChange K
      (S.ϕ ω).Completion E (F ⊗[K] G)).symm
      (x ⊗ₜ[(S.ϕ ω).Completion]
        (TensorProduct.AlgebraTensorModule.distribBaseChange K (S.ϕ ω).Completion F G).symm
          (y ⊗ₜ[(S.ϕ ω).Completion] z)))‖ ≤ ξ.norm ω x * (η.norm ω y * ζ.norm ω z))
    (t : (S.ϕ ω).Completion ⊗[K] (E ⊗[K] (F ⊗[K] G))) :
    ‖f t‖ ≤ (ξ.orthogonalTensorPair (η ⊗ʰ ζ)).norm ω t := by
  let L := (S.ϕ ω).Completion
  let A := TensorProduct.AlgebraTensorModule.distribBaseChange K L E (F ⊗[K] G)
  have h := norm_linearMap_le_orthogonalTensorPair_of_finite
    ξ (η ⊗ʰ ζ)
    ω hω f hW (C := 1) zero_le_one (fun x u ↦ by
      let g := f ∘ₗ A.symm.toLinearMap ∘ₗ
        TensorProduct.mk L (L ⊗[K] E) (L ⊗[K] (F ⊗[K] G)) x
      have h := norm_linearMap_le_orthogonalTensorPair_of_finite η ζ ω hω g hW
        (ξ.norm_nonneg ω x) (fun y z ↦ hf x y z) u
      rw [one_mul]
      exact h) t
  simpa only [one_mul] using h

/-- The actual completed associator is isometric at every finite place. -/
theorem orthogonalTensorPair_norm_assoc_of_finite
    (ξ : NormFamily S E) (η : NormFamily S F) (ζ : NormFamily S G)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] [hζ : ζ.IsHermitian]
    (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (t : (S.ϕ ω).Completion ⊗[K] ((E ⊗[K] F) ⊗[K] G)) :
    (ξ.orthogonalTensorPair (η ⊗ʰ ζ)).norm ω
      ((TensorProduct.assoc K E F G).toLinearMap.baseChange (S.ϕ ω).Completion t) =
    ((ξ ⊗ʰ η).orthogonalTensorPair ζ).norm ω t := by
  let L := (S.ϕ ω).Completion
  let σ := (ξ ⊗ʰ η).orthogonalTensorPair ζ
  let τ := ξ.orthogonalTensorPair (η ⊗ʰ ζ)
  let := σ.fibreNormedAddCommGroup ω
  let := σ.fibreNormedSpace ω
  let := τ.fibreNormedAddCommGroup ω
  let := τ.fibreNormedSpace ω
  let C := (TensorProduct.assoc K E F G).baseChange K L _ _
  have hσ := orthogonalTensorPair_isHermitian (ξ ⊗ʰ η) ζ
  have hτ := orthogonalTensorPair_isHermitian ξ (η ⊗ʰ ζ)
  change τ.norm ω (C t) = σ.norm ω t
  apply le_antisymm
  · apply norm_linearMap_le_orthogonalTensorPair_left_of_finite ξ η ζ ω hω
      C.toLinearMap (hτ.1 ω hω) _ t
    intro x y z
    change τ.norm ω ((TensorProduct.assoc K E F G).toLinearMap.baseChange L _) ≤ _
    rw [tensorBaseChangeEquiv_assoc_symm_tmul, orthogonalTensorPair_norm_tmul_completed,
      orthogonalTensorPair_norm_tmul_completed, mul_assoc]
  · have h := norm_linearMap_le_orthogonalTensorPair_right_of_finite ξ η ζ ω hω
      C.symm.toLinearMap (hσ.1 ω hω) (fun x y z ↦ by
        have he := tensorBaseChangeEquiv_assoc_symm_tmul K L E F G x y z
        change C _ = _ at he
        rw [← he, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        change σ.norm ω _ ≤ _
        rw [orthogonalTensorPair_norm_tmul_completed, orthogonalTensorPair_norm_tmul_completed,
          mul_assoc]) (C t)
    rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h
    exact h

/-- The canonical binary associator preserves the norm of every completed vector. -/
theorem orthogonalTensorPair_norm_assoc
    (ξ : NormFamily S E) (η : NormFamily S F) (ζ : NormFamily S G)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] [hζ : ζ.IsHermitian] (ω : S.Ω)
    (t : (S.ϕ ω).Completion ⊗[K] ((E ⊗[K] F) ⊗[K] G)) :
    (ξ.orthogonalTensorPair (η ⊗ʰ ζ)).norm ω
      ((TensorProduct.assoc K E F G).toLinearMap.baseChange (S.ϕ ω).Completion t) =
    ((ξ ⊗ʰ η).orthogonalTensorPair ζ).norm ω t := by
  by_cases hω : ω ∈ S.Ωinf
  · let L := (S.ϕ ω).Completion
    let := hN ω hω
    let := IsRCLikeNormedField.rclike L
    let := ξ.fibreNormedAddCommGroup ω
    let := ξ.fibreNormedSpace ω
    let := ξ.fiberInnerProductSpace ω hω
    let := η.fibreNormedAddCommGroup ω
    let := η.fibreNormedSpace ω
    let := η.fiberInnerProductSpace ω hω
    let := ζ.fibreNormedAddCommGroup ω
    let := ζ.fibreNormedSpace ω
    let := ζ.fiberInnerProductSpace ω hω
    let ξη := ξ.orthogonalTensorPair η
    let ηζ := η.orthogonalTensorPair ζ
    let hξη := orthogonalTensorPair_isHermitian ξ η
    let hηζ := orthogonalTensorPair_isHermitian η ζ
    let := ξη.fibreNormedAddCommGroup ω
    let := ξη.fibreNormedSpace ω
    let := ξη.fiberInnerProductSpace ω hω
    let := ηζ.fibreNormedAddCommGroup ω
    let := ηζ.fibreNormedSpace ω
    let := ηζ.fiberInnerProductSpace ω hω
    let eEF : (L ⊗[K] (E ⊗[K] F)) ≃ₗᵢ[L] ((L ⊗[K] E) ⊗[L] (L ⊗[K] F)) :=
      { toLinearEquiv := TensorProduct.AlgebraTensorModule.distribBaseChange K L E F
        norm_map' := fun x ↦ (orthogonalTensorPair_norm_eq_hilbert ξ η ω hω x).symm }
    let eFG : (L ⊗[K] (F ⊗[K] G)) ≃ₗᵢ[L] ((L ⊗[K] F) ⊗[L] (L ⊗[K] G)) :=
      { toLinearEquiv := TensorProduct.AlgebraTensorModule.distribBaseChange K L F G
        norm_map' := fun x ↦ (orthogonalTensorPair_norm_eq_hilbert η ζ ω hω x).symm }
    let A := TensorProduct.AlgebraTensorModule.distribBaseChange K L (E ⊗[K] F) G
    let B := TensorProduct.AlgebraTensorModule.distribBaseChange K L E (F ⊗[K] G)
    let C := (TensorProduct.assoc K E F G).toLinearMap.baseChange L
    rw [orthogonalTensorPair_norm_eq_hilbert _ _ ω hω,
      orthogonalTensorPair_norm_eq_hilbert _ _ ω hω]
    change ‖B (C t)‖ = ‖A t‖
    rw [← (TensorProduct.congrIsometry (LinearIsometryEquiv.refl L (L ⊗[K] E)) eFG).norm_map,
      ← (TensorProduct.congrIsometry eEF (LinearIsometryEquiv.refl L (L ⊗[K] G))).norm_map (A t)]
    change ‖TensorProduct.map LinearMap.id
      (TensorProduct.AlgebraTensorModule.distribBaseChange K L F G).toLinearMap (B (C t))‖ =
      ‖TensorProduct.map (TensorProduct.AlgebraTensorModule.distribBaseChange K L E F).toLinearMap
        LinearMap.id (A t)‖
    rw [tensorBaseChangeEquiv_assoc]
    exact TensorProduct.norm_assoc _
  · exact orthogonalTensorPair_norm_assoc_of_finite ξ η ζ ω (not_not.mp hω) t

end BinaryCoherence

end NormFamily

section EvaluationCoherence

variable {K : Type*} [Field K]

/-- Simultaneous reindexing preserves the full finite tensor evaluation pairing. -/
theorem piDualDistrib_reindex_apply
    {I J : Type*} [Finite I] [Finite J] {V : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] (e : I ≃ J)
    (z : ⨂[K] i, Module.Dual K (V i)) (x : ⨂[K] i, V i) :
    PiTensorProduct.dualDistrib
      (PiTensorProduct.reindex K (fun i ↦ Module.Dual K (V i)) e z)
      (PiTensorProduct.reindex K V e x) = PiTensorProduct.dualDistrib z x := by
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  induction z using PiTensorProduct.induction_on with
  | add z t hz ht => simp only [map_add, LinearMap.add_apply, hz, ht]
  | smul_tprod a f =>
    induction x using PiTensorProduct.induction_on with
    | add x y hx hy => simp only [map_add, hx, hy]
    | smul_tprod b x =>
      simp only [map_smul, PiTensorProduct.reindex_tprod, LinearMap.smul_apply,
        PiTensorProduct.dualDistrib_apply, smul_eq_mul]
      congr 2
      exact Fintype.prod_equiv e.symm _ _ (fun _ ↦ rfl)

/-- Tensor dual distribution commutes with ordinary associativity on all tensors. -/
theorem dualDistrib_assoc_apply
    {E F G : Type*} [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
    [AddCommGroup G] [Module K G]
    (z : (Module.Dual K E ⊗[K] Module.Dual K F) ⊗[K] Module.Dual K G)
    (x : (E ⊗[K] F) ⊗[K] G) :
    TensorProduct.dualDistrib K E (F ⊗[K] G)
      (TensorProduct.map LinearMap.id (TensorProduct.dualDistrib K F G)
        (TensorProduct.assoc K (Module.Dual K E) (Module.Dual K F) (Module.Dual K G) z))
      (TensorProduct.assoc K E F G x) =
    TensorProduct.dualDistrib K (E ⊗[K] F) G
      (TensorProduct.map (TensorProduct.dualDistrib K E F) LinearMap.id z) x := by
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simp only [map_add, LinearMap.add_apply, hz, ht]
  | tmul z h =>
    induction z using TensorProduct.inductionOn with
    | add z t hz ht => simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, hz, ht]
    | tmul f g =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x w =>
        induction x using TensorProduct.inductionOn with
        | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
        | tmul u v =>
          simp only [TensorProduct.assoc_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
            TensorProduct.dualDistrib_apply, mul_assoc]

/-- Joining arbitrary finite dual tensors intertwines finite and binary evaluation. -/
theorem piDualDistrib_tmulEquivDep_apply
    {I J : Type*} [Finite I] [Finite J] {V : I ⊕ J → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (z : (⨂[K] i, Module.Dual K (V (.inl i))) ⊗[K]
      (⨂[K] j, Module.Dual K (V (.inr j))))
    (x : (⨂[K] i, V (.inl i)) ⊗[K] (⨂[K] j, V (.inr j))) :
    PiTensorProduct.dualDistrib
      (PiTensorProduct.tmulEquivDep K (fun i ↦ Module.Dual K (V i)) z)
      (PiTensorProduct.tmulEquivDep K V x) =
    TensorProduct.dualDistrib K (⨂[K] i, V (.inl i)) (⨂[K] j, V (.inr j))
      (TensorProduct.map PiTensorProduct.dualDistrib PiTensorProduct.dualDistrib z) x := by
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simp only [map_add, LinearMap.add_apply, hz, ht]
  | tmul f g =>
    induction f using PiTensorProduct.induction_on with
    | add f h hf hh => simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, hf, hh]
    | smul_tprod a f =>
      induction g using PiTensorProduct.induction_on with
      | add g h hg hh => simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, hg, hh]
      | smul_tprod b g =>
        induction x using TensorProduct.inductionOn with
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul x y =>
          induction x using PiTensorProduct.induction_on with
          | add x u hx hu => simp only [TensorProduct.add_tmul, map_add, hx, hu]
          | smul_tprod c x =>
            induction y using PiTensorProduct.induction_on with
            | add y v hy hv => simp only [TensorProduct.tmul_add, map_add, hy, hv]
            | smul_tprod d y =>
              simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul,
                PiTensorProduct.tmulEquivDep_apply, LinearMap.smul_apply,
                PiTensorProduct.dualDistrib_apply, TensorProduct.map_tmul,
                TensorProduct.dualDistrib_apply, Fintype.prod_sum_type, smul_eq_mul]

end EvaluationCoherence

section BinaryEvaluationBaseChange

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  (E F : Type*) [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- Binary dual distribution commutes with scalar extension on arbitrary dual
and primal tensors, not merely on decomposable primal vectors. -/
theorem dualDistrib_baseChange_tensor_apply
    (z : L ⊗[K] (Module.Dual K E ⊗[K] Module.Dual K F))
    (x : L ⊗[K] (E ⊗[K] F)) :
    dualBaseChangeEquiv K L (E ⊗[K] F)
      ((TensorProduct.dualDistrib K E F).baseChange L z) x =
    TensorProduct.dualDistrib L (L ⊗[K] E) (L ⊗[K] F)
      (TensorProduct.map (dualBaseChangeEquiv K L E).toLinearMap
        (dualBaseChangeEquiv K L F).toLinearMap
        (TensorProduct.AlgebraTensorModule.distribBaseChange K L
          (Module.Dual K E) (Module.Dual K F) z))
      (TensorProduct.AlgebraTensorModule.distribBaseChange K L E F x) := by
  let A := TensorProduct.AlgebraTensorModule.distribBaseChange K L E F
  obtain ⟨t, rfl⟩ := A.symm.surjective x
  induction t using TensorProduct.inductionOn with
  | add t u ht hu => simp only [map_add, ht, hu]
  | tmul x y =>
    rw [LinearEquiv.apply_symm_apply]
    rw [dualDistrib_baseChange_bilinear_apply]
    generalize TensorProduct.map (dualBaseChangeEquiv K L E).toLinearMap
      (dualBaseChangeEquiv K L F).toLinearMap
      (TensorProduct.AlgebraTensorModule.distribBaseChange K L
        (Module.Dual K E) (Module.Dual K F) z) = q
    induction q using TensorProduct.inductionOn with
    | add q r hq hr => simp only [map_add, LinearMap.add_apply, hq, hr]
    | tmul f g =>
      simp only [dualTensorHom_apply, TensorProduct.dualDistrib_apply, LinearMap.smul_apply,
        smul_eq_mul]

end BinaryEvaluationBaseChange

end ArakelovGeometry
