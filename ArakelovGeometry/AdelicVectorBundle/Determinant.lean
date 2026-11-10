/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Exterior
public import ArakelovGeometry.AdelicVectorBundle.Line
public import ArakelovGeometry.Analysis.DeterminantNorm

/-!
# Determinant norm families

The determinant norm is the quotient of the projective top tensor-power norm
on the actual completed determinant line. It agrees with the mixed top exterior
norm at every place. At non-Archimedean places the proof uses nearly optimal
bases and the injective tensor contraction theorem, including dimension zero.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w

noncomputable section

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
variable {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ξ : NormFamily S E)

/-- The determinant family is the projective tensor quotient on the actual
top exterior power, as specified by the local determinant norm. -/
def determinant : NormFamily S (⋀[K]^(Module.finrank K E) E) :=
  (projectiveTensor (fun _ : Fin (Module.finrank K E) ↦ ξ)).pushforward
    (tensorToExterior K E (Module.finrank K E))
    (tensorToExterior_surjective K E (Module.finrank K E))

/-- The determinant space is a line even when the original space has dimension zero. -/
theorem determinant_finrank : Module.finrank K (⋀[K]^(Module.finrank K E) E) = 1 := by
  rw [_root_.exteriorPower.finrank_eq, Nat.choose_self]

/-- The determinant norm is the infimum of projective norms of all completed
tensor lifts. -/
theorem determinant_norm_eq_sInf (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    ξ.determinant.norm ω z = sInf
      ((projectiveTensor (fun _ : Fin (Module.finrank K E) ↦ ξ)).norm ω ''
        {x | (tensorToExterior K E (Module.finrank K E)).baseChange
          (S.ϕ ω).Completion x = z}) :=
  (projectiveTensor (fun _ : Fin (Module.finrank K E) ↦ ξ)).pushforward_norm_eq_sInf
    (tensorToExterior K E (Module.finrank K E))
    (tensorToExterior_surjective K E (Module.finrank K E)) ω z

/-- The canonical determinant quotient contracts the projective tensor norm. -/
theorem determinant_norm_le (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] (⨂[K] (_ : Fin (Module.finrank K E)), E)) :
    ξ.determinant.norm ω ((tensorToExterior K E (Module.finrank K E)).baseChange
      (S.ϕ ω).Completion x) ≤
        (projectiveTensor (fun _ : Fin (Module.finrank K E) ↦ ξ)).norm ω x :=
  (projectiveTensor (fun _ : Fin (Module.finrank K E) ↦ ξ)).pushforward_norm_le
    (tensorToExterior K E (Module.finrank K E))
    (tensorToExterior_surjective K E (Module.finrank K E)) ω x

/-- Hadamard's upper bound for every decomposable completed determinant tensor. -/
theorem determinant_norm_ιMulti_le (ω : S.Ω)
    (x : Fin (Module.finrank K E) → (S.ϕ ω).Completion ⊗[K] E) :
    ξ.determinant.norm ω
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm
        (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K E) x)) ≤
      ∏ i, ξ.norm ω (x i) := by
  have hx : (tensorToExterior K E (Module.finrank K E)).baseChange (S.ϕ ω).Completion
      ((tensorBaseChangeEquiv K (S.ϕ ω).Completion
          (fun _ : Fin (Module.finrank K E) ↦ E)).symm
        (⨂ₜ[(S.ϕ ω).Completion] i, x i)) =
        (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm
          (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K E) x) := by
    apply (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).injective
    rw [exteriorBaseChangeEquiv_tensorToExterior, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, tensorToExterior_tprod]
  rw [← hx]
  exact (ξ.determinant_norm_le ω _).trans
    (projectiveTensor_norm_tprod_le (fun _ : Fin (Module.finrank K E) ↦ ξ) ω x)

/-- The mixed top exterior norm is bounded by the determinant norm. -/
theorem exteriorPower_norm_le_determinant_norm (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    (ξ.exteriorPower (Module.finrank K E)).norm ω z ≤ ξ.determinant.norm ω z := by
  apply (le_quotientSeminorm_iff _ _
    (tensorToExterior_surjective K E (Module.finrank K E)) ω z _).2
  intro x hx
  rw [← hx]
  refine (ξ.exteriorPower_norm_le _ ω x).trans ?_
  by_cases hω : ω ∈ S.Ωfin
  · rw [mixedTensor_norm_of_mem_Ωfin _ ω hω]
    exact injectiveTensor_norm_le_projectiveTensor_norm _ ω x
  · rw [mixedTensor_norm_of_not_mem_Ωfin _ ω hω]

/-- At an Archimedean place the mixed exterior and projective determinant
constructions agree directly. -/
theorem determinant_norm_eq_exteriorPower_norm_of_not_mem_Ωfin (ω : S.Ω)
    (hω : ω ∉ S.Ωfin) (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    ξ.determinant.norm ω z = (ξ.exteriorPower (Module.finrank K E)).norm ω z := by
  apply le_antisymm _ (ξ.exteriorPower_norm_le_determinant_norm ω z)
  apply (le_quotientSeminorm_iff _ _
    (tensorToExterior_surjective K E (Module.finrank K E)) ω z _).2
  intro x hx
  rw [mixedTensor_norm_of_not_mem_Ωfin _ ω hω, ← hx]
  exact ξ.determinant_norm_le ω x

/-- The determinant and mixed exterior constructions agree in rank zero
at every place, by their common empty-tensor convention. -/
theorem determinant_eq_exteriorPower_of_finrank_eq_zero (h : Module.finrank K E = 0) :
    ξ.determinant = ξ.exteriorPower (Module.finrank K E) := by
  let : IsEmpty (Fin (Module.finrank K E)) := by rw [h]; infer_instance
  ext ω z
  apply le_antisymm _ (ξ.exteriorPower_norm_le_determinant_norm ω z)
  apply (le_quotientSeminorm_iff _ _
    (tensorToExterior_surjective K E (Module.finrank K E)) ω z _).2
  intro x hx
  have hn : (mixedTensor (fun _ : Fin (Module.finrank K E) ↦ ξ)).norm ω x =
      (projectiveTensor (fun _ : Fin (Module.finrank K E) ↦ ξ)).norm ω x := by
    rw [mixedTensor_norm_isEmpty, projectiveTensor_norm_isEmpty]
  rw [hn, ← hx]
  exact ξ.determinant_norm_le ω x

/-- In rank zero a scalar multiple of the empty wedge has its scalar norm;
in particular the determinant unit has norm one. -/
theorem determinant_norm_empty_tmul (h : Module.finrank K E = 0) (ω : S.Ω)
    (a : (S.ϕ ω).Completion) (x : Fin (Module.finrank K E) → E) :
    ξ.determinant.norm ω
      (a ⊗ₜ[K] _root_.exteriorPower.ιMulti K (Module.finrank K E) x) = ‖a‖ := by
  let : IsEmpty (Fin (Module.finrank K E)) := by rw [h]; infer_instance
  have hi : Function.Injective (tensorToExterior K E (Module.finrank K E)) := by
    rw [h]
    exact (tensorToExterior_zero_bijective K E).1
  rw [determinant, ← tensorToExterior_tprod, ← LinearMap.baseChange_tmul,
    pushforward_norm_of_injective _ _ _ hi]
  exact (tensor_norms_empty_tmul (fun _ : Fin (Module.finrank K E) ↦ ξ) ω a x).1

/-- Every completed fibre has nearly optimal bases measured by the given
family and its actual completed dual family. This includes dimension zero. -/
theorem exists_completedBasis_norm_mul_dual_norm_le (ω : S.Ω)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ b : Module.Basis (Fin (Module.finrank K E)) (S.ϕ ω).Completion
        ((S.ϕ ω).Completion ⊗[K] E), ∀ i,
      1 ≤ ξ.norm ω (b i) * ξ.dual.norm ω
        ((dualBaseChangeEquiv K (S.ϕ ω).Completion E).symm (b.coord i)) ∧
      ξ.norm ω (b i) * ξ.dual.norm ω
        ((dualBaseChangeEquiv K (S.ϕ ω).Completion E).symm (b.coord i)) ≤ α⁻¹ := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  obtain ⟨b, hb⟩ := exists_basis_mul_dual_norm_le
    ((Module.finBasis K E).baseChange (S.ϕ ω).Completion) hα hα1
  refine ⟨b, fun i ↦ ?_⟩
  simp only [dual, dualSeminorm, Seminorm.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  change 1 ≤ ‖b i‖ * linearMapOperatorSeminorm (b.coord i) ∧
    ‖b i‖ * linearMapOperatorSeminorm (b.coord i) ≤ α⁻¹
  exact hb i

/-- The determinant quotient contracts the genuine injective tensor norm
at every non-Archimedean place, without any ultrametricity assumption on the
original vector norm. The empty tensor power is included. -/
theorem determinant_norm_le_injectiveTensor_norm (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] (_ : Fin (Module.finrank K E)), E)) :
    ξ.determinant.norm ω ((tensorToExterior K E (Module.finrank K E)).baseChange
      (S.ϕ ω).Completion z) ≤
        (injectiveTensor (fun _ : Fin (Module.finrank K E) ↦ ξ)).norm ω z := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := ξ.determinant.fibreNormedAddCommGroup ω
  let := ξ.determinant.fibreNormedSpace ω
  let e := tensorBaseChangeEquiv K (S.ϕ ω).Completion
    (fun _ : Fin (Module.finrank K E) ↦ E)
  let f := ((tensorToExterior K E (Module.finrank K E)).baseChange
    (S.ϕ ω).Completion).comp e.symm.toLinearMap
  have hf (x : Fin (Module.finrank K E) → (S.ϕ ω).Completion ⊗[K] E) :
      ‖f (⨂ₜ[(S.ϕ ω).Completion] i, x i)‖ ≤ ∏ i, ‖x i‖ := by
    have hx : f (⨂ₜ[(S.ϕ ω).Completion] i, x i) =
        (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm
          (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K E) x) := by
      apply (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).injective
      change (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E))
        ((tensorToExterior K E (Module.finrank K E)).baseChange (S.ϕ ω).Completion
          (e.symm _)) = _
      rw [exteriorBaseChangeEquiv_tensorToExterior, LinearEquiv.apply_symm_apply]
      simp only [LinearEquiv.apply_symm_apply, tensorToExterior_tprod]
    rw [hx]
    exact ξ.determinant_norm_ιMulti_le ω x
  have hdet : ∀ x y : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E),
      ‖x + y‖ ≤ max ‖x‖ ‖y‖ :=
    ξ.determinant.isUltrametric_of_finrank_le_one (determinant_finrank.le) ω hω
  have H := norm_linearMap_le_injective_of_ultrametric f hdet hf (e z)
  change ‖(tensorToExterior K E (Module.finrank K E)).baseChange
    (S.ϕ ω).Completion z‖ ≤ ArakelovGeometry.injectiveTensorSeminorm (e z)
  simpa only [f, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using H

/-- The projective determinant norm and the mixed top exterior norm agree
at every place, including rank zero. -/
theorem determinant_eq_exteriorPower :
    ξ.determinant = ξ.exteriorPower (Module.finrank K E) := by
  ext ω z
  by_cases hω : ω ∈ S.Ωfin
  · apply le_antisymm _ (ξ.exteriorPower_norm_le_determinant_norm ω z)
    apply (le_quotientSeminorm_iff _ _
      (tensorToExterior_surjective K E (Module.finrank K E)) ω z _).2
    intro x hx
    rw [mixedTensor_norm_of_mem_Ωfin _ ω hω, ← hx]
    exact ξ.determinant_norm_le_injectiveTensor_norm ω hω x
  · exact ξ.determinant_norm_eq_exteriorPower_norm_of_not_mem_Ωfin ω hω z

/-- In positive rank, every completed determinant vector admits a single
wedge presentation of cost arbitrarily close above its determinant norm. -/
theorem exists_determinant_ιMulti_norm_lt (hr : 0 < Module.finrank K E) (ω : S.Ω)
    (η : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : Fin (Module.finrank K E) → (S.ϕ ω).Completion ⊗[K] E,
      (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm
          (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K E) x) = η ∧
        (∏ i, ξ.norm ω (x i)) < ξ.determinant.norm ω η + ε := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let : Nonempty (Fin (Module.finrank K E)) := ⟨⟨0, hr⟩⟩
  let b := (Module.finBasis K E).baseChange (S.ϕ ω).Completion
  let g := _root_.exteriorPower.alternatingMapLinearEquiv b.det
  have hg : g.comp (tensorToExterior (S.ϕ ω).Completion
      ((S.ϕ ω).Completion ⊗[K] E) (Module.finrank K E)) =
      PiTensorProduct.lift b.det.toMultilinearMap := by
    apply PiTensorProduct.ext
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      tensorToExterior_tprod, g, _root_.exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      PiTensorProduct.lift.tprod, AlternatingMap.coe_multilinearMap]
  obtain ⟨z, hz, hc⟩ :=
    (projectiveTensor (fun _ : Fin (Module.finrank K E) ↦ ξ)).exists_quotientSeminorm_lift_lt
      (tensorToExterior K E (Module.finrank K E))
      (tensorToExterior_surjective K E (Module.finrank K E)) ω η hε
  obtain ⟨x, hx, hcost⟩ := exists_det_eq_prod_norm_lt_of_projective b
    (tensorBaseChangeEquiv K (S.ϕ ω).Completion (fun _ : Fin (Module.finrank K E) ↦ E) z) hc
  refine ⟨x, ?_, hcost⟩
  apply (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).injective
  rw [LinearEquiv.apply_symm_apply, ← hz, exteriorBaseChangeEquiv_tensorToExterior]
  apply determinantCoordinate_injective b
  rw [_root_.exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change b.det x = g (tensorToExterior (S.ϕ ω).Completion
    ((S.ϕ ω).Completion ⊗[K] E) (Module.finrank K E) _)
  rw [← LinearMap.comp_apply, hg]
  exact hx

/-- The actual completed determinant norm is exactly the infimum over
single wedge presentations in positive rank, as in the local source formula. -/
theorem determinant_norm_eq_sInf_ιMulti (hr : 0 < Module.finrank K E) (ω : S.Ω)
    (η : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    ξ.determinant.norm ω η = sInf {c : ℝ |
      ∃ x : Fin (Module.finrank K E) → (S.ϕ ω).Completion ⊗[K] E,
        (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm
            (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K E) x) = η ∧
          (∏ i, ξ.norm ω (x i)) = c} := by
  have hne : {c : ℝ |
      ∃ x : Fin (Module.finrank K E) → (S.ϕ ω).Completion ⊗[K] E,
        (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm
            (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K E) x) = η ∧
          (∏ i, ξ.norm ω (x i)) = c}.Nonempty := by
    obtain ⟨x, hx, _⟩ := ξ.exists_determinant_ιMulti_norm_lt hr ω η zero_lt_one
    exact ⟨_, x, hx, rfl⟩
  have hb : BddBelow {c : ℝ |
      ∃ x : Fin (Module.finrank K E) → (S.ϕ ω).Completion ⊗[K] E,
        (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm
            (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K E) x) = η ∧
          (∏ i, ξ.norm ω (x i)) = c} := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, _, rfl⟩
    exact Finset.prod_nonneg fun _ _ ↦ ξ.norm_nonneg ω _
  apply le_antisymm
  · apply le_csInf hne
    rintro _ ⟨x, hx, rfl⟩
    rw [← hx]
    exact ξ.determinant_norm_ιMulti_le ω x
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨x, hx, hc⟩ := ξ.exists_determinant_ιMulti_norm_lt hr ω η hε
    exact (csInf_le hb ⟨x, hx, rfl⟩).trans hc.le

end

end ArakelovGeometry.NormFamily
