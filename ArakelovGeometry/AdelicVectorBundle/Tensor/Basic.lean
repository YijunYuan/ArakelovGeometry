/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Dual.Basic
public import ArakelovGeometry.AdelicVectorBundle.Tensor.BaseChange
public import ArakelovGeometry.Analysis.Tensor.Basic

import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Tensor products of norm families

The projective and injective tensor norms are transported to the actual
completed scalar extensions of finite tensor products. The mixed norm uses
the injective norm at non-Archimedean places and the projective norm elsewhere.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w wι

noncomputable section

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
variable {ι : Type wι} [Fintype ι]
variable {E : ι → Type w} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)]
variable (ξ : ∀ i, NormFamily S (E i))

/-- The projective tensor seminorm transported along canonical completed
scalar extension. -/
def projectiveTensorSeminorm (ω : S.Ω) :
    Seminorm (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) := by
  letI : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  letI : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedSpace ω
  exact PiTensorProduct.projectiveSeminorm.comp
    (tensorBaseChangeEquiv K (S.ϕ ω).Completion E).toLinearMap

/-- The projective tensor seminorm separates zero on the actual completed fibre. -/
theorem projectiveTensorSeminorm_eq_zero_iff (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    projectiveTensorSeminorm ξ ω z = 0 ↔ z = 0 := by
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedSpace ω
  change PiTensorProduct.projectiveSeminorm
    (tensorBaseChangeEquiv K (S.ϕ ω).Completion E z) = 0 ↔ _
  rw [ArakelovGeometry.projectiveSeminorm_eq_zero_iff, LinearEquiv.map_eq_zero_iff]

/-- The projective tensor norm family of a finite family of vector spaces. -/
def projectiveTensor : NormFamily S (⨂[K] i, E i) where
  norm := projectiveTensorSeminorm ξ
  norm_eq_zero_iff := projectiveTensorSeminorm_eq_zero_iff ξ

/-- The true injective tensor seminorm, defined by products of dual evaluations,
transported along canonical completed scalar extension. -/
def injectiveTensorSeminorm (ω : S.Ω) :
    Seminorm (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) := by
  letI : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  letI : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedSpace ω
  exact ArakelovGeometry.injectiveTensorSeminorm.comp
    (tensorBaseChangeEquiv K (S.ϕ ω).Completion E).toLinearMap

/-- The injective tensor seminorm separates zero on the actual completed fibre. -/
theorem injectiveTensorSeminorm_eq_zero_iff (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    injectiveTensorSeminorm ξ ω z = 0 ↔ z = 0 := by
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedSpace ω
  change ArakelovGeometry.injectiveTensorSeminorm
    (tensorBaseChangeEquiv K (S.ϕ ω).Completion E z) = 0 ↔ _
  rw [ArakelovGeometry.injectiveTensorSeminorm_eq_zero_iff, LinearEquiv.map_eq_zero_iff]

/-- The injective tensor norm family of a finite family of vector spaces. -/
def injectiveTensor : NormFamily S (⨂[K] i, E i) where
  norm := injectiveTensorSeminorm ξ
  norm_eq_zero_iff := injectiveTensorSeminorm_eq_zero_iff ξ

/-- The projective norm is exactly the infimum over finite sums of pure
completed tensors, as in the source's definition. -/
theorem projectiveTensor_norm_eq_sInf [Nonempty ι] (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (projectiveTensor ξ).norm ω z = sInf {r : ℝ |
      ∃ p : List (∀ i, (S.ϕ ω).Completion ⊗[K] E i),
        (p.map fun x ↦ ⨂ₜ[(S.ϕ ω).Completion] i, x i).sum =
          tensorBaseChangeEquiv K (S.ϕ ω).Completion E z ∧
        (p.map fun x ↦ ∏ i, (ξ i).norm ω (x i)).sum = r} := by
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedSpace ω
  exact ArakelovGeometry.projectiveSeminorm_eq_sInf _

/-- The injective norm is exactly the supremum of products of nonzero
completed dual evaluations divided by the products of their dual norms. -/
theorem injectiveTensor_norm_eq_sSup (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (injectiveTensor ξ).norm ω z = sSup {r : ℝ |
      ∃ φ : ∀ i, (S.ϕ ω).Completion ⊗[K] Module.Dual K (E i),
        (∀ i, φ i ≠ 0) ∧
        ‖PiTensorProduct.dualDistrib (⨂ₜ[(S.ϕ ω).Completion] i,
            dualBaseChangeEquiv K (S.ϕ ω).Completion (E i) (φ i))
          (tensorBaseChangeEquiv K (S.ϕ ω).Completion E z)‖ /
          ∏ i, (ξ i).dual.norm ω (φ i) = r} := by
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedSpace ω
  change ArakelovGeometry.injectiveTensorSeminorm
    (tensorBaseChangeEquiv K (S.ϕ ω).Completion E z) = _
  rw [ArakelovGeometry.injectiveTensorSeminorm_eq_sSup_nonzero]
  congr 1
  ext r
  constructor
  · rintro ⟨φ, hφ, hr⟩
    refine ⟨fun i ↦ (dualBaseChangeEquiv K (S.ϕ ω).Completion (E i)).symm (φ i),
      fun i ↦ ?_, ?_⟩
    · exact fun h ↦ hφ i ((LinearEquiv.map_eq_zero_iff _).mp h)
    · simpa only [tensorDualEval, dual, dualSeminorm, Seminorm.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] using hr
  · rintro ⟨φ, hφ, hr⟩
    refine ⟨fun i ↦ dualBaseChangeEquiv K (S.ϕ ω).Completion (E i) (φ i),
      fun i ↦ ?_, hr⟩
    exact fun h ↦ hφ i ((LinearEquiv.map_eq_zero_iff _).mp h)

/-- The injective norm is at most the projective norm at every place. -/
theorem injectiveTensor_norm_le_projectiveTensor_norm (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (injectiveTensor ξ).norm ω z ≤ (projectiveTensor ξ).norm ω z := by
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedSpace ω
  exact ArakelovGeometry.injectiveTensorSeminorm_le_projective _

/-- The projective norm bounds a pure completed tensor by the product of
the factor norms. -/
theorem projectiveTensor_norm_tprod_le (ω : S.Ω)
    (x : ∀ i, (S.ϕ ω).Completion ⊗[K] E i) :
    (projectiveTensor ξ).norm ω
      ((tensorBaseChangeEquiv K (S.ϕ ω).Completion E).symm
        (⨂ₜ[(S.ϕ ω).Completion] i, x i)) ≤ ∏ i, (ξ i).norm ω (x i) := by
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedSpace ω
  change PiTensorProduct.projectiveSeminorm
    ((tensorBaseChangeEquiv K (S.ϕ ω).Completion E)
      ((tensorBaseChangeEquiv K (S.ϕ ω).Completion E).symm _)) ≤ _
  rw [LinearEquiv.apply_symm_apply]
  exact PiTensorProduct.projectiveSeminorm_tprod_le x

/-- The injective family is ultrametric at every non-Archimedean place. -/
theorem injectiveTensor_isUltrametric : (injectiveTensor ξ).IsUltrametric := by
  constructor
  intro ω hω z t
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedSpace ω
  have hL (a b : (S.ϕ ω).Completion) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
    refine UniformSpace.Completion.induction_on₂ a b ?_ ?_
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · intro x y
      simpa only [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe]
        using (show ‖x + y‖ ≤ max ‖x‖ ‖y‖ from hω x.ofAbs y.ofAbs)
  change ArakelovGeometry.injectiveTensorSeminorm
    (tensorBaseChangeEquiv K (S.ϕ ω).Completion E (z + t)) ≤
      max (ArakelovGeometry.injectiveTensorSeminorm
        (tensorBaseChangeEquiv K (S.ϕ ω).Completion E z))
        (ArakelovGeometry.injectiveTensorSeminorm
          (tensorBaseChangeEquiv K (S.ϕ ω).Completion E t))
  rw [map_add]
  exact ArakelovGeometry.injectiveTensorSeminorm_add_le_max hL _ _

/-- The source's mixed tensor norm: injective at non-Archimedean places,
projective at the remaining places. -/
def mixedTensor : NormFamily S (⨂[K] i, E i) := by
  classical
  exact {
    norm := fun ω ↦
      if ω ∈ S.Ωfin then (injectiveTensor ξ).norm ω else (projectiveTensor ξ).norm ω
    norm_eq_zero_iff := fun ω z ↦ by
      split <;> exact NormFamily.norm_eq_zero_iff _ ω z }

@[simp]
theorem mixedTensor_norm_of_mem_Ωfin (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (mixedTensor ξ).norm ω z = (injectiveTensor ξ).norm ω z := by
  simp [mixedTensor, hω]

@[simp]
theorem mixedTensor_norm_of_not_mem_Ωfin (ω : S.Ω) (hω : ω ∉ S.Ωfin)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (mixedTensor ξ).norm ω z = (projectiveTensor ξ).norm ω z := by
  simp [mixedTensor, hω]

/-- The mixed tensor family is ultrametric at all non-Archimedean places. -/
theorem mixedTensor_isUltrametric : (mixedTensor ξ).IsUltrametric := by
  constructor
  intro ω hω z t
  simp only [mixedTensor_norm_of_mem_Ωfin ξ ω hω]
  exact injectiveTensor_isUltrametric ξ ω hω z t

/-- For an empty family the projective norm is the completed scalar norm
under the canonical empty-tensor identification. -/
theorem projectiveTensor_norm_isEmpty [IsEmpty ι] (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (projectiveTensor ξ).norm ω z = ‖PiTensorProduct.isEmptyEquiv ι
      (tensorBaseChangeEquiv K (S.ϕ ω).Completion E z)‖ := by
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedSpace ω
  exact ArakelovGeometry.projectiveSeminorm_isEmpty _

/-- For an empty family the injective norm is the same completed scalar norm. -/
theorem injectiveTensor_norm_isEmpty [IsEmpty ι] (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (injectiveTensor ξ).norm ω z = ‖PiTensorProduct.isEmptyEquiv ι
      (tensorBaseChangeEquiv K (S.ϕ ω).Completion E z)‖ := by
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedSpace ω
  exact ArakelovGeometry.injectiveTensorSeminorm_isEmpty _

/-- Empty tensor products give the same norm for all three constructions. -/
theorem mixedTensor_norm_isEmpty [IsEmpty ι] (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (mixedTensor ξ).norm ω z = ‖PiTensorProduct.isEmptyEquiv ι
      (tensorBaseChangeEquiv K (S.ϕ ω).Completion E z)‖ := by
  by_cases hω : ω ∈ S.Ωfin
  · rw [mixedTensor_norm_of_mem_Ωfin ξ ω hω, injectiveTensor_norm_isEmpty]
  · rw [mixedTensor_norm_of_not_mem_Ωfin ξ ω hω, projectiveTensor_norm_isEmpty]

/-- In particular, the empty tensor unit has norm one at every place. -/
theorem tensor_norms_empty_tmul [IsEmpty ι] (ω : S.Ω)
    (a : (S.ϕ ω).Completion) (x : ∀ i, E i) :
    (projectiveTensor ξ).norm ω (a ⊗ₜ[K] (⨂ₜ[K] i, x i)) = ‖a‖ ∧
    (injectiveTensor ξ).norm ω (a ⊗ₜ[K] (⨂ₜ[K] i, x i)) = ‖a‖ ∧
    (mixedTensor ξ).norm ω (a ⊗ₜ[K] (⨂ₜ[K] i, x i)) = ‖a‖ := by
  simp only [projectiveTensor_norm_isEmpty, injectiveTensor_norm_isEmpty,
    mixedTensor_norm_isEmpty, tensorBaseChangeEquiv_tmul_tprod, map_smul,
    PiTensorProduct.isEmptyEquiv_apply_tprod, smul_eq_mul, mul_one, and_self]

/-- If one factor has dimension zero, every completed tensor norm vanishes. -/
theorem tensor_norms_eq_zero_of_subsingleton (i₀ : ι) [Subsingleton (E i₀)]
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (projectiveTensor ξ).norm ω z = 0 ∧
    (injectiveTensor ξ).norm ω z = 0 ∧ (mixedTensor ξ).norm ω z = 0 := by
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedSpace ω
  have h := ArakelovGeometry.tensorSeminorms_eq_zero_of_subsingleton i₀
    (tensorBaseChangeEquiv K (S.ϕ ω).Completion E z)
  change (projectiveTensor ξ).norm ω z = 0 ∧ (injectiveTensor ξ).norm ω z = 0 at h
  refine ⟨h.1, h.2, ?_⟩
  by_cases hω : ω ∈ S.Ωfin
  · rw [mixedTensor_norm_of_mem_Ωfin ξ ω hω, h.2]
  · rw [mixedTensor_norm_of_not_mem_Ωfin ξ ω hω, h.1]

/-- The projective construction on a single factor recovers its given norm. -/
theorem projectiveTensor_norm_unique [Unique ι] (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (projectiveTensor ξ).norm ω z = (ξ default).norm ω
      (PiTensorProduct.subsingletonEquiv default
        (tensorBaseChangeEquiv K (S.ϕ ω).Completion E z)) := by
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedSpace ω
  exact ArakelovGeometry.projectiveSeminorm_unique _

/-- On a single factor the injective construction gives the bidual norm under
evaluation. Equality with the given norm needs the separate reflexivity
hypotheses; none are assumed in this construction. -/
theorem injectiveTensor_norm_unique [Unique ι] (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (injectiveTensor ξ).norm ω z = (ξ default).dual.dual.norm ω
      ((Module.Dual.eval K (E default)).baseChange (S.ϕ ω).Completion
        (PiTensorProduct.subsingletonEquiv default
          (tensorBaseChangeEquiv K (S.ϕ ω).Completion E z))) := by
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedSpace ω
  change ArakelovGeometry.injectiveTensorSeminorm
    (tensorBaseChangeEquiv K (S.ϕ ω).Completion E z) = _
  rw [ArakelovGeometry.injectiveTensorSeminorm_unique, dual_norm_eq_sSup]
  simp only [dualBaseChangeEquiv_eval, LinearEquiv.dualMap_apply, Module.Dual.eval_apply]
  congr 1
  ext r
  constructor
  · rintro ⟨φ, hr⟩
    refine ⟨(dualBaseChangeEquiv K (S.ϕ ω).Completion (E default)).symm φ, ?_⟩
    simpa only [dual, dualSeminorm, Seminorm.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using hr
  · rintro ⟨φ, hr⟩
    exact ⟨dualBaseChangeEquiv K (S.ϕ ω).Completion (E default) φ, hr⟩

end

end ArakelovGeometry.NormFamily
