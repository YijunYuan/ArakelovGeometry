/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.ScalarExtensionNorm

/-!
# Contractive scalar retractions

A contractive linear retraction of the extending scalar field induces a
contraction from the actual projective scalar extension to the original
vector space. If it fixes one, rational vectors retain their original norm.
-/

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

section Algebraic

variable {k l V : Type*} [CommRing k] [AddCommGroup l] [Module k l]
  [AddCommGroup V] [Module k V]

/-- Apply the scalar retraction to the first tensor factor, then cancel the base field. -/
def scalarExtensionRetraction (π : l →ₗ[k] k) : l ⊗[k] V →ₗ[k] V :=
  (TensorProduct.lid k V).toLinearMap.comp (π.rTensor V)

@[simp]
theorem scalarExtensionRetraction_tmul (π : l →ₗ[k] k) (a : l) (x : V) :
    scalarExtensionRetraction π (a ⊗ₜ[k] x) = π a • x := by
  simp only [scalarExtensionRetraction, LinearMap.comp_apply,
    LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul]

end Algebraic

variable {k l V : Type*} [NormedField k] [NormedField l] [NormedAlgebra k l]
  [NormedAddCommGroup V] [NormedSpace k V]

/-- A contractive scalar map contracts the actual projective extension on every vector. -/
theorem norm_scalarExtensionRetraction_le_projective
    (π : l →ₗ[k] k) (hπ : ∀ a, ‖π a‖ ≤ ‖a‖) (z : l ⊗[k] V) :
    ‖scalarExtensionRetraction π z‖ ≤ scalarExtensionProjectiveSeminorm z := by
  have hc (p : List (l × V)) :
      ‖scalarExtensionRetraction π ((p.map fun q => q.1 ⊗ₜ[k] q.2).sum)‖ ≤
        (p.map fun q => ‖q.1‖ * ‖q.2‖).sum := by
    induction p with
    | nil => simp
    | cons q p hp =>
      simp only [List.map_cons, List.sum_cons, map_add]
      apply (norm_add_le _ _).trans (add_le_add _ hp)
      rw [scalarExtensionRetraction_tmul, norm_smul]
      exact mul_le_mul_of_nonneg_right (hπ q.1) (norm_nonneg q.2)
  have hr : ∃ p : List (l × V), (p.map fun q => q.1 ⊗ₜ[k] q.2).sum = z := by
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨[], by simp⟩
    | tmul a x => exact ⟨[(a, x)], by simp⟩
    | add z t hz ht =>
      obtain ⟨p, hp⟩ := hz
      obtain ⟨q, hq⟩ := ht
      exact ⟨p ++ q, by simp only [List.map_append, List.sum_append, hp, hq]⟩
  rw [scalarExtensionProjectiveSeminorm_eq_sInf]
  obtain ⟨p, hp⟩ := hr
  apply le_csInf (show Set.Nonempty {d : ℝ | ∃ p : List (l × V),
    (p.map fun q => q.1 ⊗ₜ[k] q.2).sum = z ∧
      (p.map fun q => ‖q.1‖ * ‖q.2‖).sum = d} from
    ⟨(p.map fun q => ‖q.1‖ * ‖q.2‖).sum, p, hp, rfl⟩)
  rintro _ ⟨q, hq, rfl⟩
  simpa only [hq] using hc q

/-- Fixing one makes a contractive scalar retraction an isometry on rational vectors. -/
theorem scalarExtensionProjectiveSeminorm_one_tmul_of_retraction
    (π : l →ₗ[k] k) (hπ₁ : π 1 = 1) (hπ : ∀ a, ‖π a‖ ≤ ‖a‖) (x : V) :
    scalarExtensionProjectiveSeminorm ((1 : l) ⊗ₜ[k] x) = ‖x‖ := by
  apply le_antisymm (scalarExtensionProjectiveSeminorm_one_tmul_le x)
  simpa only [scalarExtensionRetraction_tmul, hπ₁, one_smul] using
    norm_scalarExtensionRetraction_le_projective π hπ ((1 : l) ⊗ₜ[k] x)

/-- Hahn–Banach supplies an actual contractive scalar retraction over a field
with its usual real or complex norm, even for an infinite-dimensional extension. -/
theorem exists_contractive_scalar_retraction_of_isRCLike [IsRCLikeNormedField k] :
    ∃ π : l →ₗ[k] k, π 1 = 1 ∧ ∀ a, ‖π a‖ ≤ ‖a‖ := by
  let := IsRCLikeNormedField.rclike k
  obtain ⟨π, hn, h₁⟩ := exists_dual_vector k (1 : l) (by simp)
  refine ⟨π.toLinearMap, ?_, fun a => ?_⟩
  · simpa only [ContinuousLinearMap.coe_coe, norm_one, RCLike.ofReal_one] using h₁
  · simpa only [ContinuousLinearMap.coe_coe, hn, one_mul] using π.le_opNorm a

/-- Projective extension preserves rational-vector norms over normalized
Archimedean fields without a finite-dimensionality assumption on the vector space. -/
theorem scalarExtensionProjectiveSeminorm_one_tmul_of_isRCLike
    [IsRCLikeNormedField k] (x : V) :
    scalarExtensionProjectiveSeminorm ((1 : l) ⊗ₜ[k] x) = ‖x‖ := by
  obtain ⟨π, h₁, hπ⟩ := exists_contractive_scalar_retraction_of_isRCLike (k := k) (l := l)
  exact scalarExtensionProjectiveSeminorm_one_tmul_of_retraction π h₁ hπ x

end ArakelovGeometry
