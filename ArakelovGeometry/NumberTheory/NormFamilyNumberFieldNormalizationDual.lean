/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.EquivalentCompletionDual
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldNormalizationDomination

/-!
# Actual duality and domination under number-field normalization

Compare the operator norms on the actual completed duals by transporting their
evaluation pairing and the genuine bounds defining those operator norms.
-/

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

open AdelicStructure

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The actual canonical tensor transports intertwine completed dual evaluation. -/
theorem normalizedNormFamilyTensorEquiv_dualPairing
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (z : (placeRep ω.val).Completion ⊗[K] Module.Dual K E)
    (y : (placeRep ω.val).Completion ⊗[K] E) :
    dualBaseChangeEquiv K (normalizedPlaceValue ω).Completion E
        (normalizedNormFamilyTensorEquiv ω z) (normalizedNormFamilyTensorEquiv ω y) =
      AbsoluteValue.completionAlgEquivOfIsEquiv _ _
        (normalizedPlaceValue_isEquiv_placeRep ω).symm
        (dualBaseChangeEquiv K (placeRep ω.val).Completion E z y) :=
  AbsoluteValue.completionScalarExtensionEquiv_dualBaseChange_apply _ _
    (normalizedPlaceValue_isEquiv_placeRep ω).symm E z y

/-- The norm of every transported completed evaluation has the actual local power. -/
theorem normalizedNormFamilyTensorEquiv_dualPairing_norm
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (z : (placeRep ω.val).Completion ⊗[K] Module.Dual K E)
    (y : (placeRep ω.val).Completion ⊗[K] E) :
    ‖dualBaseChangeEquiv K (normalizedPlaceValue ω).Completion E
        (normalizedNormFamilyTensorEquiv ω z) (normalizedNormFamilyTensorEquiv ω y)‖ =
      ‖dualBaseChangeEquiv K (placeRep ω.val).Completion E z y‖ ^
        numberFieldNormalizationExponent ω := by
  rw [normalizedNormFamilyTensorEquiv_dualPairing]
  apply AbsoluteValue.norm_completionAlgEquivOfIsEquiv _ _
    (normalizedPlaceValue_isEquiv_placeRep ω).symm
    (numberFieldNormalizationExponent ω) (numberFieldNormalizationExponent_pos ω)
  intro a
  by_cases hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin
  · erw [numberFieldNormalizationExponent_of_fin ω hω]
    exact normalizedPlace_value_rpow_of_mem_fin ω hω a
  · erw [numberFieldNormalizationExponent_of_inf ω hω, Real.rpow_one]
    exact normalizedPlace_value_eq_of_not_mem_fin ω hω a

namespace NormFamily

variable (ξ : NormFamily (numberFieldAdelicStructure K) E) (hξ : ξ.IsUltrametric)

omit [FiniteDimensional K E] in
/-- The actual finite and infinite completed norm formulas in one positive exponent. -/
theorem numberFieldNormalize_norm_map
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (y : (placeRep ω.val).Completion ⊗[K] E) :
    (ξ.numberFieldNormalize hξ).norm ω (normalizedNormFamilyTensorEquiv ω y) =
      ξ.norm ω.val y ^ numberFieldNormalizationExponent ω := by
  by_cases hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin
  · erw [numberFieldNormalizationExponent_of_fin ω hω]
    exact ξ.numberFieldNormalize_norm_map_fin hξ ω hω y
  · erw [numberFieldNormalizationExponent_of_inf ω hω, Real.rpow_one]
    exact ξ.numberFieldNormalize_norm_map_inf hξ ω hω y

/-- Dual operator norms transport by the same positive local power as the original norms. -/
theorem numberFieldNormalize_dual_norm_map
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (z : (placeRep ω.val).Completion ⊗[K] Module.Dual K E) :
    (ξ.numberFieldNormalize hξ).dual.norm ω (normalizedNormFamilyTensorEquiv ω z) =
      ξ.dual.norm ω.val z ^ numberFieldNormalizationExponent ω := by
  let θ := numberFieldNormalizationExponent ω
  have hθ : 0 < θ := numberFieldNormalizationExponent_pos ω
  have hcancel {r : ℝ} (hr : 0 ≤ r) : (r ^ θ⁻¹) ^ θ = r := by
    rw [← Real.rpow_mul hr, inv_mul_cancel₀ hθ.ne', Real.rpow_one]
  apply le_antisymm
  · apply (ξ.numberFieldNormalize hξ).dual_norm_le ω _
      (Real.rpow_nonneg (ξ.dual.norm_nonneg ω.val z) θ)
    intro y
    obtain ⟨x, rfl⟩ := (normalizedNormFamilyTensorEquiv ω).surjective y
    erw [normalizedNormFamilyTensorEquiv_dualPairing_norm,
      numberFieldNormalize_norm_map]
    exact (Real.rpow_le_rpow (_root_.norm_nonneg _)
      (ξ.norm_dual_apply_le ω.val z x) hθ.le).trans_eq
      (Real.mul_rpow (ξ.dual.norm_nonneg ω.val z) (ξ.norm_nonneg ω.val x))
  · have hB := (ξ.numberFieldNormalize hξ).dual.norm_nonneg ω
      (normalizedNormFamilyTensorEquiv ω z)
    have hbound : ξ.dual.norm ω.val z ≤
        (ξ.numberFieldNormalize hξ).dual.norm ω
          (normalizedNormFamilyTensorEquiv ω z) ^ θ⁻¹ := by
      apply ξ.dual_norm_le ω.val z (Real.rpow_nonneg hB θ⁻¹)
      intro y
      have hb := (ξ.numberFieldNormalize hξ).norm_dual_apply_le ω
        (normalizedNormFamilyTensorEquiv ω z) (normalizedNormFamilyTensorEquiv ω y)
      erw [normalizedNormFamilyTensorEquiv_dualPairing_norm,
        numberFieldNormalize_norm_map] at hb
      apply (Real.rpow_le_rpow_iff (_root_.norm_nonneg _)
        (mul_nonneg (Real.rpow_nonneg hB θ⁻¹) (ξ.norm_nonneg ω.val y)) hθ).mp
      calc
        _ ≤ (ξ.numberFieldNormalize hξ).dual.norm ω
            (normalizedNormFamilyTensorEquiv ω z) * ξ.norm ω.val y ^ θ := hb
        _ = _ := by
          rw [Real.mul_rpow (Real.rpow_nonneg hB θ⁻¹) (ξ.norm_nonneg ω.val y),
            hcancel hB]
    exact (Real.rpow_le_rpow (ξ.dual.norm_nonneg ω.val z) hbound hθ.le).trans_eq
      (hcancel hB)

/-- Normalization commutes with the actual completed dual norm family. -/
theorem numberFieldNormalize_dual :
    (ξ.numberFieldNormalize hξ).dual = ξ.dual.numberFieldNormalize ξ.dual_isUltrametric := by
  ext ω z
  obtain ⟨y, rfl⟩ := (normalizedNormFamilyTensorEquiv ω).surjective z
  erw [numberFieldNormalize_dual_norm_map, numberFieldNormalize_norm_map]

/-- Upper envelopes for the original family and its actual dual transport together. -/
theorem IsDominated.numberFieldNormalize {ξ : NormFamily (numberFieldAdelicStructure K) E}
    (h : ξ.IsDominated) (hξ : ξ.IsUltrametric) :
    (ξ.numberFieldNormalize hξ).IsDominated := by
  refine ⟨h.1.numberFieldNormalize hξ, ?_⟩
  rw [ξ.numberFieldNormalize_dual hξ]
  exact h.2.numberFieldNormalize ξ.dual_isUltrametric

end NormFamily

end ArakelovGeometry
