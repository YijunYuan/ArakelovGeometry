/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.TensorPairNorm
import ArakelovGeometry.AdelicVectorBundle.DeterminantWedgeApproximation
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Actual determinant tensor norm comparison

Scalar-weighted wedge approximation retains the degree-zero determinant line.
The projective bound is an inequality, as required by the corrected source
tensor-degree statement.
-/

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E F : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- The completed determinant tensor map contracts scalar-weighted wedges.
The scalar powers retain the tensor unit when a rank is zero. -/
theorem projectiveTensorPair_determinant_norm_smul_wedge_le
    (ξ : NormFamily S E) (η : NormFamily S F) (ω : S.Ω)
    (a b : (S.ϕ ω).Completion)
    (x : Fin (Module.finrank K E) → (S.ϕ ω).Completion ⊗[K] E)
    (y : Fin (Module.finrank K F) → (S.ϕ ω).Completion ⊗[K] F) :
    (ξ.projectiveTensorPair η).determinant.norm ω
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion (E ⊗[K] F)
        (Module.finrank K (E ⊗[K] F))).symm
        (determinantTensorEquivCompleted K (S.ϕ ω).Completion E F
          ((⨂ₜ[(S.ϕ ω).Completion] (_ : Fin (Module.finrank K F)),
            a • exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K E) x)
            ⊗ₜ[(S.ϕ ω).Completion]
            (⨂ₜ[(S.ϕ ω).Completion] (_ : Fin (Module.finrank K E)),
              b • exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K F) y)))) ≤
      (‖a‖ * ∏ i, ξ.norm ω (x i)) ^ Module.finrank K F *
        (‖b‖ * ∏ j, η.norm ω (y j)) ^ Module.finrank K E := by
  simp only [MultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, TensorProduct.smul_tmul_smul, map_smul,
    norm_smul, norm_mul, norm_pow]
  calc
    _ ≤ (‖a‖ ^ Module.finrank K F * ‖b‖ ^ Module.finrank K E) *
        ((∏ i, ξ.norm ω (x i)) ^ Module.finrank K F *
          (∏ j, η.norm ω (y j)) ^ Module.finrank K E) :=
      mul_le_mul_of_nonneg_left (ξ.projectiveTensorPair_determinant_norm_wedge_le η ω x y)
        (mul_nonneg (pow_nonneg (_root_.norm_nonneg a) _) (pow_nonneg (_root_.norm_nonneg b) _))
    _ = _ := by
      simp only [mul_pow]
      ring

/-- Actual completed projective determinant norm comparison in every rank. -/
theorem projectiveTensorPair_determinant_norm_le
    (ξ : NormFamily S E) (η : NormFamily S F) (ω : S.Ω)
    (z : ⋀[(S.ϕ ω).Completion]^(Module.finrank K E) ((S.ϕ ω).Completion ⊗[K] E))
    (t : ⋀[(S.ϕ ω).Completion]^(Module.finrank K F) ((S.ϕ ω).Completion ⊗[K] F)) :
    (ξ.projectiveTensorPair η).determinant.norm ω
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion (E ⊗[K] F)
        (Module.finrank K (E ⊗[K] F))).symm
        (determinantTensorEquivCompleted K (S.ϕ ω).Completion E F
          ((⨂ₜ[(S.ϕ ω).Completion] (_ : Fin (Module.finrank K F)), z) ⊗ₜ[(S.ϕ ω).Completion]
            (⨂ₜ[(S.ϕ ω).Completion] (_ : Fin (Module.finrank K E)), t)))) ≤
      ξ.determinant.norm ω
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm z) ^
          Module.finrank K F *
      η.determinant.norm ω
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion F (Module.finrank K F)).symm t) ^
          Module.finrank K E := by
  let C := ξ.determinant.norm ω
    ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm z)
  let D := η.determinant.norm ω
    ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion F (Module.finrank K F)).symm t)
  let q : (⋀[(S.ϕ ω).Completion]^(Module.finrank K E)
      ((S.ϕ ω).Completion ⊗[K] E)) →
      (⋀[(S.ϕ ω).Completion]^(Module.finrank K F)
        ((S.ϕ ω).Completion ⊗[K] F)) → ℝ := fun z t ↦
    (ξ.projectiveTensorPair η).determinant.norm ω
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion (E ⊗[K] F)
        (Module.finrank K (E ⊗[K] F))).symm
        (determinantTensorEquivCompleted K (S.ϕ ω).Completion E F
          ((⨂ₜ[(S.ϕ ω).Completion] (_ : Fin (Module.finrank K F)), z) ⊗ₜ[(S.ϕ ω).Completion]
            (⨂ₜ[(S.ϕ ω).Completion] (_ : Fin (Module.finrank K E)), t))))
  change q z t ≤ C ^ Module.finrank K F * D ^ Module.finrank K E
  have hε (ε : ℝ) (hε : 0 < ε) :
      q z t ≤ (C + ε) ^ Module.finrank K F * (D + ε) ^ Module.finrank K E := by
    obtain ⟨a, x, hx, hcx⟩ := ξ.exists_smul_determinant_ιMulti_norm_lt ω
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm z) hε
    obtain ⟨b, y, hy, hdy⟩ := η.exists_smul_determinant_ιMulti_norm_lt ω
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion F (Module.finrank K F)).symm t) hε
    have hz : z = a • exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K E) x := by
      have he := congrArg (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E
        (Module.finrank K E)) hx
      simpa only [map_smul, LinearEquiv.apply_symm_apply] using he.symm
    have ht : t = b • exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K F) y := by
      have he := congrArg (exteriorBaseChangeEquiv K (S.ϕ ω).Completion F
        (Module.finrank K F)) hy
      simpa only [map_smul, LinearEquiv.apply_symm_apply] using he.symm
    rw [hz, ht]
    apply (ξ.projectiveTensorPair_determinant_norm_smul_wedge_le η ω a b x y).trans
    exact mul_le_mul
        (pow_le_pow_left₀ (mul_nonneg (_root_.norm_nonneg a)
          (Finset.prod_nonneg (fun i _ ↦ ξ.norm_nonneg ω (x i)))) hcx.le _)
        (pow_le_pow_left₀ (mul_nonneg (_root_.norm_nonneg b)
          (Finset.prod_nonneg (fun j _ ↦ η.norm_nonneg ω (y j)))) hdy.le _)
        (pow_nonneg (mul_nonneg (_root_.norm_nonneg b)
          (Finset.prod_nonneg (fun j _ ↦ η.norm_nonneg ω (y j)))) _)
        (pow_nonneg (add_nonneg (ξ.determinant.norm_nonneg ω _) hε.le) _)
  have hlim : Filter.Tendsto
      (fun n : ℕ ↦ (C + 1 / ((n : ℝ) + 1)) ^ Module.finrank K F *
        (D + 1 / ((n : ℝ) + 1)) ^ Module.finrank K E)
      Filter.atTop (nhds (C ^ Module.finrank K F * D ^ Module.finrank K E)) := by
    simpa only [add_zero] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add C).pow
        (Module.finrank K F) |>.mul
        (((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add D).pow
          (Module.finrank K E))
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun n ↦
    hε _ (one_div_pos.mpr (by positivity)))

/-- Actual completed mixed determinant norm comparison in every rank. -/
theorem mixedTensorPair_determinant_norm_le
    (ξ : NormFamily S E) (η : NormFamily S F) (ω : S.Ω)
    (z : ⋀[(S.ϕ ω).Completion]^(Module.finrank K E) ((S.ϕ ω).Completion ⊗[K] E))
    (t : ⋀[(S.ϕ ω).Completion]^(Module.finrank K F) ((S.ϕ ω).Completion ⊗[K] F)) :
    (ξ.mixedTensorPair η).determinant.norm ω
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion (E ⊗[K] F)
        (Module.finrank K (E ⊗[K] F))).symm
        (determinantTensorEquivCompleted K (S.ϕ ω).Completion E F
          ((⨂ₜ[(S.ϕ ω).Completion] (_ : Fin (Module.finrank K F)), z) ⊗ₜ[(S.ϕ ω).Completion]
            (⨂ₜ[(S.ϕ ω).Completion] (_ : Fin (Module.finrank K E)), t)))) ≤
      ξ.determinant.norm ω
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm z) ^
          Module.finrank K F *
      η.determinant.norm ω
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion F (Module.finrank K F)).symm t) ^
          Module.finrank K E :=
  (determinant_norm_mono _ _ ω
    (fun z ↦ ξ.mixedTensorPair_norm_le_projectiveTensorPair_norm η ω z) _).trans
      (ξ.projectiveTensorPair_determinant_norm_le η ω z t)

end

end ArakelovGeometry.NormFamily
