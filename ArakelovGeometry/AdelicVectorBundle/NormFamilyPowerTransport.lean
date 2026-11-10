/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.EquivalentCompletion
import ArakelovGeometry.AdelicVectorBundle.NormFamily

/-!
# Positive-power norms on actual completed scalar extensions

Use the canonical K-algebra equivalence of equivalent completed fields on the
left tensor factor. Ultrametricity permits every positive power, and the actual
completed scalar norm identity proves homogeneity over the new completed field.
-/

open scoped TensorProduct

noncomputable section

namespace AbsoluteValue

variable {K : Type*} [Field K] (v w : AbsoluteValue K ℝ) (h : v.IsEquiv w)
variable (E : Type*) [AddCommGroup E] [Module K E]

/-- The actual completed tensor fibres are canonically equivalent over the original field. -/
def completionScalarExtensionEquiv :
    (v.Completion ⊗[K] E) ≃ₗ[K] (w.Completion ⊗[K] E) :=
  TensorProduct.congr (completionAlgEquivOfIsEquiv v w h).toLinearEquiv (LinearEquiv.refl K E)

/-- The canonical tensor map applies the actual completed algebra map to its scalar factor. -/
theorem completionScalarExtensionEquiv_tmul (a : v.Completion) (x : E) :
    completionScalarExtensionEquiv v w h E (a ⊗ₜ[K] x) =
      completionAlgEquivOfIsEquiv v w h a ⊗ₜ[K] x :=
  TensorProduct.congr_tmul _ _ _ _

/-- Every actual completed scalar obeys the transported scalar action. -/
theorem completionScalarExtensionEquiv_smul (a : v.Completion)
    (z : v.Completion ⊗[K] E) :
    completionScalarExtensionEquiv v w h E (a • z) =
      completionAlgEquivOfIsEquiv v w h a • completionScalarExtensionEquiv v w h E z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
    simp only [TensorProduct.smul_tmul', completionScalarExtensionEquiv_tmul,
      smul_eq_mul, map_mul]
  | add z z' hz hz' => simp only [smul_add, map_add, hz, hz']

/-- The inverse tensor map transports every scalar through the inverse field-algebra map. -/
theorem completionScalarExtensionEquiv_symm_smul (a : w.Completion)
    (z : w.Completion ⊗[K] E) :
    (completionScalarExtensionEquiv v w h E).symm (a • z) =
      (completionAlgEquivOfIsEquiv v w h).symm a •
        (completionScalarExtensionEquiv v w h E).symm z := by
  apply (completionScalarExtensionEquiv v w h E).injective
  rw [(completionScalarExtensionEquiv v w h E).apply_symm_apply,
    completionScalarExtensionEquiv_smul,
    (completionAlgEquivOfIsEquiv v w h).apply_symm_apply,
    (completionScalarExtensionEquiv v w h E).apply_symm_apply]

variable (θ : ℝ) (hθ : 0 < θ) (hpow : ∀ a : K, w a = (v a) ^ θ)
variable (p : Seminorm v.Completion (v.Completion ⊗[K] E))
variable (hp : ∀ x y, p (x + y) ≤ max (p x) (p y))

/-- A genuine ultrametric completed seminorm transports as a positive power. -/
def powerTransportSeminorm : Seminorm w.Completion (w.Completion ⊗[K] E) where
  toFun y := p ((completionScalarExtensionEquiv v w h E).symm y) ^ θ
  map_zero' := by rw [map_zero, map_zero, Real.zero_rpow hθ.ne']
  neg' y := by rw [map_neg, map_neg_eq_map]
  add_le' y z := by
    rw [map_add]
    calc
      p ((completionScalarExtensionEquiv v w h E).symm y +
          (completionScalarExtensionEquiv v w h E).symm z) ^ θ ≤
          max (p ((completionScalarExtensionEquiv v w h E).symm y))
            (p ((completionScalarExtensionEquiv v w h E).symm z)) ^ θ :=
        Real.rpow_le_rpow (apply_nonneg _ _) (hp _ _) hθ.le
      _ = max (p ((completionScalarExtensionEquiv v w h E).symm y) ^ θ)
          (p ((completionScalarExtensionEquiv v w h E).symm z) ^ θ) :=
        Real.rpow_max (apply_nonneg _ _) (apply_nonneg _ _) hθ.le
      _ ≤ _ := max_le_iff.mpr
        ⟨le_add_of_nonneg_right (Real.rpow_nonneg (apply_nonneg _ _) θ),
          le_add_of_nonneg_left (Real.rpow_nonneg (apply_nonneg _ _) θ)⟩
  smul' a y := by
    rw [completionScalarExtensionEquiv_symm_smul, map_smul_eq_mul,
      Real.mul_rpow (norm_nonneg _) (apply_nonneg _ _),
      norm_completionAlgEquivOfIsEquiv_symm_rpow v w h θ hθ hpow]

/-- The actual powered seminorm has its defining value on every new completed tensor. -/
theorem powerTransportSeminorm_apply (y : w.Completion ⊗[K] E) :
    powerTransportSeminorm v w h E θ hθ hpow p hp y =
      p ((completionScalarExtensionEquiv v w h E).symm y) ^ θ := rfl

/-- It gives the original norm power on every transported completed tensor. -/
theorem powerTransportSeminorm_map (z : v.Completion ⊗[K] E) :
    powerTransportSeminorm v w h E θ hθ hpow p hp
      (completionScalarExtensionEquiv v w h E z) = p z ^ θ := by
  rw [powerTransportSeminorm_apply,
    (completionScalarExtensionEquiv v w h E).symm_apply_apply]

/-- The actual transported completed seminorm remains ultrametric. -/
theorem powerTransportSeminorm_isUltrametric (y z : w.Completion ⊗[K] E) :
    powerTransportSeminorm v w h E θ hθ hpow p hp (y + z) ≤
      max (powerTransportSeminorm v w h E θ hθ hpow p hp y)
        (powerTransportSeminorm v w h E θ hθ hpow p hp z) := by
  simp only [powerTransportSeminorm_apply, map_add]
  rw [← Real.rpow_max (apply_nonneg _ _) (apply_nonneg _ _) hθ.le]
  exact Real.rpow_le_rpow (apply_nonneg _ _) (hp _ _) hθ.le

/-- Separation is preserved on every actual completed fibre, including dimension zero. -/
theorem powerTransportSeminorm_eq_zero_iff
    (hsep : ∀ z, p z = 0 ↔ z = 0) (y : w.Completion ⊗[K] E) :
    powerTransportSeminorm v w h E θ hθ hpow p hp y = 0 ↔ y = 0 := by
  rw [powerTransportSeminorm_apply, Real.rpow_eq_zero (apply_nonneg _ _) hθ.ne', hsep]
  exact (completionScalarExtensionEquiv v w h E).symm.map_eq_zero_iff

/-- The true completed pure-tensor norms obey the same positive-power identity. -/
theorem powerTransportSeminorm_tmul (a : v.Completion) (x : E) :
    powerTransportSeminorm v w h E θ hθ hpow p hp
      (completionAlgEquivOfIsEquiv v w h a ⊗ₜ[K] x) = p (a ⊗ₜ[K] x) ^ θ := by
  rw [← completionScalarExtensionEquiv_tmul, powerTransportSeminorm_map]

variable (hvalue : ∀ a : K, w a = v a)

/-- Exact equality on original values transports every completed seminorm without a power. -/
def sameValueTransportSeminorm : Seminorm w.Completion (w.Completion ⊗[K] E) where
  toFun y := p ((completionScalarExtensionEquiv v w h E).symm y)
  map_zero' := by rw [map_zero, map_zero]
  neg' y := by rw [map_neg, map_neg_eq_map]
  add_le' y z := by
    rw [map_add]
    exact map_add_le_add _ _ _
  smul' a y := by
    have hn : ‖(completionAlgEquivOfIsEquiv v w h).symm a‖ = ‖a‖ := by
      simpa only [Real.rpow_one] using
        (norm_completionAlgEquivOfIsEquiv_symm_rpow v w h 1 zero_lt_one
          (fun c => (hvalue c).trans (Real.rpow_one (v c)).symm) a)
    rw [completionScalarExtensionEquiv_symm_smul, map_smul_eq_mul, hn]

/-- The actual unchanged-value seminorm is given on every transported tensor. -/
theorem sameValueTransportSeminorm_map (z : v.Completion ⊗[K] E) :
    sameValueTransportSeminorm v w h E p hvalue
      (completionScalarExtensionEquiv v w h E z) = p z := by
  change p ((completionScalarExtensionEquiv v w h E).symm
    (completionScalarExtensionEquiv v w h E z)) = p z
  rw [(completionScalarExtensionEquiv v w h E).symm_apply_apply]

/-- Exact original-value transport preserves separation of the genuine completed norm. -/
theorem sameValueTransportSeminorm_eq_zero_iff
    (hsep : ∀ z, p z = 0 ↔ z = 0) (y : w.Completion ⊗[K] E) :
    sameValueTransportSeminorm v w h E p hvalue y = 0 ↔ y = 0 := by
  change p ((completionScalarExtensionEquiv v w h E).symm y) = 0 ↔ y = 0
  rw [hsep]
  exact (completionScalarExtensionEquiv v w h E).symm.map_eq_zero_iff

end AbsoluteValue
