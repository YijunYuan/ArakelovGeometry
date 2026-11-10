/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Complex.OperatorNorm
public import Mathlib.Analysis.Normed.Module.RCLike.Extend

/-!
# The actual complex trace factor on continuous duals

Real-part extension is Mathlib's canonical dual isometry. The trace map
on the same original normed space is twice its inverse; its exact norm
factor is needed before transporting weighted Archimedean trace metrics.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.ComplexTraceDual

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]

/-- The actual local complex trace dual map, with the original domain norm. -/
def traceEquiv : StrongDual ℂ V ≃ₗ[ℝ] StrongDual ℝ V :=
  (StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ) (F := V)).symm.toLinearEquiv.trans
    (LinearEquiv.smulOfNeZero ℝ (StrongDual ℝ V) (2 : ℝ) (by norm_num))

@[simp]
theorem traceEquiv_apply (f : StrongDual ℂ V) (x : V) :
    traceEquiv f x = 2 * (f x).re := rfl

@[simp]
theorem traceEquiv_norm (f : StrongDual ℂ V) : ‖traceEquiv f‖ = 2 * ‖f‖ := by
  change ‖(2 : ℝ) • (StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ) (F := V)).symm f‖ = _
  rw [norm_smul, LinearIsometryEquiv.norm_map]
  norm_num

@[simp]
theorem traceEquiv_symm_apply (ℓ : StrongDual ℝ V) (x : V) :
    traceEquiv.symm ℓ x = ((ℓ x : ℂ) - Complex.I * (ℓ (Complex.I • x) : ℂ)) / 2 := by
  change StrongDual.extendRCLike ((2 : ℝ)⁻¹ • ℓ) x = _
  rw [StrongDual.extendRCLike_apply]
  change (((2 : ℝ)⁻¹ * ℓ x : ℝ) : ℂ) -
    Complex.I * (((2 : ℝ)⁻¹ * ℓ (Complex.I • x) : ℝ) : ℂ) = _
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_ofNat]
  ring

@[simp]
theorem traceEquiv_symm_norm (ℓ : StrongDual ℝ V) :
    ‖traceEquiv.symm ℓ‖ = (1 / 2 : ℝ) * ‖ℓ‖ := by
  have h := traceEquiv_norm (traceEquiv.symm ℓ)
  rw [LinearEquiv.apply_symm_apply] at h
  linarith

end ArakelovGeometry.ComplexTraceDual
