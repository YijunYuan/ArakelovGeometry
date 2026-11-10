/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HermitianHNMeasure
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The distributional derivative of the actual Hermitian HN rank function

Compactly supported continuously differentiable test functions identify the
actual signed jump measure as the weak derivative of the actual rank function.
Integrability is proved before invoking the fundamental theorem of calculus.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S E)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hV : V.toNormFamily.IsHermitian hN)

private theorem rank_mul_eq_sum_indicator (g : ℝ → ℝ) :
    (fun t ↦ (Module.finrank K (V.hermitianHNFiltration hS hN hV t) : ℝ) * g t) =
      fun t ↦ ∑ j : Fin (Module.finrank K E),
        (Set.Iic (V.hermitianHNOrderedSlope hS hN hV j)).indicator g t := by
  classical
  funext t
  rw [V.hermitianHNFiltration_finrank_eq_sum_indicator hS hN hV, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Set.indicator_apply]
  split_ifs <;> simp

/-- The actual rank times a compactly supported test derivative is genuinely
Lebesgue integrable; the integral does not use a default value. -/
theorem integrable_hermitianHNFiltration_finrank_mul_deriv
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun t ↦
      (Module.finrank K (V.hermitianHNFiltration hS hN hV t) : ℝ) * deriv φ t) volume := by
  classical
  rw [V.rank_mul_eq_sum_indicator hS hN hV]
  have hd : Integrable (deriv φ) volume :=
    (hφ.continuous_deriv le_rfl).integrable_of_hasCompactSupport hc.deriv
  exact integrable_finsetSum Finset.univ (fun j _ ↦
    (integrable_indicator_iff measurableSet_Iic).mpr hd.integrableOn)

/-- Fundamental calculus evaluates the actual rank against every compactly
supported continuously differentiable test derivative. -/
theorem integral_hermitianHNFiltration_finrank_mul_deriv
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (∫ t : ℝ, (Module.finrank K (V.hermitianHNFiltration hS hN hV t) : ℝ) * deriv φ t) =
      ∑ j : Fin (Module.finrank K E), φ (V.hermitianHNOrderedSlope hS hN hV j) := by
  classical
  rw [V.rank_mul_eq_sum_indicator hS hN hV]
  have hd : Integrable (deriv φ) volume :=
    (hφ.continuous_deriv le_rfl).integrable_of_hasCompactSupport hc.deriv
  rw [integral_finsetSum Finset.univ (fun j _ ↦
    (integrable_indicator_iff measurableSet_Iic).mpr hd.integrableOn)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_indicator measurableSet_Iic]
  exact HasCompactSupport.integral_Iic_deriv_eq hφ hc _

/-- The actual canonical signed rank-jump measure is the distributional
derivative of the actual rank function, on all compactly supported C¹ tests. -/
theorem hermitianHNSignedJumpMeasure_weakDerivative
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    -(∫ t : ℝ, (Module.finrank K (V.hermitianHNFiltration hS hN hV t) : ℝ) * deriv φ t) =
      ∫ᵛ t, φ t ∂<•V.hermitianHNSignedJumpMeasure hS hN hV := by
  rw [V.integral_hermitianHNFiltration_finrank_mul_deriv hS hN hV φ hφ hc,
    V.integral_hermitianHNSignedJumpMeasure hS hN hV]

end

end ArakelovGeometry.AdelicVectorBundle
