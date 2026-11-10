/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Defs

/-!
# Adelic divisors and their degree

The divisor space in Chen–Moriwaki, Section 4.2, is exactly the real `L¹`
space of the adelic measure, with its existing Banach structure.
-/

open MeasureTheory Filter

namespace ArakelovGeometry

universe u v

variable {K : Type u} [Field K]

/-- The actual real `L¹` space of adelic divisors, modulo equality almost everywhere. -/
abbrev AdelicDivisor (S : AdelicStructure.{u, v} K) := Lp ℝ 1 S.v

namespace AdelicDivisor

variable (S : AdelicStructure.{u, v} K)

/-- Completeness uses the canonical `L¹` structure and requires no finiteness
or sigma-finiteness assumption on the adelic measure. -/
theorem completeSpace : CompleteSpace (AdelicDivisor S) := inferInstance

/-- An integrable function gives its actual almost-everywhere equivalence class. -/
noncomputable abbrev ofIntegrable (f : S.Ω → ℝ) (hf : Integrable f S.v) :
    AdelicDivisor S := hf.toL1 f

/-- The norm of a divisor is the integral of the absolute value of its representative. -/
theorem norm_eq_integral_abs (ζ : AdelicDivisor S) :
    ‖ζ‖ = ∫ ω, |ζ ω| ∂S.v := by
  simpa only [Real.norm_eq_abs] using L1.norm_eq_integral_norm ζ

/-- Equation (4.18), bundled as its continuous real-linear form. -/
noncomputable def degree : AdelicDivisor S →L[ℝ] ℝ := L1.integralCLM

/-- Degree is integration of the canonical representative, hence of any
almost-everywhere equal representative. -/
theorem degree_eq_integral (ζ : AdelicDivisor S) :
    degree S ζ = ∫ ω, ζ ω ∂S.v :=
  (L1.integral_eq ζ).symm.trans (L1.integral_eq_integral ζ)

/-- The degree formula on an integrable representative. -/
@[simp]
theorem degree_ofIntegrable (f : S.Ω → ℝ) (hf : Integrable f S.v) :
    degree S (ofIntegrable S f hf) = ∫ ω, f ω ∂S.v := by
  rw [degree_eq_integral]
  exact integral_congr_ae hf.coeFn_toL1

/-- The degree form has operator norm at most one, including zero measure. -/
theorem norm_degree_le_one : ‖degree S‖ ≤ 1 := L1.norm_Integral_le_one

/-- The absolute value of degree is bounded by the divisor norm. -/
theorem abs_degree_le_norm (ζ : AdelicDivisor S) : |degree S ζ| ≤ ‖ζ‖ := by
  rw [← Real.norm_eq_abs]
  exact ((degree S).le_opNorm ζ).trans
    ((mul_le_mul_of_nonneg_right (norm_degree_le_one S) (norm_nonneg ζ)).trans_eq (one_mul _))

/-- Effectivity is almost-everywhere nonnegativity in the actual `L¹` space. -/
def IsEffective (ζ : AdelicDivisor S) : Prop := ∀ᵐ ω ∂S.v, 0 ≤ ζ ω

/-- Effectivity can be tested on any integrable representative. -/
theorem isEffective_ofIntegrable_iff (f : S.Ω → ℝ) (hf : Integrable f S.v) :
    IsEffective S (ofIntegrable S f hf) ↔ ∀ᵐ ω ∂S.v, 0 ≤ f ω := by
  constructor
  · intro h
    filter_upwards [h, hf.coeFn_toL1] with ω hω heq
    rwa [← heq]
  · intro h
    filter_upwards [h, hf.coeFn_toL1] with ω hω heq
    rwa [heq]

/-- The zero divisor is effective. -/
theorem isEffective_zero : IsEffective S 0 := by
  filter_upwards [Lp.coeFn_zero ℝ 1 S.v] with ω hω
  simp only [hω, Pi.zero_apply, le_refl]

/-- Effective divisors are closed under addition. -/
theorem IsEffective.add {ζ η : AdelicDivisor S}
    (hζ : IsEffective S ζ) (hη : IsEffective S η) : IsEffective S (ζ + η) := by
  filter_upwards [hζ, hη, Lp.coeFn_add ζ η] with ω hζω hηω heq
  rw [heq]
  exact add_nonneg hζω hηω

/-- Effective divisors are closed under multiplication by a nonnegative real scalar. -/
theorem IsEffective.smul {ζ : AdelicDivisor S} (hζ : IsEffective S ζ)
    {a : ℝ} (ha : 0 ≤ a) : IsEffective S (a • ζ) := by
  filter_upwards [hζ, Lp.coeFn_smul a ζ] with ω hζω heq
  rw [heq]
  exact mul_nonneg ha hζω

/-- Every effective divisor has nonnegative degree. -/
theorem IsEffective.degree_nonneg {ζ : AdelicDivisor S} (hζ : IsEffective S ζ) :
    0 ≤ degree S ζ := by
  rw [degree_eq_integral]
  exact integral_nonneg_of_ae hζ

/-- On the zero measure the degree form is zero. -/
theorem degree_eq_zero_of_measure_eq_zero (hS : S.v = 0) : degree S = 0 := by
  ext ζ
  simp [degree_eq_integral, hS]

end AdelicDivisor
end ArakelovGeometry
