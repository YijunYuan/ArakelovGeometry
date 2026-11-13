/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Countable
public import ArakelovGeometry.AdelicVectorBundle.Degree.Basic

import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Determinant.Basic
import ArakelovGeometry.AdelicVectorBundle.Determinant.Comparison
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Integrable exponential rescaling of actual adelic bundles

Measurability is required of the chosen pointwise representative. Domination
uses only its integrable class. All completed norms and determinant degrees
are the existing canonical ones.
-/

@[expose] public section

open MeasureTheory Filter
open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace NormFamily

omit [FiniteDimensional K E] in
/-- Exponential rescaling translates each nonzero rational log norm. -/
theorem logNorm_scale_exp (ξ : NormFamily S E) (φ : S.Ω → ℝ)
    (x : E) (hx : x ≠ 0) (ω : S.Ω) :
    (ξ.scale (fun ω ↦ Real.exp (φ ω)) (fun _ ↦ Real.exp_pos _)).logNorm x ω =
      φ ω + ξ.logNorm x ω := by
  simp only [logNorm, scale_norm,
    Real.log_mul (Real.exp_ne_zero _) (ξ.norm_rational_pos ω hx).ne', Real.log_exp]

omit [FiniteDimensional K E] in
/-- Integrability of the exponent preserves upper domination without any
new measurability premise on the norm family or exponent. -/
theorem IsUpperDominated.scale_exp {ξ : NormFamily S E} (hξ : ξ.IsUpperDominated)
    {φ : S.Ω → ℝ} (hφ : Integrable φ S.v) :
    (ξ.scale (fun ω ↦ Real.exp (φ ω)) (fun _ ↦ Real.exp_pos _)).IsUpperDominated := by
  constructor
  intro x hx
  have h := (integrable_hasIntegrableBounds hφ).1.add (hξ x hx)
  apply h.congr
  exact Eventually.of_forall fun ω ↦ (ξ.logNorm_scale_exp φ x hx ω).symm

/-- Actual dual rescaling by the inverse exponential supplies the second
domination field rather than assuming it of the target. -/
theorem IsDominated.scale_exp {ξ : NormFamily S E} (hξ : ξ.IsDominated)
    {φ : S.Ω → ℝ} (hφ : Integrable φ S.v) :
    (ξ.scale (fun ω ↦ Real.exp (φ ω)) (fun _ ↦ Real.exp_pos _)).IsDominated := by
  refine ⟨hξ.1.scale_exp hφ, ?_⟩
  rw [scale_dual]
  simpa only [Pi.neg_apply, Real.exp_neg] using hξ.2.scale_exp hφ.neg

/-- The actual determinant log norm translates by rank times the exponent,
including rank zero and its scalar determinant unit. -/
theorem determinant_logNorm_scale_exp (ξ : NormFamily S E) (φ : S.Ω → ℝ)
    (z : ⋀[K]^(Module.finrank K E) E) (hz : z ≠ 0) (ω : S.Ω) :
    (ξ.scale (fun ω ↦ Real.exp (φ ω)) (fun _ ↦ Real.exp_pos _)).determinant.logNorm z ω =
      (Module.finrank K E : ℝ) * φ ω + ξ.determinant.logNorm z ω := by
  change Real.log (_ : ℝ) = _
  rw [determinant_scale_norm, Real.log_mul
    (pow_ne_zero _ (Real.exp_ne_zero _)) (ξ.determinant.norm_rational_pos ω hz).ne',
    Real.log_pow, Real.log_exp]
  rfl

end NormFamily

namespace AdelicVectorBundle

/-- The actual adelic bundle with completed norms multiplied by `exp φ`.
All analytic fields are produced from a measurable integrable representative. -/
abbrev scaleExp (V : AdelicVectorBundle S) (φ : S.Ω → ℝ)
    (hm : Measurable φ) (hi : Integrable φ S.v) : AdelicVectorBundle S where
  carrier := V
  toNormFamily := V.toNormFamily.scale (fun ω ↦ Real.exp (φ ω)) (fun _ ↦ Real.exp_pos _)
  toIsAdelic := {
    isMeasurable := V.isMeasurable.scale _ _ hm.exp
    dual_isMeasurable := by
      rw [NormFamily.scale_dual]
      exact V.dual_isMeasurable.scale _ _ hm.exp.inv
    isDominated := V.isDominated.scale_exp hi
  }

@[simp]
theorem scaleExp_toNormFamily (V : AdelicVectorBundle S) (φ : S.Ω → ℝ)
    (hm : Measurable φ) (hi : Integrable φ S.v) :
    (V.scaleExp φ hm hi).toNormFamily =
      V.toNormFamily.scale (fun ω ↦ Real.exp (φ ω)) (fun _ ↦ Real.exp_pos _) := rfl

/-- Integrating the exact actual determinant rescaling gives its degree shift. -/
theorem degree_scaleExp [S.IsProper] (V : AdelicVectorBundle.{w} S) (φ : S.Ω → ℝ)
    (hm : Measurable φ) (hi : Integrable φ S.v)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (V.scaleExp φ hm hi).degree = V.degree -
      (Module.finrank K V : ℝ) * (∫ ω, φ ω ∂S.v) := by
  let z := determinantGenerator (K := K) (E := V)
  have hz : z ≠ 0 := determinantGenerator_ne_zero
  have hlog : (V.scaleExp φ hm hi).toNormFamily.determinant.logNorm z =
      (fun ω ↦ (Module.finrank K V : ℝ) * φ ω) + V.toNormFamily.determinant.logNorm z := by
    funext ω
    exact V.toNormFamily.determinant_logNorm_scale_exp φ z hz ω
  have hbase : Integrable (V.toNormFamily.determinant.logNorm z) S.v :=
    (V.determinantOfMeasurableBase).integrable_logNorm z
  rw [(V.scaleExp φ hm hi).degree_eq_neg_integral ⟨z, hz⟩,
    V.degree_eq_neg_integral ⟨z, hz⟩, hlog]
  simp only [Pi.add_apply]
  rw [integral_add (hi.const_mul (Module.finrank K V : ℝ)) hbase, integral_const_mul]
  ring

/-- Restriction and actual exponential rescaling commute as adelic bundles.
The structure equality follows from equality of their canonical norm families. -/
theorem restrict_scaleExp (V : AdelicVectorBundle S) (φ : S.Ω → ℝ)
    (hm : Measurable φ) (hi : Integrable φ S.v)
    [hS : S.HasMeasurableBase]
    (U : Submodule K V) :
    (V.scaleExp φ hm hi).restrictOfMeasurableBase U =
      (V.restrictOfMeasurableBase U).scaleExp φ hm hi := by
  apply AdelicVectorBundle.ext
    (hξ := ((V.scaleExp φ hm hi).restrictOfMeasurableBase U).toIsAdelic)
    (hη := ((V.restrictOfMeasurableBase U).scaleExp φ hm hi).toIsAdelic)
  ext ω z
  rfl

/-- Every actual restricted degree has its own exact rank shift. -/
theorem degree_restrict_scaleExp [S.IsProper] (V : AdelicVectorBundle S)
    (φ : S.Ω → ℝ) (hm : Measurable φ) (hi : Integrable φ S.v)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (U : Submodule K V) :
    ((V.scaleExp φ hm hi).restrictOfMeasurableBase U).degree =
      (V.restrictOfMeasurableBase U).degree -
        (Module.finrank K U : ℝ) * (∫ ω, φ ω ∂S.v) := by
  rw [V.restrict_scaleExp φ hm hi U]
  exact degree_scaleExp _ φ hm hi

end AdelicVectorBundle

end

end ArakelovGeometry
