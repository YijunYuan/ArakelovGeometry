/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.ParameterSpace
public import ArakelovGeometry.Analysis.AbsoluteValue.Basic
import ArakelovGeometry.Analysis.AbsoluteValue.FiniteExtension
import ArakelovGeometry.Analysis.AbsoluteValue.LocalDegree
import Mathlib.CategoryTheory.Category.Init
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Integration over finite separable fibres

Local-degree probabilities and their fibre integrals, including linearity and
restriction compatibility (Chen–Moriwaki, §3.3.1).
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure.ParameterSpaceExtension

open MeasureTheory AbsoluteValue
open scoped ENNReal

universe u v w

variable {K : Type u} [Field K] (AS : AdelicStructure.{u, v} K)
variable (L : Type w) [Field L] [Algebra K L]

variable [FiniteDimensional K L] [_s : Algebra.IsSeparable K L]

/-- The concrete fibre weight `[L_x : K_ω] / [L : K]` from (3.2). -/
noncomputable def fibreWeight (ω : AS.Ω) (x : ExtensionFiber AS L ω) : ℝ≥0∞ :=
  (localDegree x.1.ϕ K : ℝ≥0∞) / (Module.finrank K L : ℝ≥0∞)

/-- The concrete fibre weights from (3.2) have total mass one. -/
theorem tsum_fibreWeight (ω : AS.Ω) :
    ∑' x : ExtensionFiber AS L ω, fibreWeight AS L ω x = 1 := by
  classical
  let E := {w : AbsoluteValue L ℝ // w.under K = AS.ϕ ω}
  let e : ExtensionFiber AS L ω ≃ E := {
    toFun x := ⟨x.val.ϕ, x.val.restrict_eq.trans (congrArg AS.ϕ x.property)⟩
    invFun w := ⟨⟨ω, w.val, w.property⟩, rfl⟩
    left_inv x := by
      apply Subtype.ext
      exact ParameterSpaceExtension.ext AS L x.property.symm rfl
    right_inv _ := rfl }
  let : Fintype E := (AbsoluteValue.finite_extensions (L := L) (AS.ϕ ω)).fintype
  let : Fintype (ExtensionFiber AS L ω) := Fintype.ofEquiv E e.symm
  rw [tsum_fintype]
  change (∑ x : ExtensionFiber AS L ω,
    (x.val.ϕ.localDegree K : ℝ≥0∞) / (Module.finrank K L : ℝ≥0∞)) = 1
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum]
  have hs : ∑ x : ExtensionFiber AS L ω, x.val.ϕ.localDegree K = Module.finrank K L :=
    (e.sum_comp (fun w ↦ w.val.localDegree K)).trans (AbsoluteValue.sum_localDegree (AS.ϕ ω))
  rw [hs, ← div_eq_mul_inv]
  exact ENNReal.div_self (by exact_mod_cast (ne_of_gt (Module.finrank_pos (R := K) (M := L))))
    (by simp)

/-- The finite fibre probability measure `P_{L,ω}` of (3.2), defined from its point masses. -/
noncomputable def fibreProbabilityMeasure (ω : AS.Ω) :
    Measure (ExtensionFiber AS L ω) :=
  Measure.sum fun x : ExtensionFiber AS L ω ↦ fibreWeight AS L ω x • Measure.dirac x

/-- The local-degree normalization makes every fibre measure a probability measure. -/
instance isProbabilityMeasure_fibreProbabilityMeasure (ω : AS.Ω) :
    IsProbabilityMeasure (fibreProbabilityMeasure AS L ω) where
  measure_univ := by
    simpa [fibreProbabilityMeasure, Measure.sum_apply] using tsum_fibreWeight AS L ω

/-- The fibre integration operator `I_{L/K}` on real-valued functions from §3.3.1. -/
noncomputable def fibreIntegral (f : ParameterSpaceExtension AS L → ℝ) : AS.Ω → ℝ :=
  fun ω ↦ ∫ x : ExtensionFiber AS L ω, f x.1 ∂fibreProbabilityMeasure AS L ω

/-- The nonnegative version of the fibre integration operator, used in Definition 3.3.6. -/
noncomputable def fibreLIntegral (f : ParameterSpaceExtension AS L → ℝ≥0∞) : AS.Ω → ℝ≥0∞ :=
  fun ω ↦ ∫⁻ x : ExtensionFiber AS L ω, f x.1 ∂fibreProbabilityMeasure AS L ω

omit _s in
/-- The fibres of the projection of a finite extension are finite sets (§3.3, p. 178: a base
absolute value has at most `[L : K]` extensions to `L`). -/
theorem finite_extensionFiber (ω : AS.Ω) : Finite (ExtensionFiber AS L ω) := by
  have : Finite {w : AbsoluteValue L ℝ // w.under K = AS.ϕ ω} :=
    Set.finite_coe_iff.mpr (AbsoluteValue.finite_extensions (L := L) (AS.ϕ ω))
  let f : ExtensionFiber AS L ω → {w : AbsoluteValue L ℝ // w.under K = AS.ϕ ω} :=
    fun x ↦ ⟨x.val.abv, x.val.restrict_eq.trans (congrArg AS.ϕ x.property)⟩
  apply Finite.of_injective f
  intro x y h
  apply Subtype.ext
  exact ext AS L (x.property.trans y.property.symm) (congrArg Subtype.val h)

/-- Formula (3.3): the fibre integration operator sends the constant function `1` on `Ω_L`
to the constant function `1` on `Ω_K` (§3.3.1). -/
theorem fibreIntegral_one : fibreIntegral AS L (fun _ ↦ 1) = fun _ ↦ 1 := by
  funext ω
  simp [fibreIntegral]

/-- Every real function on a finite fibre is integrable for its probability measure. -/
theorem integrable_fibre (ω : AS.Ω) (f : ExtensionFiber AS L ω → ℝ) :
    Integrable f (fibreProbabilityMeasure AS L ω) := by
  let := finite_extensionFiber AS L ω
  exact Integrable.of_finite

/-- Real fibre integration is the finite sum with its local-degree weights. -/
theorem fibreIntegral_eq_sum (f : ParameterSpaceExtension AS L → ℝ) (ω : AS.Ω)
    [Fintype (ExtensionFiber AS L ω)] :
    fibreIntegral AS L f ω =
      ∑ x : ExtensionFiber AS L ω, (fibreWeight AS L ω x).toReal * f x.val := by
  unfold fibreIntegral fibreProbabilityMeasure
  rw [integral_sum_measure (integrable_fibre AS L ω _), tsum_fintype]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]

omit [Algebra.IsSeparable K L] in
/-- Nonnegative fibre integration is the finite sum with its local-degree weights. -/
theorem fibreLIntegral_eq_sum (f : ParameterSpaceExtension AS L → ℝ≥0∞) (ω : AS.Ω)
    [Fintype (ExtensionFiber AS L ω)] :
    fibreLIntegral AS L f ω =
      ∑ x : ExtensionFiber AS L ω, fibreWeight AS L ω x * f x.val := by
  unfold fibreLIntegral fibreProbabilityMeasure
  rw [lintegral_sum_measure, tsum_fintype]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-- The fibre integration operator is additive (§3.3.1). -/
theorem fibreIntegral_add (f g : ParameterSpaceExtension AS L → ℝ) :
    fibreIntegral AS L (f + g) = fibreIntegral AS L f + fibreIntegral AS L g := by
  funext ω
  exact integral_add (integrable_fibre AS L ω _) (integrable_fibre AS L ω _)

set_option linter.unusedSectionVars false in
/-- The fibre integration operator is `ℝ`-homogeneous (§3.3.1). -/
theorem fibreIntegral_smul (c : ℝ) (f : ParameterSpaceExtension AS L → ℝ) :
    fibreIntegral AS L (c • f) = c • fibreIntegral AS L f := by
  funext ω
  exact integral_smul c _

set_option linter.unusedSectionVars false in
/-- Chen--Moriwaki, Proposition 3.3.1: fibre integration is linear over functions pulled back
from the base: `I_{K'/K}((φ ∘ π_{K'/K}) * f) = φ * I_{K'/K}(f)`. -/
theorem fibreIntegral_comp_proj_mul (φ : AS.Ω → ℝ) (f : ParameterSpaceExtension AS L → ℝ) :
    fibreIntegral AS L (fun x ↦ φ (proj x) * f x) = fun ω ↦ φ ω * fibreIntegral AS L f ω := by
  funext ω
  have hproj : ∀ x : ExtensionFiber AS L ω, x.val.proj = ω := fun x ↦ x.property
  change (∫ x : ExtensionFiber AS L ω, φ x.val.proj * f x.val
    ∂fibreProbabilityMeasure AS L ω) = _
  simp_rw [hproj]
  exact integral_const_mul (φ ω) _

/-- Chen--Moriwaki, Corollary 3.3.3: fibre integration retracts the pullback along the
projection: `I_{K'/K}(φ ∘ π_{K'/K}) = φ`. -/
theorem fibreIntegral_comp_proj (φ : AS.Ω → ℝ) :
    fibreIntegral AS L (fun x ↦ φ (proj x)) = φ := by
  funext ω
  change (∫ x : ExtensionFiber AS L ω, φ x.val.proj
    ∂fibreProbabilityMeasure AS L ω) = φ ω
  simp only [show ∀ x : ExtensionFiber AS L ω, x.val.proj = ω from fun x ↦ x.property]
  simp

/-- Chen--Moriwaki, Proposition 3.3.2, formula (3.4): fibre integration is compatible with
successive finite separable extensions `K ⊆ F ⊆ L`: integrating a function pulled back from
the intermediate stage agrees with integrating the function at the intermediate stage. -/
theorem fibreIntegral_comp_restrict (F : IntermediateField K L)
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (f : ParameterSpaceExtension AS F → ℝ) :
    fibreIntegral AS L (fun x ↦ f (restrict AS L x F)) = fibreIntegral AS F f := by
  classical
  funext ω
  let E := {w : AbsoluteValue L ℝ // w.under K = AS.ϕ ω}
  let D := {w : AbsoluteValue F ℝ // w.under K = AS.ϕ ω}
  let : Fintype E := (AbsoluteValue.finite_extensions (L := L) (AS.ϕ ω)).fintype
  let : Fintype D := (AbsoluteValue.finite_extensions (L := F) (AS.ϕ ω)).fintype
  let eL : ExtensionFiber AS L ω ≃ E := {
    toFun x := ⟨x.val.ϕ, x.val.restrict_eq.trans (congrArg AS.ϕ x.property)⟩
    invFun w := ⟨⟨ω, w.val, w.property⟩, rfl⟩
    left_inv x := by
      apply Subtype.ext
      exact ParameterSpaceExtension.ext AS L x.property.symm rfl
    right_inv _ := rfl }
  let eF : ExtensionFiber AS F ω ≃ D := {
    toFun x := ⟨x.val.ϕ, x.val.restrict_eq.trans (congrArg AS.ϕ x.property)⟩
    invFun w := ⟨⟨ω, w.val, w.property⟩, rfl⟩
    left_inv x := by
      apply Subtype.ext
      exact ParameterSpaceExtension.ext AS F x.property.symm rfl
    right_inv _ := rfl }
  let : Fintype (ExtensionFiber AS L ω) := Fintype.ofEquiv E eL.symm
  let : Fintype (ExtensionFiber AS F ω) := Fintype.ofEquiv D eF.symm
  let φ (w : D) : ℝ := f ⟨ω, w.val, w.property⟩
  have hs := AbsoluteValue.sum_localDegree_nsmul_restriction F (AS.ϕ ω) φ
  simp only [nsmul_eq_mul] at hs
  have hl :
      ∑ x : ExtensionFiber AS L ω, (x.val.ϕ.localDegree K : ℝ) * f (restrict AS L x.val F) =
        ∑ w : E, (w.val.localDegree K : ℝ) * φ ⟨w.val.under F, w.property⟩ := by
    rw [← eL.sum_comp (fun w ↦ (w.val.localDegree K : ℝ) *
      φ ⟨w.val.under F, w.property⟩)]
    apply Finset.sum_congr rfl
    intro x _
    apply congrArg ((x.val.ϕ.localDegree K : ℝ) * ·)
    apply congrArg f
    exact ParameterSpaceExtension.ext AS F x.property rfl
  have hr :
      ∑ x : ExtensionFiber AS F ω, (x.val.ϕ.localDegree K : ℝ) * f x.val =
        ∑ w : D, (w.val.localDegree K : ℝ) * φ w := by
    rw [← eF.sum_comp (fun w ↦ (w.val.localDegree K : ℝ) * φ w)]
    apply Finset.sum_congr rfl
    intro x _
    apply congrArg ((x.val.ϕ.localDegree K : ℝ) * ·)
    apply congrArg f
    exact ParameterSpaceExtension.ext AS F x.property rfl
  rw [fibreIntegral_eq_sum, fibreIntegral_eq_sum]
  simp only [fibreWeight, ENNReal.toReal_div, ENNReal.toReal_natCast,
    div_mul_eq_mul_div, ← Finset.sum_div]
  rw [hl, hr, hs]
  have hd : (Module.finrank K L : ℝ) =
      (Module.finrank K F : ℝ) * (Module.finrank F L : ℝ) := by
    exact_mod_cast (Module.finrank_mul_finrank K F L).symm
  rw [hd]
  have hn : (Module.finrank F L : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := F) (M := L)).ne'
  rw [mul_comm (Module.finrank K F : ℝ), mul_div_mul_left _ _ hn]

end ArakelovGeometry.AdelicStructure.ParameterSpaceExtension
