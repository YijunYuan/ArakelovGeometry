/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.RootBounds
public import ArakelovGeometry.AdelicCurve.Extension.Separable.Measure
public import Mathlib.RingTheory.Norm.Defs

/-!
# The finite separable scalar extension

Logarithmic integrability, the norm-integral formula and preservation of properness
construct the scalar extension (Chen–Moriwaki, Theorem 3.3.7(4–5)).
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure.ParameterSpaceExtension

open MeasureTheory AbsoluteValue
open scoped ENNReal

universe u v w

variable {K : Type u} [Field K] (AS : AdelicStructure.{u, v} K)
variable (L : Type w) [Field L] [Algebra K L]

variable [FiniteDimensional K L] [_s : Algebra.IsSeparable K L]

/-- Formula (3.10): the fibre integral of a logarithmic evaluation is the logarithm
of its field norm divided by the extension degree. -/
theorem fibreIntegral_log_eq_log_norm (b : L) (hb : b ≠ 0) (ω : AS.Ω) :
    fibreIntegral AS L (fun x ↦ Real.log (ϕ x b)) ω =
      Real.log (AS.ϕ ω (Algebra.norm K b)) / (Module.finrank K L : ℝ) := by
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
  rw [fibreIntegral_eq_sum]
  simp only [fibreWeight, ENNReal.toReal_div, ENNReal.toReal_natCast,
    div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  have hp : AS.ϕ ω (Algebra.norm K b) =
      ∏ x : ExtensionFiber AS L ω, x.val.ϕ b ^ x.val.ϕ.localDegree K :=
    (AbsoluteValue.apply_norm_eq_prod (AS.ϕ ω) b).trans
      (e.prod_comp (fun w ↦ w.val b ^ w.val.localDegree K)).symm
  rw [hp, Real.log_prod (fun x _ ↦ pow_ne_zero _ (x.val.ϕ.ne_zero hb))]
  simp only [Real.log_pow]

/-- Chen--Moriwaki, Theorem 3.3.7(4): logarithmic evaluations are integrable for the measure
defined in Definition 3.3.6. -/
theorem integrable_log_inducedMeasure (a : L) (ha : a ≠ 0) :
    Integrable
      (fun x : ParameterSpaceExtension AS L ↦ Real.log ((ParameterSpaceExtension.ϕ x) a))
      (inducedMeasure AS L) := by
  let p := minpoly K a
  have hp : p.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral a)
  let h : AS.Ω → ℝ := fun ω ↦
    Real.log (p.natDegree : ℝ) * AS.κ ω + AS.coefficientLogBound p ω
  have hm : Measurable h := AS.measurable_logarithmicRootBound p
  have hi : Integrable h AS.v := AS.integrable_logarithmicRootBound p
  let u : ParameterSpaceExtension AS L → ℝ := fun x ↦ h (proj x) - Real.log (ϕ x a)
  have um : Measurable u := (hm.comp (measurable_proj AS L)).sub (measurable_log AS L a)
  have un (x : ParameterSpaceExtension AS L) : 0 ≤ u x := by
    exact sub_nonneg.mpr (AS.log_apply_le_rootBound p hp a
      (minpoly.aeval K a) ha (proj x) (ϕ x) (ϕ_restriction AS L x))
  have uint : Integrable u (inducedMeasure AS L) := by
    apply (integrable_inducedMeasure_iff AS L um).mpr
    have heq : (fibreIntegral AS L fun x ↦ |u x|) =
        fun ω ↦ h ω -
          Real.log (AS.ϕ ω (Algebra.norm K a)) / (Module.finrank K L : ℝ) := by
      funext ω
      simp_rw [abs_of_nonneg (un _)]
      change (∫ x : ExtensionFiber AS L ω, u x.val
        ∂fibreProbabilityMeasure AS L ω) = _
      rw [show (fun x : ExtensionFiber AS L ω ↦ u x.val) =
        (fun x ↦ h (proj x.val) - Real.log (ϕ x.val a)) from rfl]
      rw [integral_sub (integrable_fibre AS L ω _) (integrable_fibre AS L ω _)]
      change fibreIntegral AS L (fun x ↦ h (proj x)) ω -
        fibreIntegral AS L (fun x ↦ Real.log (ϕ x a)) ω = _
      rw [fibreIntegral_comp_proj, fibreIntegral_log_eq_log_norm AS L a ha]
    rw [heq]
    exact hi.sub ((AS.integrable_log (Algebra.norm K a)
      (Algebra.norm_ne_zero_iff.mpr ha)).div_const _)
  have hmp : MeasurePreserving (proj (AS := AS) (L := L))
      (inducedMeasure AS L) AS.v :=
    ⟨measurable_proj AS L, map_inducedMeasure_proj AS L⟩
  have hc := hmp.integrable_comp_of_integrable hi
  convert hc.sub uint using 1
  funext x
  dsimp [u, Function.comp_def]
  ring

/-- Chen--Moriwaki, Theorem 3.3.7(5), formula (3.9): the logarithmic integral against the
induced measure computes the logarithm of the norm form:
`[K' : K] ∫ ln |b|_x dν_{K'} = ∫ ln |N_{K'/K}(b)|_ω dν_K`. -/
theorem finrank_mul_integral_log_inducedMeasure (b : L) (hb : b ≠ 0) :
    (Module.finrank K L : ℝ) * ∫ x, Real.log (ϕ x b) ∂inducedMeasure AS L =
      ∫ ω, Real.log (AS.ϕ ω (Algebra.norm K b)) ∂AS.v := by
  rw [integral_inducedMeasure AS L (integrable_log_inducedMeasure AS L b hb)]
  simp_rw [fibreIntegral_log_eq_log_norm (AS := AS) (L := L) b hb]
  rw [integral_div]
  exact mul_div_cancel₀ _ (by exact_mod_cast (Module.finrank_pos (R := K) (M := L)).ne')

/-- The finite separable extension adelic structure on `L`, using the measure defined by
Definition 3.3.6. -/
noncomputable def _root_.ArakelovGeometry.AdelicStructure.finiteSeparableExtension :
    AdelicStructure L where
  Ω := ParameterSpaceExtension AS L
  A := inferInstance
  v := inducedMeasure AS L
  ϕ := ParameterSpaceExtension.ϕ
  measurable_log := fun a _ha ↦ ParameterSpaceExtension.measurable_log AS L a
  integrable_log := integrable_log_inducedMeasure AS L

/-- Chen--Moriwaki, Theorem 3.3.7(5): the finite separable extension of a proper adelic curve
is proper. -/
theorem isProper_finiteSeparableExtension [AS.IsProper] :
    (AS.finiteSeparableExtension L).IsProper := by
  constructor
  change ∀ a : L, a ≠ 0 → ∫ x, Real.log (ϕ x a) ∂inducedMeasure AS L = 0
  intro a ha
  have hn : Algebra.norm K a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
  have h := finrank_mul_integral_log_inducedMeasure AS L a ha
  have hzero : (∫ ω, Real.log (AS.ϕ ω (Algebra.norm K a)) ∂AS.v) = 0 :=
    AdelicStructure.IsProper.product_formula (AS := AS) (Algebra.norm K a) hn
  rw [hzero] at h
  exact (mul_eq_zero.mp h).resolve_left
    (by exact_mod_cast (Module.finrank_pos (R := K) (M := L)).ne')

end ArakelovGeometry.AdelicStructure.ParameterSpaceExtension
