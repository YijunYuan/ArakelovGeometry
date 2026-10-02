/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Defs
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Archimedean places of the rational-function adelic curve

The archimedean component of Chen–Moriwaki §3.2.5 consists of the parameters
`t ∈ [0,1]` for which `exp (2πit)` is transcendental over `ℚ`. Its measure is
the induced Lebesgue measure. Evaluation at these points gives absolute values
on `ℚ(T)` extending the usual rational absolute value.
-/

namespace ArakelovGeometry.AdelicCurve.RationalFunction

open MeasureTheory Set
open scoped ENNReal

/-- The unit-circle point with parameter `t ∈ [0,1]`. -/
noncomputable def circlePoint (t : ℝ) : ℂ := circleMap 0 1 (t * (2 * Real.pi))

theorem circlePoint_eq_exp (t : ℝ) :
    circlePoint t = Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
  simp [circlePoint, circleMap, mul_comm t]

theorem continuous_circlePoint : Continuous circlePoint := by
  exact (continuous_circleMap 0 1).comp (continuous_id.mul continuous_const)

/-- The full-measure subset of transcendental unit-circle parameters. -/
def archimedeanDomain : Set ℝ :=
  Icc 0 1 ∩ {t | Transcendental ℚ (circlePoint t)}

/-- An archimedean place of the rational-function example. -/
abbrev ArchimedeanPlace := archimedeanDomain

theorem countable_algebraic_circle_parameters :
    {t : ℝ | IsAlgebraic ℚ (circlePoint t)}.Countable := by
  have h := ((Algebraic.countable ℚ ℂ).preimage_circleMap 0 (R := 1) one_ne_zero).preimage
    (f := fun t : ℝ ↦ t * (2 * Real.pi))
    (mul_left_injective₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero))
  exact h

theorem measurableSet_archimedeanDomain : MeasurableSet archimedeanDomain :=
  measurableSet_Icc.inter countable_algebraic_circle_parameters.measurableSet.compl

theorem volume_archimedeanDomain : volume archimedeanDomain = 1 := by
  change volume (Icc (0 : ℝ) 1 \ {t | IsAlgebraic ℚ (circlePoint t)}) = 1
  rw [measure_sdiff_null (countable_algebraic_circle_parameters.measure_zero volume)]
  simp

/-- Lebesgue measure on the transcendental unit-circle parameters. -/
noncomputable def archimedeanMeasure : Measure ArchimedeanPlace := volume.comap Subtype.val

instance : IsProbabilityMeasure archimedeanMeasure where
  measure_univ := by
    rw [archimedeanMeasure,
      (MeasurableEmbedding.subtype_coe measurableSet_archimedeanDomain).comap_apply]
    simpa using volume_archimedeanDomain

/-- Evaluation of a rational function at a transcendental unit-circle point. -/
noncomputable def archimedeanEval (t : ArchimedeanPlace) : RatFunc ℚ →+* ℂ :=
  RatFunc.liftRingHom (Polynomial.aeval (R := ℚ) (circlePoint t)).toRingHom (by
    intro p hp
    change Polynomial.aeval (circlePoint t) p ∈ nonZeroDivisors ℂ
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact fun h ↦ (mem_nonZeroDivisors_iff_ne_zero.mp hp)
      ((transcendental_iff_injective.mp t.property.2) (by simpa using h)))

/-- The absolute value obtained by evaluating at a transcendental unit-circle point. -/
noncomputable def archimedeanAbv (t : ArchimedeanPlace) : AbsoluteValue (RatFunc ℚ) ℝ :=
  (NormedField.toAbsoluteValue ℂ).pullback (archimedeanEval t)

theorem archimedeanAbv_apply (t : ArchimedeanPlace) (f : RatFunc ℚ) :
    archimedeanAbv t f = ‖Polynomial.aeval (circlePoint t) f.num /
      Polynomial.aeval (circlePoint t) f.denom‖ := by
  change ‖archimedeanEval t f‖ = _
  rw [archimedeanEval, RatFunc.liftRingHom_apply]
  rfl

@[simp]
theorem archimedeanAbv_rat (t : ArchimedeanPlace) (a : ℚ) :
    archimedeanAbv t (algebraMap ℚ (RatFunc ℚ) a) = Rat.AbsoluteValue.real a := by
  change ‖archimedeanEval t (algebraMap ℚ (RatFunc ℚ) a)‖ = _
  simp [Rat.AbsoluteValue.real_eq_abs]

theorem not_isNonarchimedean_archimedeanAbv (t : ArchimedeanPlace) :
    ¬IsNonarchimedean (archimedeanAbv t) := by
  intro h
  have htwo := archimedeanAbv_rat t 2
  norm_num [Rat.AbsoluteValue.real_eq_abs] at htwo
  have hone := h 1 1
  norm_num [show (1 : RatFunc ℚ) + 1 = 2 by norm_num, htwo] at hone

theorem measurable_log_archimedeanAbv (f : RatFunc ℚ) :
    Measurable (fun t : ArchimedeanPlace ↦ Real.log (archimedeanAbv t f)) := by
  simp_rw [archimedeanAbv_apply]
  exact (((f.num.continuous_aeval.comp continuous_circlePoint).measurable.comp
    measurable_subtype_coe).div
      ((f.denom.continuous_aeval.comp continuous_circlePoint).measurable.comp
        measurable_subtype_coe)).norm.log

theorem integrable_log_polynomial_circle (p : Polynomial ℚ) :
    Integrable (fun t : ArchimedeanPlace ↦
      Real.log ‖Polynomial.aeval (circlePoint t) p‖) archimedeanMeasure := by
  have h := ((p.map (algebraMap ℚ ℂ)).intervalIntegrable_mahlerMeasure).comp_mul_right
    (c := 2 * Real.pi)
  have hi : IntegrableOn (fun t : ℝ ↦ Real.log ‖Polynomial.aeval (circlePoint t) p‖)
      (Icc 0 1) volume := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    simpa [circlePoint, Polynomial.eval_map_algebraMap,
      mul_ne_zero two_ne_zero Real.pi_ne_zero] using h
  exact (integrableOn_iff_comap_subtypeVal measurableSet_archimedeanDomain).mp
    (hi.mono_set inter_subset_left)

theorem integrable_log_archimedeanAbv {f : RatFunc ℚ} (hf : f ≠ 0) :
    Integrable (fun t : ArchimedeanPlace ↦ Real.log (archimedeanAbv t f))
      archimedeanMeasure := by
  refine ((integrable_log_polynomial_circle f.num).sub
    (integrable_log_polynomial_circle f.denom)).congr (Filter.Eventually.of_forall fun t ↦ ?_)
  dsimp only [Pi.sub_apply]
  rw [archimedeanAbv_apply, norm_div, Real.log_div]
  · exact norm_ne_zero_iff.mpr (fun h ↦ RatFunc.num_ne_zero hf
      ((transcendental_iff_injective.mp t.property.2) (by simpa using h)))
  · exact norm_ne_zero_iff.mpr (fun h ↦ f.denom_ne_zero
      ((transcendental_iff_injective.mp t.property.2) (by simpa using h)))

/-- The archimedean component of Chen–Moriwaki's rational-function adelic structure. -/
noncomputable def archimedeanAdelicStructure : AdelicStructure (RatFunc ℚ) where
  Ω := ArchimedeanPlace
  v := archimedeanMeasure
  ϕ := archimedeanAbv
  measurable_log f _ := measurable_log_archimedeanAbv f
  integrable_log _ hf := integrable_log_archimedeanAbv hf

end ArakelovGeometry.AdelicCurve.RationalFunction
