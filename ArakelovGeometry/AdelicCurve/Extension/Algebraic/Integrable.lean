/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Integral

/-!
# Almost everywhere algebraic fibre integration

Algebraic fibre integration respects almost everywhere equality. Integrable
functions admit measurable representatives, and the fibre operator descends
to equivalence classes of integrable functions.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ArakelovGeometry.AdelicStructure.Algebraic

variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]


/-- Algebraic fibre integration respects global almost everywhere equality. -/
theorem fibreIntegral_congr_ae {f g : ParameterSpaceExtension AS L → ℝ}
    (hfg : f =ᵐ[measure AS L] g) :
    fibreIntegral AS L f =ᵐ[AS.v] fibreIntegral AS L g := by
  filter_upwards [ae_ae_fibre_of_ae AS L hfg] with ω hω
  exact integral_congr_ae hω


/-- Every integrable real function has a projectively measurable representative. -/
theorem exists_measurable_representative {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    ∃ g : ParameterSpaceExtension AS L → ℝ,
      Measurable[projectiveMeasurableSpace AS L] g ∧ f =ᵐ[measure AS L] g := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  exact ⟨hf.aestronglyMeasurable.mk f,
    hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable,
    hf.aestronglyMeasurable.ae_eq_mk⟩


/-- Fibre integration is additive almost everywhere for integrable functions. -/
theorem fibreIntegral_add_ae {f g : ParameterSpaceExtension AS L → ℝ}
    (hf : Integrable[projectiveMeasurableSpace AS L] f (measure AS L))
    (hg : Integrable[projectiveMeasurableSpace AS L] g (measure AS L)) :
    fibreIntegral AS L (f + g) =ᵐ[AS.v]
      fibreIntegral AS L f + fibreIntegral AS L g := by
  filter_upwards [integrable_fibre_ae AS L hf, integrable_fibre_ae AS L hg] with ω hωf hωg
  exact integral_add hωf hωg

/-- Fibre integration commutes with multiplication by a real scalar. -/
theorem fibreIntegral_smul (c : ℝ) (f : ParameterSpaceExtension AS L → ℝ) :
    fibreIntegral AS L (c • f) = c • fibreIntegral AS L f := by
  funext ω
  exact integral_smul c _

/-- Fibre integration of an L1 class, as an L1 class on the base. -/
noncomputable def fibreIntegralL1 :
    Lp ℝ 1 (measure AS L) → Lp ℝ 1 AS.v :=
  fun f ↦ (integrable_fibreIntegral AS L (L1.integrable_coeFn f)).toL1
    (fibreIntegral AS L f)

/-- The L1 fibre average is represented by the fibre integral of a representative. -/
theorem coeFn_fibreIntegralL1 (f : Lp ℝ 1 (measure AS L)) :
    fibreIntegralL1 AS L f =ᵐ[AS.v] fibreIntegral AS L f :=
  Integrable.coeFn_toL1 _

/-- The operation on L1 classes is additive. -/
theorem fibreIntegralL1_add (f g : Lp ℝ 1 (measure AS L)) :
    fibreIntegralL1 AS L (f + g) = fibreIntegralL1 AS L f + fibreIntegralL1 AS L g := by
  apply Lp.ext
  filter_upwards [coeFn_fibreIntegralL1 AS L (f + g),
    fibreIntegral_congr_ae AS L (Lp.coeFn_add f g),
    fibreIntegral_add_ae AS L (L1.integrable_coeFn f) (L1.integrable_coeFn g),
    coeFn_fibreIntegralL1 AS L f, coeFn_fibreIntegralL1 AS L g,
    Lp.coeFn_add (fibreIntegralL1 AS L f) (fibreIntegralL1 AS L g)] with ω h1 h2 h3 h4 h5 h6
  simpa only [Pi.add_apply] using
    h1.trans (h2.trans (h3.trans ((congrArg₂ (· + ·) h4 h5).symm.trans h6.symm)))

/-- The operation on L1 classes respects real scalar multiplication. -/
theorem fibreIntegralL1_smul (c : ℝ) (f : Lp ℝ 1 (measure AS L)) :
    fibreIntegralL1 AS L (c • f) = c • fibreIntegralL1 AS L f := by
  apply Lp.ext
  filter_upwards [coeFn_fibreIntegralL1 AS L (c • f),
    fibreIntegral_congr_ae AS L (Lp.coeFn_smul c f),
    coeFn_fibreIntegralL1 AS L f,
    Lp.coeFn_smul c (fibreIntegralL1 AS L f)] with ω h1 h2 h3 h4
  simp only [fibreIntegral_smul, Pi.smul_apply] at h2
  exact h1.trans (h2.trans ((congrArg (c • ·) h3).symm.trans h4.symm))

/-- Fibre integration does not increase the L1 norm. -/
theorem norm_fibreIntegralL1_le (f : Lp ℝ 1 (measure AS L)) :
    ‖fibreIntegralL1 AS L f‖ ≤ ‖f‖ := by
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
  have heq : (fun ω ↦ ‖fibreIntegralL1 AS L f ω‖) =ᵐ[AS.v]
      fun ω ↦ ‖fibreIntegral AS L f ω‖ := by
    filter_upwards [coeFn_fibreIntegralL1 AS L f] with ω hω
    exact congrArg norm hω
  rw [integral_congr_ae heq]
  simpa only [Real.norm_eq_abs] using integral_abs_fibreIntegral_le AS L (L1.integrable_coeFn f)

/-- The continuous linear contraction induced by algebraic fibre integration. -/
noncomputable def fibreIntegralL1ContinuousLinearMap :
    Lp ℝ 1 (measure AS L) →L[ℝ] Lp ℝ 1 AS.v :=
  ({ toFun := fibreIntegralL1 AS L
     map_add' := fibreIntegralL1_add AS L
     map_smul' := fibreIntegralL1_smul AS L } :
    Lp ℝ 1 (measure AS L) →ₗ[ℝ] Lp ℝ 1 AS.v).mkContinuous 1
      (fun f ↦ by simpa using norm_fibreIntegralL1_le AS L f)

/-- The operator norm of algebraic fibre integration is at most one. -/
theorem norm_fibreIntegralL1ContinuousLinearMap_le :
    ‖fibreIntegralL1ContinuousLinearMap AS L‖ ≤ 1 :=
  (fibreIntegralL1ContinuousLinearMap AS L).opNorm_le_bound zero_le_one
    (fun f ↦ by simpa [fibreIntegralL1ContinuousLinearMap] using
      norm_fibreIntegralL1_le AS L f)

/-- The continuous linear operator agrees with fibre integration on every integrable function. -/
theorem fibreIntegralL1_toL1 {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    fibreIntegralL1ContinuousLinearMap AS L (hf.toL1 f) =
      (integrable_fibreIntegral AS L hf).toL1 (fibreIntegral AS L f) := by
  apply Lp.ext
  exact (coeFn_fibreIntegralL1 AS L (hf.toL1 f)).trans
    ((fibreIntegral_congr_ae AS L hf.coeFn_toL1).trans
      (integrable_fibreIntegral AS L hf).coeFn_toL1.symm)

end ArakelovGeometry.AdelicStructure.Algebraic
