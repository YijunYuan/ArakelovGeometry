/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Rescaling
public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic
public import ArakelovGeometry.NumberTheory.NumberField.Model.Sections
import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.AdelicVectorBundle.Slope.Rescaling
import Mathlib.Topology.Sheaves.Init

/-! # Actual arithmetic twists of prescribed degree -/

@[expose] public section

noncomputable section
open NumberField MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldClassicalPositiveTwist

open AdelicStructure NumberFieldFullLattice NumberFieldProjectiveGeneric
  ActualPrimeIndexing
open NumberFieldInvertibleGeneric (genericImage genericImage_fullSpan)

variable (K : Type*) [Field K] [NumberField K]

/-- The actual Archimedean exponent, with integral equal to minus the prescribed degree. -/
def twistExponent (t : ℝ) : (normalizedNumberFieldAdelicStructure K).Ω → ℝ :=
  (normalizedNumberFieldAdelicStructure K).Ωinf.indicator
    (fun _ => -t / (Module.finrank ℚ K : ℝ))

theorem twistExponent_measurable (t : ℝ) : Measurable (twistExponent K t) :=
  measurable_const.indicator (normalizedNumberFieldAdelicStructure K).measurableSet_Ωinf

theorem twistExponent_integrable (t : ℝ) :
    Integrable (twistExponent K t) (normalizedNumberFieldAdelicStructure K).v := by
  let S := normalizedNumberFieldAdelicStructure K
  have hf : S.v S.Ωinf ≠ ⊤ := by
    rw [normalizedNumberFieldAdelicStructure_v_Ωinf]
    simp
  exact (integrableOn_const (μ := S.v) (C := -t / (Module.finrank ℚ K : ℝ))
    (s := S.Ωinf) hf).integrable_indicator S.measurableSet_Ωinf

theorem integral_twistExponent (t : ℝ) :
    (∫ ω, twistExponent K t ω ∂(normalizedNumberFieldAdelicStructure K).v) = -t := by
  let S := normalizedNumberFieldAdelicStructure K
  have hm : S.v.real S.Ωinf = (Module.finrank ℚ K : ℝ) := by
    change (S.v S.Ωinf).toReal = _
    rw [normalizedNumberFieldAdelicStructure_v_Ωinf, ENNReal.toReal_natCast]
  rw [twistExponent, integral_indicator_const _ S.measurableSet_Ωinf, hm, smul_eq_mul]
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (Module.finrank_pos (R := ℚ) (M := K)))
  field_simp

variable {K}
  {E : Type*} [AddCommGroup E] [Module K E]

/-- The actual norm family with infinite norms multiplied by exp(-t/d). -/
def twistFamily (η : NormFamily (normalizedNumberFieldAdelicStructure K) E) (t : ℝ) :
    NormFamily (normalizedNumberFieldAdelicStructure K) E :=
  η.scale (fun ω => Real.exp (twistExponent K t ω)) (fun _ => Real.exp_pos _)

theorem twistFamily_isHermitian
    {η : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) (t : ℝ) :
    (twistFamily η t).IsHermitian normalizedNumberFieldArchimedeanCompletions :=
  hη.scale _ _

/-- The actual canonical arithmetic model commutes with the Archimedean twist. -/
theorem fullLatticeAdelicBundle_twistFamily [FiniteDimensional K E]
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤)
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) E) (t : ℝ) :
    fullLatticeAdelicBundle L hfg hspan (twistFamily η t) =
      (fullLatticeAdelicBundle L hfg hspan η).scaleExp (twistExponent K t)
        (twistExponent_measurable K t) (twistExponent_integrable K t) := by
  classical
  apply AdelicVectorBundle.ext
  ext ω z
  by_cases hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin
  · obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
    change (fullLatticeGaugeFamily L hfg hspan (twistFamily η t)).norm
        (normalizedPrimeParameter p) z =
      Real.exp (twistExponent K t (normalizedPrimeParameter p)) *
        (fullLatticeGaugeFamily L hfg hspan η).norm (normalizedPrimeParameter p) z
    rw [fullLatticeGaugeFamily_norm_prime, fullLatticeGaugeFamily_norm_prime]
    have hn : normalizedPrimeParameter p ∉ (normalizedNumberFieldAdelicStructure K).Ωinf :=
      fun h => h hω
    simp only [twistExponent, Set.indicator_of_notMem hn, Real.exp_zero, one_mul]
  · change (fullLatticeGaugeFamily L hfg hspan (twistFamily η t)).norm ω z =
      Real.exp (twistExponent K t ω) * (fullLatticeGaugeFamily L hfg hspan η).norm ω z
    rw [fullLatticeGaugeFamily_norm_not_finite _ _ _ _ ω hω,
      fullLatticeGaugeFamily_norm_not_finite _ _ _ _ ω hω]
    rfl

/-- The actual arithmetic determinant degree increases by rank times the prescribed twist. -/
theorem degree_twistFamily [FiniteDimensional K E]
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤)
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) E) (t : ℝ) :
    (fullLatticeAdelicBundle L hfg hspan (twistFamily η t)).degree
        (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions =
      (fullLatticeAdelicBundle L hfg hspan η).degree
        (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions +
          (Module.finrank K E : ℝ) * t := by
  rw [fullLatticeAdelicBundle_twistFamily, AdelicVectorBundle.degree_scaleExp,
    integral_twistExponent]
  ring

/-- The actual minimal slope gains the prescribed twist, including its infinite rank-zero value. -/
theorem minimalSlope_twistFamily [FiniteDimensional K E]
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤)
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) E) (t : ℝ) :
    (fullLatticeAdelicBundle L hfg hspan (twistFamily η t)).minimalSlope
        (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions =
      (fullLatticeAdelicBundle L hfg hspan η).minimalSlope
        (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions + (t : EReal) := by
  rw [fullLatticeAdelicBundle_twistFamily, AdelicVectorBundle.minimalSlope_scaleExp,
    integral_twistExponent]
  simp only [EReal.coe_neg, sub_eq_add_neg, neg_neg]

variable (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]

omit [AddCommGroup E] [Module K E] in
/-- Every original effective section remains effective under a nonnegative actual twist. -/
theorem effectiveSections_subset_twistFamily
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    {t : ℝ} (ht : 0 ≤ t) :
    effectiveSections M η ⊆ effectiveSections M (twistFamily η t) := by
  intro m hm ω hω
  change Real.exp (twistExponent K t ω) *
    η.norm ω (1 ⊗ₜ[K] NumberFieldInvertibleGeneric.genericInclusion (K := K) M m) ≤ 1
  rw [twistExponent, Set.indicator_of_mem hω]
  have he : Real.exp (-t / (Module.finrank ℚ K : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (by positivity))
  exact (mul_le_mul_of_nonneg_right he (η.norm_nonneg _ _)).trans
    (by simpa only [one_mul] using hm ω hω)

omit [AddCommGroup E] [Module K E] in
/-- Literal finite original section-set inclusion gives the actual source h0 monotonicity. -/
theorem logSectionCount_le_twistFamily
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    {t : ℝ} (ht : 0 ≤ t) :
    logSectionCount M η ≤ logSectionCount M (twistFamily η t) := by
  have hc : Nat.card (effectiveSections M η) ≤ Nat.card (effectiveSections M (twistFamily η t)) :=
    Set.ncard_le_ncard (effectiveSections_subset_twistFamily M η ht)
      (finite_effectiveSections M (twistFamily η t))
  exact Real.log_le_log (Nat.cast_pos.mpr (card_effectiveSections_pos M η))
    (Nat.cast_le.mpr hc)

end ArakelovGeometry.NumberFieldClassicalPositiveTwist
