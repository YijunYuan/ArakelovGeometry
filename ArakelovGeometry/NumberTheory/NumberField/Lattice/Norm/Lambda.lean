/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Minima.Basic
public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Norm.Gauge

import ArakelovGeometry.AdelicVectorBundle.Minima.BasisSupremum
import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.InfiniteMass

/-!
# The actual number-field integral-basis invariant

The Archimedean maximum and the finite integral lattice are taken on the
original rational vectors and completed fibres. The integral-basis thresholds
define an extended-real supremum, with top in rank zero. Gauge replacement
preserves this invariant. Analytic hypotheses enter only the comparison with
the actual last logarithmic minimum, not the invariant's definition.
-/

@[expose] public section

open MeasureTheory
open scoped NumberField TensorProduct BigOperators

noncomputable section

namespace ArakelovGeometry.NormFamily

open AdelicStructure

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]

variable (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)

/-- The finite Archimedean maximum on actual rational vectors. Adjoining zero
also gives the canonical empty-maximum convention. -/
def archimedeanMaxNorm (x : E) : ℝ :=
  sSup (insert 0 ((fun ω => ξ.norm ω (1 ⊗ₜ[K] x)) ''
    (normalizedNumberFieldAdelicStructure K).Ωinf))

private theorem archimedeanNormValues_bddAbove (x : E) :
    BddAbove (insert 0 ((fun ω => ξ.norm ω (1 ⊗ₜ[K] x)) ''
      (normalizedNumberFieldAdelicStructure K).Ωinf)) :=
  ((normalizedNumberFieldAdelicStructure_Ωinf_finite.image _).insert 0).bddAbove

theorem archimedeanMaxNorm_nonneg (x : E) : 0 ≤ ξ.archimedeanMaxNorm x :=
  le_csSup (ξ.archimedeanNormValues_bddAbove x) (Set.mem_insert 0 _)

theorem archimedeanMaxNorm_le_iff (x : E) {r : ℝ} (hr : 0 ≤ r) :
    ξ.archimedeanMaxNorm x ≤ r ↔
      ∀ ω ∈ (normalizedNumberFieldAdelicStructure K).Ωinf,
        ξ.norm ω (1 ⊗ₜ[K] x) ≤ r := by
  constructor
  · intro h ω hω
    exact (le_csSup (ξ.archimedeanNormValues_bddAbove x)
      (Set.mem_insert_of_mem 0 ⟨ω, hω, rfl⟩)).trans h
  · intro h
    apply Real.sSup_le _ hr
    rintro y (rfl | ⟨ω, hω, rfl⟩)
    · exact hr
    · exact h ω hω

variable [FiniteDimensional K E]

/-- Actual rational bases lying in the literal finite integral ball and
bounded at every infinite place. No endpoint finiteness is assumed. -/
def integralBasisThresholds : Set ℝ :=
  {a | ∃ b : Module.Basis (Fin (Module.finrank K E)) K E,
    ∀ i, b i ∈ ξ.globalUnitBall ∧ ξ.archimedeanMaxNorm (b i) ≤ Real.exp (-a)}

/-- The source integral-basis invariant, extended to arbitrary norm families.
The empty basis gives value top in rank zero. -/
def latticeLambda : EReal := ⨆ a ∈ ξ.integralBasisThresholds, (a : EReal)

omit [FiniteDimensional K E] in
theorem mem_integralBasisThresholds_iff (a : ℝ) : a ∈ ξ.integralBasisThresholds ↔
    ∃ b : Module.Basis (Fin (Module.finrank K E)) K E,
      ∀ i, b i ∈ ξ.globalUnitBall ∧
        ∀ ω ∈ (normalizedNumberFieldAdelicStructure K).Ωinf,
          ξ.norm ω (1 ⊗ₜ[K] b i) ≤ Real.exp (-a) := by
  simp only [integralBasisThresholds, Set.mem_ofPred_eq,
    ξ.archimedeanMaxNorm_le_iff _ (Real.exp_pos _).le]

theorem latticeLambda_eq_top_of_finrank_eq_zero (hr : Module.finrank K E = 0) :
    ξ.latticeLambda = ⊤ := by
  apply top_unique
  apply EReal.ge_of_forall_gt_iff_ge.mp
  intro a _
  have ha : a ∈ ξ.integralBasisThresholds := by
    refine ⟨Module.finBasis K E, fun i => ?_⟩
    exact False.elim (by simpa [hr] using i.isLt)
  exact le_iSup_of_le a (le_iSup_of_le ha le_rfl)

theorem latticeGaugeFamily_archimedeanMaxNorm_eq [hξ : ξ.IsUltrametric] (x : E) :
    (ξ.latticeGaugeFamily).archimedeanMaxNorm x = ξ.archimedeanMaxNorm x := by
  unfold archimedeanMaxNorm
  congr 2
  apply Set.image_congr
  intro ω hω
  rw [ξ.latticeGaugeFamily_norm_not_finite ω hω]

theorem latticeGaugeFamily_integralBasisThresholds_eq [hξ : ξ.IsUltrametric] :
    (ξ.latticeGaugeFamily).integralBasisThresholds = ξ.integralBasisThresholds := by
  ext a
  simp only [integralBasisThresholds, Set.mem_ofPred_eq,
    ξ.latticeGaugeFamily_globalUnitBall_eq,
    ξ.latticeGaugeFamily_archimedeanMaxNorm_eq]

theorem latticeGaugeFamily_latticeLambda_eq [hξ : ξ.IsUltrametric] :
    (ξ.latticeGaugeFamily).latticeLambda = ξ.latticeLambda := by
  simp only [latticeLambda, ξ.latticeGaugeFamily_integralBasisThresholds_eq]

/-- Genuine full rational span of the literal integral ball produces an
actual integral basis and a real threshold, including the empty basis. -/
theorem integralBasisThresholds_nonempty_of_span_globalUnitBall_eq_top
    (hspan : Submodule.span K ξ.globalUnitBall = ⊤) :
    ξ.integralBasisThresholds.Nonempty := by
  classical
  have he := Submodule.exists_fun_fin_finrank_span_eq K ξ.globalUnitBall
  rw [hspan, finrank_top] at he
  obtain ⟨f, hf, _, hli⟩ := he
  let b := basisOfLinearIndependentOfCardEqFinrank' f hli (by simp)
  let C : ℝ := 1 + ∑ i, ξ.archimedeanMaxNorm (b i)
  have hsum : 0 ≤ ∑ i, ξ.archimedeanMaxNorm (b i) :=
    Finset.sum_nonneg fun i _ => ξ.archimedeanMaxNorm_nonneg (b i)
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨-Real.log C, b, fun i => ⟨?_, ?_⟩⟩
  · simpa only [b, coe_basisOfLinearIndependentOfCardEqFinrank'] using hf i
  · rw [neg_neg, Real.exp_log hC]
    have hi : ξ.archimedeanMaxNorm (b i) ≤ ∑ j, ξ.archimedeanMaxNorm (b j) :=
      Finset.single_le_sum (fun j _ => ξ.archimedeanMaxNorm_nonneg (b j)) (Finset.mem_univ i)
    dsimp [C]
    linarith

/-- Source coherence supplies the nonempty real threshold set; no integral
basis or bound is supplied as an extra certificate. -/
theorem HasFiniteNormExceptions.integralBasisThresholds_nonempty
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hfinite : ξ.HasFiniteNormExceptions) : ξ.integralBasisThresholds.Nonempty :=
  ξ.integralBasisThresholds_nonempty_of_span_globalUnitBall_eq_top
    (hfinite.span_globalUnitBall_eq_top (fun ω _ =>
      NormalizedNumberFieldPlaces.parameter_isNontrivial
        (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω)))

/-- Coherence rules out the negative infinite endpoint of the integral-basis
invariant without assuming a finite upper endpoint. -/
theorem HasFiniteNormExceptions.latticeLambda_ne_bot
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hfinite : ξ.HasFiniteNormExceptions) : ξ.latticeLambda ≠ ⊥ := by
  obtain ⟨a, ha⟩ := hfinite.integralBasisThresholds_nonempty
  have h : (a : EReal) ≤ ξ.latticeLambda :=
    le_iSup_of_le a (le_iSup_of_le ha le_rfl)
  intro hbot
  rw [hbot] at h
  exact EReal.coe_ne_bot a (le_bot_iff.mp h)

/-- The actual degree of an integral vector bounded at infinity is at least
the rational number-field degree times its logarithmic bound. -/
theorem vectorDegree_ge_of_integral_archimedean_bound
    [hd : ξ.IsDominated] [hm : ξ.IsMeasurable] (s : {x : E // x ≠ 0})
    {a : ℝ} (hs : s.val ∈ ξ.globalUnitBall)
    (ha : ξ.archimedeanMaxNorm s.val ≤ Real.exp (-a)) :
    (Module.finrank ℚ K : ℝ) * a ≤ ξ.vectorDegree s := by
  classical
  let S := normalizedNumberFieldAdelicStructure K
  have : MeasurableSingletonClass S.Ω := by
    change MeasurableSingletonClass
      {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}
    infer_instance
  have hmInf : MeasurableSet S.Ωinf :=
    normalizedNumberFieldAdelicStructure_Ωinf_finite.measurableSet
  have hfinite : S.v S.Ωinf ≠ ⊤ := by
    rw [normalizedNumberFieldAdelicStructure_v_Ωinf]
    simp
  have hupper : Integrable (S.Ωinf.indicator (fun _ => -a)) S.v :=
    (integrableOn_const (μ := S.v) (C := -a) (s := S.Ωinf) hfinite).integrable_indicator hmInf
  have hbound : ∀ ω, ξ.logNorm s.val ω ≤ S.Ωinf.indicator (fun _ => -a) ω := by
    intro ω
    by_cases hω : ω ∈ S.Ωinf
    · rw [Set.indicator_of_mem hω]
      have hn := (ξ.archimedeanMaxNorm_le_iff _ (Real.exp_pos _).le).mp ha ω hω
      change Real.log _ ≤ -a
      simpa only [Real.log_exp] using
        Real.log_le_log (ξ.norm_rational_pos ω s.property) hn
    · rw [Set.indicator_of_notMem hω]
      have hf : ω ∈ S.Ωfin := not_not.mp hω
      have hn := (ξ.mem_globalUnitBall s.val).mp hs ω hf
      exact Real.log_nonpos (ξ.norm_nonneg ω _) hn
  have hi := integral_mono (hd.integrable_logNorm hm s.val) hupper hbound
  rw [integral_indicator_const _ hmInf] at hi
  have hmass : S.v.real S.Ωinf = (Module.finrank ℚ K : ℝ) := by
    change ((normalizedNumberFieldAdelicStructure K).v
      (normalizedNumberFieldAdelicStructure K).Ωinf).toReal = _
    rw [normalizedNumberFieldAdelicStructure_v_Ωinf, ENNReal.toReal_natCast]
  rw [hmass, smul_eq_mul] at hi
  rw [ξ.vectorDegree_eq_neg_integral s]
  linarith

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.AdelicVectorBundle

open AdelicStructure NormFamily

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- Each actual integral-basis threshold supplies a lower threshold for the
existing last logarithmic minimum, without endpoint finiteness or attainment. -/
theorem coe_le_minimalLogarithmicMinimum_of_integralBasisThreshold
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K))
    {a : ℝ} (ha : a ∈ V.toNormFamily.integralBasisThresholds) :
    ((Module.finrank ℚ K : ℝ) * a : EReal) ≤ V.minimalLogarithmicMinimum := by
  obtain ⟨b, hb⟩ := ha
  apply V.coe_le_logarithmicMinimum_of_finrank_le
  apply (V.finrank_le_degreeThresholdSpan_iff_exists_basis _).mpr
  refine ⟨b, fun i => ?_⟩
  exact V.toNormFamily.vectorDegree_ge_of_integral_archimedean_bound
    ⟨b i, b.ne_zero i⟩ (hb i).1 (hb i).2

/-- The first inequality of source Proposition 4.4.10 in the extended real
line. Coherence and a finite endpoint are unnecessary for this direction. -/
theorem degree_mul_latticeLambda_le_minimalLogarithmicMinimum
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K)) :
    ((Module.finrank ℚ K : ℝ) : EReal) * V.toNormFamily.latticeLambda ≤
      V.minimalLogarithmicMinimum := by
  let d : ℝ := Module.finrank ℚ K
  have hd : 0 < d := Nat.cast_pos.mpr Module.finrank_pos
  have hinv : 0 ≤ ((d⁻¹ : ℝ) : EReal) := EReal.coe_nonneg.mpr (inv_pos.mpr hd).le
  have hlambda : V.toNormFamily.latticeLambda ≤
      ((d⁻¹ : ℝ) : EReal) * V.minimalLogarithmicMinimum := by
    apply iSup_le
    intro a
    apply iSup_le
    intro ha
    have h := mul_le_mul_of_nonneg_left
      (V.coe_le_minimalLogarithmicMinimum_of_integralBasisThreshold ha) hinv
    change ((d⁻¹ : ℝ) : EReal) * ((d * a : ℝ) : EReal) ≤ _ at h
    simpa only [← EReal.coe_mul, ← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul] using h
  have h := mul_le_mul_of_nonneg_left hlambda (EReal.coe_nonneg.mpr hd.le)
  simpa only [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hd.ne',
    EReal.coe_one, one_mul] using h

end ArakelovGeometry.AdelicVectorBundle
