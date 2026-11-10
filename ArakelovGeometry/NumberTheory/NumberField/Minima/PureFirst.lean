/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Minima.Basic
public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic
public import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Normalization.Hermitian
public import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Purity.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Hermitian.Approximation
import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.InfiniteMass
import ArakelovGeometry.NumberTheory.NumberField.Minima.HermitianFirst
import ArakelovGeometry.NumberTheory.NumberField.Minima.SlopeComparison
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Topology.Sheaves.Init

/-! # The actual ordinary first minimum with pure finite norms -/

@[expose] public section

noncomputable section

open NumberField MeasureTheory Filter
open scoped Topology

namespace ArakelovGeometry.NumberFieldPureFirstMinimum

open AdelicStructure NumberFieldMinimumSlopeComparison

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

omit [AddCommGroup E] [Module K E] [FiniteDimensional K E] in
/-- The literal logarithmic comparison envelope, supported on the actual infinite locus. -/
def infiniteLogEnvelope (n : ℕ) (ε : ℝ) :
    (normalizedNumberFieldAdelicStructure K).Ω → ℝ :=
  (normalizedNumberFieldAdelicStructure K).Ωinf.indicator
    (fun _ => Real.log (Real.sqrt ((n : ℝ) + ε)))

omit [AddCommGroup E] [Module K E] [FiniteDimensional K E] in
theorem infiniteLogEnvelope_integrable (n : ℕ) (ε : ℝ) :
    Integrable (infiniteLogEnvelope (K := K) n ε) (normalizedNumberFieldAdelicStructure K).v := by
  let S := normalizedNumberFieldAdelicStructure K
  have hf : S.v S.Ωinf ≠ ⊤ := by
    rw [normalizedNumberFieldAdelicStructure_v_Ωinf]
    simp
  exact (integrableOn_const (μ := S.v) (C := Real.log (Real.sqrt ((n : ℝ) + ε)))
    (s := S.Ωinf) hf).integrable_indicator S.measurableSet_Ωinf

omit [AddCommGroup E] [Module K E] [FiniteDimensional K E] in
theorem integral_infiniteLogEnvelope {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    (∫ ω, infiniteLogEnvelope (K := K) n ε ω
      ∂(normalizedNumberFieldAdelicStructure K).v) =
        (Module.finrank ℚ K : ℝ) / 2 * Real.log ((n : ℝ) + ε) := by
  let S := normalizedNumberFieldAdelicStructure K
  have hm : S.v.real S.Ωinf = (Module.finrank ℚ K : ℝ) := by
    change ((normalizedNumberFieldAdelicStructure K).v
      (normalizedNumberFieldAdelicStructure K).Ωinf).toReal = _
    rw [normalizedNumberFieldAdelicStructure_v_Ωinf, ENNReal.toReal_natCast]
  rw [infiniteLogEnvelope, integral_indicator_const _ S.measurableSet_Ωinf, hm, smul_eq_mul,
    Real.log_sqrt (by positivity : 0 ≤ (n : ℝ) + ε)]
  ring

/-- A genuine actual Hermitian bundle is produced by measurable approximation, with its
domination proved from the computed infinite envelope and its finite purity retained. -/
theorem exists_hermitian_approximation
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hU : V.toNormFamily.IsUltrametric) (hpure : V.toNormFamily.IsPureAtFinitePlaces)
    (hn : 0 < Module.finrank K E) {ε : ℝ} (hε : 0 < ε) :
    ∃ W : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E,
      W.toNormFamily.IsHermitian normalizedNumberFieldArchimedeanCompletions ∧
      W.toNormFamily.IsPureAtFinitePlaces ∧
      (∀ ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin, ∀ z,
        W.toNormFamily.norm ω z = V.toNormFamily.norm ω z) ∧
      (∀ ω z, V.toNormFamily.norm ω z ≤ W.toNormFamily.norm ω z) ∧
      ∀ ω z, W.toNormFamily.norm ω z ≤
        Real.exp (infiniteLogEnvelope (Module.finrank K E) ε ω) * V.toNormFamily.norm ω z := by
  classical
  let S := normalizedNumberFieldAdelicStructure K
  let : Countable K := (Module.finBasis ℚ K).repr.injective.countable
  obtain ⟨η, hmη, hHη, hfη, hbη⟩ := V.isMeasurable.exists_hermitian_approximation hU
    normalizedNumberFieldArchimedeanCompletions (⊤ : Subfield K)
      (fun ω _ => S.isDenseSubfieldAt_top ω) hε
  let g := infiniteLogEnvelope (K := K) (Module.finrank K E) ε
  have hg := infiniteLogEnvelope_integrable (K := K) (Module.finrank K E) ε
  have hC : 1 ≤ Real.sqrt ((Module.finrank K E : ℝ) + ε) := by
    have hn' : (1 : ℝ) ≤ Module.finrank K E := by exact_mod_cast hn
    simpa using Real.sqrt_le_sqrt (by linarith : (1 : ℝ) ≤ (Module.finrank K E : ℝ) + ε)
  have hg0 (ω : S.Ω) : 0 ≤ g ω := by
    exact Set.indicator_nonneg (fun _ _ => Real.log_nonneg hC) ω
  have hlower (ω : S.Ω) (z) : V.toNormFamily.norm ω z ≤ η.norm ω z := by
    by_cases hω : ω ∈ S.Ωinf
    · exact (hbη ω hω z).1
    · rw [hfη ω (not_not.mp hω)]
  have hupper (ω : S.Ω) (z) : η.norm ω z ≤ Real.exp (g ω) * V.toNormFamily.norm ω z := by
    by_cases hω : ω ∈ S.Ωinf
    · have hgω : g ω = Real.log (Real.sqrt ((Module.finrank K E : ℝ) + ε)) :=
        Set.indicator_of_mem hω _
      rw [hgω, Real.exp_log (lt_of_lt_of_le zero_lt_one hC)]
      exact (hbη ω hω z).2
    · have hgω : g ω = 0 := Set.indicator_of_notMem hω _
      rw [hgω, Real.exp_zero, one_mul, hfη ω (not_not.mp hω)]
  have hδ (ω : S.Ω) : V.toNormFamily.localDist η ω ≤ g ω := by
    apply (V.toNormFamily.localDist_le_iff η ω (hg0 ω)).mpr
    intro z
    refine ⟨?_, hupper ω z⟩
    calc
      _ ≤ 1 * V.toNormFamily.norm ω z := mul_le_mul_of_nonneg_right
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hg0 ω))) (V.toNormFamily.norm_nonneg ω z)
      _ ≤ η.norm ω z := by simpa using hlower ω z
  have hdη : η.IsDominated := V.isDominated.of_localDist ⟨g, hg, Eventually.of_forall hδ⟩
  let W := AdelicVectorBundle.ofMeasurableDominated η hmη hdη (Or.inl inferInstance)
  refine ⟨W, hHη, ?_, hfη, hlower, hupper⟩
  intro ω hω z hz
  obtain ⟨a, ha, he⟩ := hpure ω hω z hz
  exact ⟨a, ha, (hfη ω hω z).trans he⟩

/-- The actual first-minimum estimate at every positive Hermitian approximation scale. -/
theorem maximalSlope_sub_approximation_error_le_firstMinimum
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hU : V.toNormFamily.IsUltrametric) (hpure : V.toNormFamily.IsPureAtFinitePlaces)
    (hn : 0 < Module.finrank K E) {ε : ℝ} (hε : 0 < ε) :
    V.maximalSlope (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions -
      (((Module.finrank ℚ K : ℝ) / 2 * Real.log ((Module.finrank K E : ℝ) + ε) +
        ((Module.finrank ℚ K : ℝ) / 2 * Real.log (Module.finrank K E : ℝ) +
          Real.log |(NumberField.discr K : ℝ)| / 2) : ℝ) : EReal) ≤
            V.maximalLogarithmicMinimum := by
  obtain ⟨W, hH, hP, _, hlower, hupper⟩ := exists_hermitian_approximation V hU hpure hn hε
  let g := infiniteLogEnvelope (K := K) (Module.finrank K E) ε
  have hg := infiniteLogEnvelope_integrable (K := K) (Module.finrank K E) ε
  have hmin := (logarithmicMinimum_comparison V W (fun _ => 0) g (integrable_zero _ ℝ _) hg
    (by simpa only [Real.exp_zero, one_mul] using hlower) hupper 1).2
  simp only [integral_zero, EReal.coe_zero, sub_zero] at hmin
  have hslope := maximalSlope_sub_integral_le V W g hg hupper
  rw [integral_infiniteLogEnvelope (K := K) hn hε] at hslope
  have hherm := NumberFieldHermitianFirstMinimum.maximalSlope_sub_error_le_firstMinimum
    W hH hP hn
  have h := (EReal.sub_le_sub hslope le_rfl).trans (hherm.trans hmin)
  convert h using 1 <;>
    simp only [AdelicVectorBundle.maximalLogarithmicMinimum, sub_eq_add_neg,
      ← EReal.coe_neg, add_assoc, ← EReal.coe_add]
  congr 1
  congr 1
  ring

/-- The actual ordinary first minimum with arbitrary infinite norms and pure ultrametric
finite norms, obtained by the honest positive-scale limit without finite-value assumptions. -/
theorem maximalSlope_sub_error_le_firstMinimum
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hU : V.toNormFamily.IsUltrametric) (hpure : V.toNormFamily.IsPureAtFinitePlaces)
    (hn : 0 < Module.finrank K E) :
    V.maximalSlope (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions -
      (((Module.finrank ℚ K : ℝ) * Real.log (Module.finrank K E : ℝ) +
        Real.log |(NumberField.discr K : ℝ)| / 2 : ℝ) : EReal) ≤
          V.maximalLogarithmicMinimum := by
  let M := V.maximalSlope (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions
  let c : ℝ → ℝ := fun ε =>
    (Module.finrank ℚ K : ℝ) / 2 * Real.log ((Module.finrank K E : ℝ) + ε) +
      ((Module.finrank ℚ K : ℝ) / 2 * Real.log (Module.finrank K E : ℝ) +
        Real.log |(NumberField.discr K : ℝ)| / 2)
  have hc : ContinuousAt c 0 := by
    apply ContinuousAt.add
    · apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.log (continuousAt_const.add continuousAt_id)
      simpa using (Nat.cast_pos.mpr hn : (0 : ℝ) < Module.finrank K E).ne'
    · exact continuousAt_const
  have hc0 : c 0 = (Module.finrank ℚ K : ℝ) * Real.log (Module.finrank K E : ℝ) +
      Real.log |(NumberField.discr K : ℝ)| / 2 := by
    dsimp [c]
    rw [add_zero]
    ring
  have hcoe : Tendsto (fun ε : ℝ => ((-c ε : ℝ) : EReal)) (𝓝[>] 0)
      (𝓝 ((-c 0 : ℝ) : EReal)) :=
    EReal.tendsto_coe.mpr ((hc.tendsto.mono_left nhdsWithin_le_nhds).neg)
  have hadd : ContinuousAt (fun p : EReal × EReal => p.1 + p.2)
      (M, ((-c 0 : ℝ) : EReal)) :=
    EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
  have hlim : Tendsto (fun ε : ℝ => M + ((-c ε : ℝ) : EReal)) (𝓝[>] 0)
      (𝓝 (M + ((-c 0 : ℝ) : EReal))) :=
    hadd.tendsto.comp (tendsto_const_nhds.prodMk_nhds hcoe)
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      M + ((-c ε : ℝ) : EReal) ≤ V.maximalLogarithmicMinimum := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have h := maximalSlope_sub_approximation_error_le_firstMinimum V hU hpure hn hε
    simpa only [M, c, sub_eq_add_neg, ← EReal.coe_neg] using h
  have h := le_of_tendsto hlim hbound
  simpa only [hc0, M, EReal.coe_neg, sub_eq_add_neg] using h

end ArakelovGeometry.NumberFieldPureFirstMinimum
