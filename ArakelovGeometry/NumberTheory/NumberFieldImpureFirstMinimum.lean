/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldFullLatticeReplacement
public import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldImpurityMinima
public import ArakelovGeometry.NumberTheory.NumberFieldFullLatticeLineIndex
public import ArakelovGeometry.NumberTheory.NumberFieldMinimumSlopeComparison
public import ArakelovGeometry.NumberTheory.NumberFieldPureFirstMinimum

/-! # The actual number-field first minimum with its finite impurity cost -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldImpureFirstMinimum

open AdelicStructure NumberFieldFullLattice NumberFieldMinimumSlopeComparison
  CompletedUnitBallGauge

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

attribute [local instance] normalizedNumberFieldAdelicStructure_isProper

local instance impureFirstMinimumDiscreteMeasurable :
    DiscreteMeasurableSpace (normalizedNumberFieldAdelicStructure K).Ω :=
  inferInstanceAs
    (DiscreteMeasurableSpace {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})

/-- The canonical adelic replacement is the full-lattice bundle of the literal finite
global ball, with finite generation and full span produced from the original bundle. -/
theorem latticeGauge_eq_fullLatticeBundle
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hU : V.toNormFamily.IsUltrametric) (hc : V.toNormFamily.HasFiniteNormExceptions) :
    V.numberFieldLatticeGauge hU hc =
      fullLatticeAdelicBundle (V.toNormFamily.globalUnitBallModule hU)
        (V.isDominated.fg_normalizedGlobalUnitBallModule hU)
        ((NormFamily.hasFiniteNormExceptions_iff_span_normalizedGlobalUnitBall_eq_top
          V.toNormFamily hU).mp hc) V.toNormFamily := by
  apply AdelicVectorBundle.ext
  exact hc.latticeGaugeFamily_eq_fullLatticeGaugeFamily V.toNormFamily hU
    (V.isDominated.fg_normalizedGlobalUnitBallModule hU)

/-- Purity of the actual produced replacement is inherited from its literal full-lattice
gauge, rather than supplied as a model hypothesis. -/
theorem latticeGauge_isPure
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hU : V.toNormFamily.IsUltrametric) (hc : V.toNormFamily.HasFiniteNormExceptions) :
    (V.numberFieldLatticeGauge hU hc).toNormFamily.IsPureAtFinitePlaces := by
  rw [latticeGauge_eq_fullLatticeBundle V hU hc]
  exact fullLatticeGaugeFamily_isPureAtFinitePlaces _ _ _ _

/-- The same actual replacement preserves the original Hermitian infinite norms. -/
theorem latticeGauge_isHermitian
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hU : V.toNormFamily.IsUltrametric) (hc : V.toNormFamily.HasFiniteNormExceptions)
    (hH : V.toNormFamily.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    (V.numberFieldLatticeGauge hU hc).toNormFamily.IsHermitian
      normalizedNumberFieldArchimedeanCompletions := by
  rw [latticeGauge_eq_fullLatticeBundle V hU hc]
  exact fullLatticeGaugeFamily_isHermitian _ _ _ _ hH

/-- Intrinsic finite unit-ball gauges increase the original norms by at most their
actual completed-fibre distance, and agree at infinity. -/
theorem latticeGauge_norm_comparison
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hU : V.toNormFamily.IsUltrametric) (hc : V.toNormFamily.HasFiniteNormExceptions)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (z : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] E) :
    V.toNormFamily.norm ω z ≤ (V.numberFieldLatticeGauge hU hc).toNormFamily.norm ω z ∧
      (V.numberFieldLatticeGauge hU hc).toNormFamily.norm ω z ≤
        Real.exp (V.toNormFamily.localDist
          (V.numberFieldLatticeGauge hU hc).toNormFamily ω) * V.toNormFamily.norm ω z := by
  refine ⟨?_, ?_⟩
  · change V.toNormFamily.norm ω z ≤ (V.toNormFamily.latticeGaugeFamily hU).norm ω z
    by_cases hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin
    · obtain ⟨p, rfl⟩ := ActualPrimeIndexing.exists_normalizedPrimeParameter_eq ω hω
      rw [V.toNormFamily.latticeGaugeFamily_norm_finite hU _
        (ActualPrimeIndexing.normalizedPrimeParameter_mem_fin p)]
      exact (completedUnitBallGauge_comparison V.toNormFamily p z).1
    · rw [V.toNormFamily.latticeGaugeFamily_norm_not_finite hU ω hω]
  · exact ((V.toNormFamily.localDist_le_iff
      (V.numberFieldLatticeGauge hU hc).toNormFamily ω
        (V.toNormFamily.localDist_nonneg _ ω)).mp le_rfl z).2

/-- The produced replacement loses no ordinary minimum in the reverse direction, while
its actual maximal slope loses at most the literal finite source impurity. -/
theorem latticeGauge_minima_and_maximalSlope
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hU : V.toNormFamily.IsUltrametric) (hc : V.toNormFamily.HasFiniteNormExceptions) :
    (∀ i : ℕ, (V.numberFieldLatticeGauge hU hc).logarithmicMinimum i ≤
      V.logarithmicMinimum i) ∧
    V.maximalSlope (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions -
      (V.toNormFamily.globalImpurity.toReal : EReal) ≤
        (V.numberFieldLatticeGauge hU hc).maximalSlope (Or.inl inferInstance)
          normalizedNumberFieldArchimedeanCompletions := by
  let Q := V.numberFieldLatticeGauge hU hc
  let δ := V.toNormFamily.localDist Q.toNormFamily
  have hσ := V.isDominated.globalImpurity_ne_top V.toNormFamily hU hc
  have hδ : Integrable δ (normalizedNumberFieldAdelicStructure K).v :=
    (V.toNormFamily.globalImpurity_ne_top_iff_integrable_localDist_latticeGaugeFamily hU).mp hσ
  have hn := latticeGauge_norm_comparison V hU hc
  have hm := logarithmicMinimum_comparison V Q (fun _ => 0) δ
    (integrable_zero _ ℝ _) hδ
    (by simpa only [Real.exp_zero, one_mul] using fun ω z => (hn ω z).1)
    (fun ω z => (hn ω z).2)
  have hs := maximalSlope_sub_integral_le V Q δ hδ (fun ω z => (hn ω z).2)
  refine ⟨fun i => ?_, ?_⟩
  · simpa only [integral_zero, EReal.coe_zero, sub_zero] using (hm i).2
  · dsimp only [δ, Q] at hs
    rw [AdelicVectorBundle.numberFieldLatticeGauge_toNormFamily,
      V.toNormFamily.integral_localDist_latticeGaugeFamily_eq_globalImpurity_toReal
      hU hσ] at hs
    exact hs

/-- The actual Hermitian first minimum with its literal source impurity cost.
Finite ultrametricity and coherence are explicit; all replacement properties are proved. -/
theorem maximalSlope_sub_impurity_hermitian_error_le_firstMinimum
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hU : V.toNormFamily.IsUltrametric) (hc : V.toNormFamily.HasFiniteNormExceptions)
    (hH : V.toNormFamily.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (hn : 0 < Module.finrank K E) :
    V.maximalSlope (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions -
      (V.toNormFamily.globalImpurity.toReal : EReal) -
        (((Module.finrank ℚ K : ℝ) / 2 * Real.log (Module.finrank K E : ℝ) +
          Real.log |(NumberField.discr K : ℝ)| / 2 : ℝ) : EReal) ≤
            V.maximalLogarithmicMinimum := by
  have htransfer := latticeGauge_minima_and_maximalSlope V hU hc
  have hpure := latticeGauge_isPure V hU hc
  have hherm := latticeGauge_isHermitian V hU hc hH
  have hmin := NumberFieldHermitianFirstMinimum.maximalSlope_sub_error_le_firstMinimum
    (V.numberFieldLatticeGauge hU hc) hherm hpure hn
  exact (EReal.sub_le_sub htransfer.2 le_rfl).trans (hmin.trans (htransfer.1 1))

/-- The actual first minimum for arbitrary infinite norms, with its proved finite impurity
cost and the accepted pure-finite error. No finite-value hypotheses are imposed. -/
theorem maximalSlope_sub_impurity_error_le_firstMinimum
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hU : V.toNormFamily.IsUltrametric) (hc : V.toNormFamily.HasFiniteNormExceptions)
    (hn : 0 < Module.finrank K E) :
    V.maximalSlope (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions -
      (V.toNormFamily.globalImpurity.toReal : EReal) -
        (((Module.finrank ℚ K : ℝ) * Real.log (Module.finrank K E : ℝ) +
          Real.log |(NumberField.discr K : ℝ)| / 2 : ℝ) : EReal) ≤
            V.maximalLogarithmicMinimum := by
  have htransfer := latticeGauge_minima_and_maximalSlope V hU hc
  have hpure := latticeGauge_isPure V hU hc
  have hmin := NumberFieldPureFirstMinimum.maximalSlope_sub_error_le_firstMinimum
    (V.numberFieldLatticeGauge hU hc)
    (V.toNormFamily.latticeGaugeFamily_isUltrametric hU) hpure hn
  exact (EReal.sub_le_sub htransfer.2 le_rfl).trans (hmin.trans (htransfer.1 1))

end ArakelovGeometry.NumberFieldImpureFirstMinimum
