/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic
public import ArakelovGeometry.NumberTheory.NumberField.Covolume.Degree
public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Coherence.Criteria
public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Coherence.FiniteGeneration
public import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Impurity.Minima

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.NumberTheory.NumberField.Lattice.Full.Replacement
import ArakelovGeometry.NumberTheory.NumberField.Lattice.Line.FullLatticeIndex
import ArakelovGeometry.NumberTheory.NumberField.Lattice.Norm.GaugeDomination
import ArakelovGeometry.NumberTheory.NumberField.Minima.HermitianFirst
import ArakelovGeometry.NumberTheory.NumberField.Minima.PureFirst
import ArakelovGeometry.NumberTheory.NumberField.Minima.SlopeComparison
import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Impurity.Distance
import Mathlib.Topology.Sheaves.Init

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

/-- The canonical adelic replacement is the full-lattice bundle of the literal finite
global ball, with finite generation and full span produced from the original bundle. -/
theorem latticeGauge_eq_fullLatticeBundle
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K))
    [hU : V.toNormFamily.IsUltrametric] [hc : V.toNormFamily.HasFiniteNormExceptions] :
    V.numberFieldLatticeGauge =
      fullLatticeAdelicBundle (V.toNormFamily.globalUnitBallModule)
        (V.isDominated.fg_normalizedGlobalUnitBallModule hU)
        ((NormFamily.hasFiniteNormExceptions_iff_span_normalizedGlobalUnitBall_eq_top
          V.toNormFamily).mp hc) V.toNormFamily := by
  apply AdelicVectorBundle.ext
    (hξ := V.numberFieldLatticeGauge.toIsAdelic)
    (hη := (fullLatticeAdelicBundle V.toNormFamily.globalUnitBallModule
      (V.isDominated.fg_normalizedGlobalUnitBallModule hU)
      ((NormFamily.hasFiniteNormExceptions_iff_span_normalizedGlobalUnitBall_eq_top
        V.toNormFamily).mp hc) V.toNormFamily).toIsAdelic)
  exact hc.latticeGaugeFamily_eq_fullLatticeGaugeFamily V.toNormFamily hU
    (V.isDominated.fg_normalizedGlobalUnitBallModule hU)

/-- Purity of the actual produced replacement is inherited from its literal full-lattice
gauge, rather than supplied as a model hypothesis. -/
theorem latticeGauge_isPure
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K))
    [hU : V.toNormFamily.IsUltrametric] [hc : V.toNormFamily.HasFiniteNormExceptions] :
    (V.numberFieldLatticeGauge).toNormFamily.IsPureAtFinitePlaces := by
  rw [latticeGauge_eq_fullLatticeBundle V]
  exact fullLatticeGaugeFamily_isPureAtFinitePlaces _ _ _ _

/-- The same actual replacement preserves the original Hermitian infinite norms. -/
theorem latticeGauge_isHermitian
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K))
    [hU : V.toNormFamily.IsUltrametric] [hc : V.toNormFamily.HasFiniteNormExceptions]
    [hH : V.toNormFamily.IsHermitian] :
    (V.numberFieldLatticeGauge).toNormFamily.IsHermitian
      := by
  rw [latticeGauge_eq_fullLatticeBundle V]
  exact fullLatticeGaugeFamily_isHermitian _ _ _ _

/-- Intrinsic finite unit-ball gauges increase the original norms by at most their
actual completed-fibre distance, and agree at infinity. -/
theorem latticeGauge_norm_comparison
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K))
    [hU : V.toNormFamily.IsUltrametric] [hc : V.toNormFamily.HasFiniteNormExceptions]
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (z : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] V) :
    V.toNormFamily.norm ω z ≤ (V.numberFieldLatticeGauge).toNormFamily.norm ω z ∧
      (V.numberFieldLatticeGauge).toNormFamily.norm ω z ≤
        Real.exp (V.toNormFamily.localDist
          (V.numberFieldLatticeGauge).toNormFamily ω) * V.toNormFamily.norm ω z := by
  refine ⟨?_, ?_⟩
  · change V.toNormFamily.norm ω z ≤ (V.toNormFamily.latticeGaugeFamily).norm ω z
    by_cases hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin
    · obtain ⟨p, rfl⟩ := ActualPrimeIndexing.exists_normalizedPrimeParameter_eq ω hω
      rw [V.toNormFamily.latticeGaugeFamily_norm_finite _
        (ActualPrimeIndexing.normalizedPrimeParameter_mem_fin p)]
      exact (completedUnitBallGauge_comparison V.toNormFamily p z).1
    · rw [V.toNormFamily.latticeGaugeFamily_norm_not_finite ω hω]
  · exact ((V.toNormFamily.localDist_le_iff
      (V.numberFieldLatticeGauge).toNormFamily ω
        (V.toNormFamily.localDist_nonneg _ ω)).mp le_rfl z).2

/-- The produced replacement loses no ordinary minimum in the reverse direction, while
its actual maximal slope loses at most the literal finite source impurity. -/
theorem latticeGauge_minima_and_maximalSlope
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K))
    [hU : V.toNormFamily.IsUltrametric] [hc : V.toNormFamily.HasFiniteNormExceptions] :
    (∀ i : ℕ, (V.numberFieldLatticeGauge).logarithmicMinimum i ≤
      V.logarithmicMinimum i) ∧
    V.maximalSlope -
      (V.toNormFamily.globalImpurity.toReal : EReal) ≤
        (V.numberFieldLatticeGauge).maximalSlope
          := by
  let Q := V.numberFieldLatticeGauge
  let δ := V.toNormFamily.localDist Q.toNormFamily
  have hσ := V.isDominated.globalImpurity_ne_top V.toNormFamily hc
  have hδ : Integrable δ (normalizedNumberFieldAdelicStructure K).v :=
    (V.toNormFamily.globalImpurity_ne_top_iff_integrable_localDist_latticeGaugeFamily).mp hσ
  have hn := latticeGauge_norm_comparison V
  have hm := logarithmicMinimum_comparison V Q.toNormFamily (hQ := Q.toIsAdelic) (fun _ => 0) δ
    (integrable_zero _ ℝ _) hδ
    (by simpa only [Real.exp_zero, one_mul] using fun ω z => (hn ω z).1)
    (fun ω z => (hn ω z).2)
  have hs := maximalSlope_sub_integral_le V Q.toNormFamily (hQ := Q.toIsAdelic) δ hδ
    (fun ω z => (hn ω z).2)
  refine ⟨fun i => ?_, ?_⟩
  · simpa only [integral_zero, EReal.coe_zero, sub_zero] using (hm i).2
  · dsimp only [δ, Q] at hs
    rw [V.toNormFamily.integral_localDist_latticeGaugeFamily_eq_globalImpurity_toReal
       hσ] at hs
    exact hs

/-- The actual Hermitian first minimum with its literal source impurity cost.
Finite ultrametricity and coherence are explicit; all replacement properties are proved. -/
theorem maximalSlope_sub_impurity_hermitian_error_le_firstMinimum
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K))
    [hU : V.toNormFamily.IsUltrametric] [hc : V.toNormFamily.HasFiniteNormExceptions]
    [hH : V.toNormFamily.IsHermitian]
    (hn : 0 < Module.finrank K V) :
    V.maximalSlope -
      (V.toNormFamily.globalImpurity.toReal : EReal) -
        (((Module.finrank ℚ K : ℝ) / 2 * Real.log (Module.finrank K V : ℝ) +
          Real.log |(NumberField.discr K : ℝ)| / 2 : ℝ) : EReal) ≤
            V.maximalLogarithmicMinimum := by
  have htransfer := latticeGauge_minima_and_maximalSlope V
  have hpure := latticeGauge_isPure V
  have hherm := latticeGauge_isHermitian V
  have hmin := NumberFieldHermitianFirstMinimum.maximalSlope_sub_error_le_firstMinimum
    (V.numberFieldLatticeGauge) (hV := hherm) (hpure := hpure) hn
  exact (EReal.sub_le_sub htransfer.2 le_rfl).trans (hmin.trans (htransfer.1 1))

/-- The actual first minimum for arbitrary infinite norms, with its proved finite impurity
cost and the accepted pure-finite error. No finite-value hypotheses are imposed. -/
theorem maximalSlope_sub_impurity_error_le_firstMinimum
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K))
    [hU : V.toNormFamily.IsUltrametric] [hc : V.toNormFamily.HasFiniteNormExceptions]
    (hn : 0 < Module.finrank K V) :
    V.maximalSlope -
      (V.toNormFamily.globalImpurity.toReal : EReal) -
        (((Module.finrank ℚ K : ℝ) * Real.log (Module.finrank K V : ℝ) +
          Real.log |(NumberField.discr K : ℝ)| / 2 : ℝ) : EReal) ≤
            V.maximalLogarithmicMinimum := by
  have htransfer := latticeGauge_minima_and_maximalSlope V
  have hpure := latticeGauge_isPure V
  have hmin := NumberFieldPureFirstMinimum.maximalSlope_sub_error_le_firstMinimum
    (V.numberFieldLatticeGauge)
    (hU := (V.toNormFamily.latticeGaugeFamily_isUltrametric)) (hpure := hpure) hn
  exact (EReal.sub_le_sub htransfer.2 le_rfl).trans (hmin.trans (htransfer.1 1))

end ArakelovGeometry.NumberFieldImpureFirstMinimum
