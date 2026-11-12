/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Norm.Gauge
public import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Impurity.Basic

/-!
# Actual global impurity and completed-fibre distance

The literal source impurity equals the extended integral of the canonical
distance to the actual lattice-gauge norm family. Its finiteness therefore
supplies the existing domination-transfer theorem with an integrable envelope.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace ArakelovGeometry.NormFamily

open AdelicStructure CompletedUnitBallGauge

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

variable (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
  [hξ : ξ.IsUltrametric]

/-- The actual impurity profile is the canonical completed-fibre distance. -/
theorem finiteImpurityProfile_eq_localDist_latticeGaugeFamily :
    ξ.finiteImpurityProfile = ξ.localDist (ξ.latticeGaugeFamily) := by
  classical
  funext ω
  by_cases hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin
  · rw [finiteImpurityProfile, ite_eq_left hω,
      ξ.latticeGaugeFamily_localDist_finite ω hω]
  · rw [finiteImpurityProfile, ite_eq_right hω,
      ξ.latticeGaugeFamily_localDist_not_finite ω hω]

/-- The source's extended impurity is the literal global distance integral. -/
theorem globalImpurity_eq_lintegral_localDist_latticeGaugeFamily : ξ.globalImpurity =
    ∫⁻ ω, ENNReal.ofReal (ξ.localDist (ξ.latticeGaugeFamily) ω)
      ∂(normalizedNumberFieldAdelicStructure K).v := by
  rw [ξ.globalImpurity_eq_lintegral, ξ.finiteImpurityProfile_eq_localDist_latticeGaugeFamily]

theorem globalImpurity_ne_top_iff_integrable_localDist_latticeGaugeFamily :
    ξ.globalImpurity ≠ ⊤ ↔ Integrable (ξ.localDist (ξ.latticeGaugeFamily))
      (normalizedNumberFieldAdelicStructure K).v := by
  rw [ξ.globalImpurity_ne_top_iff_integrable,
    ξ.finiteImpurityProfile_eq_localDist_latticeGaugeFamily]

/-- On the actual discrete curve, finite impurity is precisely the upper
envelope required for domination transfer. -/
theorem globalImpurity_ne_top_iff_localDist_hasIntegrableUpperBound :
    ξ.globalImpurity ≠ ⊤ ↔
      HasIntegrableUpperBound (ξ.localDist (ξ.latticeGaugeFamily))
        (normalizedNumberFieldAdelicStructure K).v := by
  rw [ξ.globalImpurity_ne_top_iff_integrable_localDist_latticeGaugeFamily]
  constructor
  · exact fun h => (integrable_hasIntegrableBounds h).1
  · intro h
    apply HasIntegrableBounds.integrable (hm := Measurable.of_discrete.aestronglyMeasurable)
    exact ⟨h, 0, integrable_zero _ _ _, Filter.Eventually.of_forall
      (fun ω ↦ ξ.localDist_nonneg (ξ.latticeGaugeFamily) ω)⟩

/-- Zero source impurity identifies the entire actual gauge family. -/
theorem globalImpurity_eq_zero_iff_latticeGaugeFamily_eq :
    ξ.globalImpurity = 0 ↔ ξ.latticeGaugeFamily = ξ := by
  rw [ξ.globalImpurity_eq_zero_iff]
  constructor
  · intro h
    apply NormFamily.ext
    intro ω z
    by_cases hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin
    · rw [ξ.latticeGaugeFamily_norm_finite ω hω]
      exact h ω hω z
    · rw [ξ.latticeGaugeFamily_norm_not_finite ω hω]
  · intro h ω hω z
    rw [← ξ.latticeGaugeFamily_norm_finite ω hω, h]

/-- Replacing finite norms by the intrinsic gauges removes all impurity. -/
theorem latticeGaugeFamily_globalImpurity_eq_zero :
    (ξ.latticeGaugeFamily).globalImpurity = 0 := by
  apply ((ξ.latticeGaugeFamily).globalImpurity_eq_zero_iff).mpr
  intro ω hω z
  unfold completedUnitBallGauge
  rw [ξ.latticeGaugeFamily_completedUnitBall_eq ω hω]
  exact (ξ.latticeGaugeFamily_norm_finite ω hω z).symm

/-- Finite actual impurity transfers domination from the produced gauge family. -/
theorem isDominated_of_latticeGaugeFamily_of_globalImpurity_ne_top
    [hg : (ξ.latticeGaugeFamily).IsDominated] (hσ : ξ.globalImpurity ≠ ⊤) :
    ξ.IsDominated := by
  apply hg.of_localDist
  have hd := (ξ.globalImpurity_ne_top_iff_localDist_hasIntegrableUpperBound).mp hσ
  exact hd.congr (Filter.Eventually.of_forall fun ω => ξ.localDist_comm _ ω)

/-- Finite impurity likewise transfers domination to the produced gauge family. -/
theorem IsDominated.latticeGaugeFamily_of_globalImpurity_ne_top
    (hd : ξ.IsDominated) (hσ : ξ.globalImpurity ≠ ⊤) :
    (ξ.latticeGaugeFamily).IsDominated :=
  hd.of_localDist ((ξ.globalImpurity_ne_top_iff_localDist_hasIntegrableUpperBound).mp hσ)

end ArakelovGeometry.NormFamily
