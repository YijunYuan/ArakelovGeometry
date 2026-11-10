/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Local.Lattice.UnitBallGaugeComparison
import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.ProductFormulaComparison

/-!
# Global impurity on the actual normalized number-field curve

The extended nonnegative weighted sum of the actual completed unit-ball
impurities, including infinite impurity and the zero-dimensional convention.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace ArakelovGeometry.NormFamily

open AdelicStructure ActualPrimeIndexing CompletedUnitBallGauge

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]

variable (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)

/-- The actual local impurity at finite places and zero at infinity. -/
def finiteImpurityProfile (ω : (normalizedNumberFieldAdelicStructure K).Ω) : ℝ := by
  classical
  exact if ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin then
    completedUnitBallImpurity ξ ω else 0

theorem finiteImpurityProfile_nonneg (ω : (normalizedNumberFieldAdelicStructure K).Ω) :
    0 ≤ ξ.finiteImpurityProfile ω := by
  classical
  unfold finiteImpurityProfile
  split_ifs with hω
  · obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
    exact (completedUnitBallImpurity_bounds ξ p).1
  · exact le_rfl

/-- The literal extended weighted sum from source Section 4.4.3. -/
def globalImpurity : ℝ≥0∞ :=
  ∑' ω : {ω : (normalizedNumberFieldAdelicStructure K).Ω //
    ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin},
    ENNReal.ofReal (completedUnitBallImpurity ξ ω.val) *
      (normalizedNumberFieldAdelicStructure K).v {ω.val}

/-- The source weighted sum equals the actual normalized discrete integral. -/
theorem globalImpurity_eq_lintegral : ξ.globalImpurity =
    ∫⁻ ω, ENNReal.ofReal (ξ.finiteImpurityProfile ω)
      ∂(normalizedNumberFieldAdelicStructure K).v := by
  classical
  rw [lintegral_countable']
  unfold globalImpurity
  calc
    _ = ∑' ω : {ω : (normalizedNumberFieldAdelicStructure K).Ω //
        ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin},
        ENNReal.ofReal (ξ.finiteImpurityProfile ω.val) *
          (normalizedNumberFieldAdelicStructure K).v {ω.val} := by
      apply tsum_congr
      intro ω
      simp only [finiteImpurityProfile, ite_eq_left ω.property]
    _ = _ := tsum_subtype_eq_of_support_subset
      (f := fun ω : (normalizedNumberFieldAdelicStructure K).Ω =>
        ENNReal.ofReal (ξ.finiteImpurityProfile ω) *
          (normalizedNumberFieldAdelicStructure K).v {ω})
      (s := (normalizedNumberFieldAdelicStructure K).Ωfin) (by
        intro ω hω
        by_contra hfin
        exact hω (by simp [finiteImpurityProfile, hfin]))

/-- Finite impurity means integrability of its actual nonnegative profile. -/
theorem globalImpurity_ne_top_iff_integrable : ξ.globalImpurity ≠ ⊤ ↔
    Integrable ξ.finiteImpurityProfile (normalizedNumberFieldAdelicStructure K).v := by
  rw [ξ.globalImpurity_eq_lintegral]
  exact lintegral_ofReal_ne_top_iff_integrable
    Measurable.of_discrete.aestronglyMeasurable
    (Filter.Eventually.of_forall ξ.finiteImpurityProfile_nonneg)

/-- Every finite-place atom in the source curve has strictly positive mass. -/
theorem finitePlaceMass_ne_zero (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) :
    (normalizedNumberFieldAdelicStructure K).v {ω} ≠ 0 := by
  obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
  erw [normalizedNumberFieldAdelicStructure_v_singleton (normalizedPrimeParameter p)]
  exact_mod_cast
    (normalizedPlaceValue_finitePlace_localDegree_pos (NumberField.FinitePlace.mk p)).ne'

/-- Every actual local contribution is bounded by the literal global sum. -/
theorem weighted_localImpurity_le_globalImpurity
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) :
    ENNReal.ofReal (completedUnitBallImpurity ξ ω) *
      (normalizedNumberFieldAdelicStructure K).v {ω} ≤ ξ.globalImpurity := by
  unfold globalImpurity
  exact ENNReal.le_tsum (f := fun v : {v : (normalizedNumberFieldAdelicStructure K).Ω //
    v ∈ (normalizedNumberFieldAdelicStructure K).Ωfin} =>
      ENNReal.ofReal (completedUnitBallImpurity ξ v.val) *
        (normalizedNumberFieldAdelicStructure K).v {v.val}) ⟨ω, hω⟩

/-- A genuinely positive finite-place impurity forces positive global impurity. -/
theorem globalImpurity_pos_of_localImpurity_pos
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin)
    (hδ : 0 < completedUnitBallImpurity ξ ω) : 0 < ξ.globalImpurity := by
  apply lt_of_lt_of_le _ (ξ.weighted_localImpurity_le_globalImpurity ω hω)
  exact pos_iff_ne_zero.mpr (mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hδ))
    (finitePlaceMass_ne_zero ω hω))

theorem globalImpurity_eq_zero_iff : ξ.globalImpurity = 0 ↔
    ∀ ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin,
      ∀ z, completedUnitBallGauge ξ ω z = ξ.norm ω z := by
  classical
  unfold globalImpurity
  rw [ENNReal.tsum_eq_zero]
  constructor
  · intro h ω hω
    have hz := h ⟨ω, hω⟩
    have hδ : ENNReal.ofReal (completedUnitBallImpurity ξ ω) = 0 :=
      (mul_eq_zero.mp hz).resolve_right (finitePlaceMass_ne_zero ω hω)
    obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
    apply (completedUnitBallImpurity_eq_zero_iff ξ p).mp
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp hδ)
      (completedUnitBallImpurity_bounds ξ p).1
  · intro h ω
    obtain ⟨p, hp⟩ := exists_normalizedPrimeParameter_eq ω.val ω.property
    have hδ := (completedUnitBallImpurity_eq_zero_iff ξ p).mpr
      (hp ▸ h ω.val ω.property)
    rw [← hp, hδ, ENNReal.ofReal_zero, zero_mul]

theorem globalImpurity_rank_zero [Subsingleton E] : ξ.globalImpurity = 0 := by
  unfold globalImpurity
  apply ENNReal.tsum_eq_zero.mpr
  intro ω
  obtain ⟨p, hp⟩ := exists_normalizedPrimeParameter_eq ω.val ω.property
  rw [← hp]
  rw [completedUnitBallImpurity_rank_zero, ENNReal.ofReal_zero, zero_mul]

end ArakelovGeometry.NormFamily
