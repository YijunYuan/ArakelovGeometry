/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.GeometryOfNumbers.LatticeCount
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # The actual lattice-normalized Haar measure and lattice counting -/

noncomputable section
open Module MeasureTheory MeasureTheory.Measure Bornology
open scoped ENNReal

namespace ArakelovGeometry.GeometryOfNumbers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (μ : Measure E) [IsAddHaarMeasure μ]

/-- Lattice-normalized Haar measure, obtained from the actual additive covolume. -/
def latticeNormalizedMeasure : Measure E := (addCovolume L E μ)⁻¹ • μ

/-- The actual additive covolume is positive and finite; these are conclusions. -/
theorem latticeCovolume_pos_lt_top :
    0 < addCovolume L E μ ∧ addCovolume L E μ < ∞ :=
  ENNReal.toReal_pos_iff.mp (ZLattice.covolume_pos L μ)

/-- The constructed normalized measure is an actual Haar measure. -/
theorem latticeNormalizedMeasure_isAddHaar : IsAddHaarMeasure (latticeNormalizedMeasure L μ) :=
  IsAddHaarMeasure.smul μ
    (ENNReal.inv_ne_zero.mpr (latticeCovolume_pos_lt_top L μ).2.ne)
    (ENNReal.inv_ne_top.mpr (latticeCovolume_pos_lt_top L μ).1.ne')

/-- Every actual fundamental domain has normalized measure one. -/
theorem latticeNormalizedMeasure_fundamentalDomain {F : Set E}
    (hF : IsAddFundamentalDomain L F μ) : latticeNormalizedMeasure L μ F = 1 := by
  let : Countable L := inferInstance
  let : MeasurableVAdd L E := inferInstanceAs (MeasurableVAdd L.toAddSubgroup E)
  let : VAddInvariantMeasure L E μ :=
    inferInstanceAs (VAddInvariantMeasure L.toAddSubgroup E μ)
  rw [latticeNormalizedMeasure, Measure.smul_apply, smul_eq_mul,
    ← hF.covolume_eq_volume μ]
  exact ENNReal.inv_mul_cancel (latticeCovolume_pos_lt_top L μ).1.ne'
    (latticeCovolume_pos_lt_top L μ).2.ne

/-- Actual normalization removes the choice of the initial Haar measure. -/
theorem latticeNormalizedMeasure_eq (ν : Measure E) [IsAddHaarMeasure ν] :
    latticeNormalizedMeasure L μ = latticeNormalizedMeasure L ν := by
  let ρ := latticeNormalizedMeasure L μ
  let σ := latticeNormalizedMeasure L ν
  let : IsAddHaarMeasure ρ := latticeNormalizedMeasure_isAddHaar L μ
  let : IsAddHaarMeasure σ := latticeNormalizedMeasure_isAddHaar L ν
  let b := Module.Free.chooseBasis ℤ L
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)
  have hρ : ρ F = 1 :=
    latticeNormalizedMeasure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain b μ)
  have hσ : σ F = 1 :=
    latticeNormalizedMeasure_fundamentalDomain L ν (ZLattice.isAddFundamentalDomain b ν)
  let c := ρ.addHaarScalarFactor σ
  have heq : ρ = c • σ := isAddLeftInvariant_eq_smul ρ σ
  have hc : (c : ℝ≥0∞) = 1 := by
    have hv := congrArg (fun τ : Measure E => τ F) heq
    simpa only [hρ, Measure.smul_apply, hσ, ENNReal.smul_one] using hv.symm
  have hcR : c = 1 := ENNReal.coe_eq_one.mp hc
  simpa only [hcR, one_smul] using heq

/-- The actual construction is the unique Haar normalization on any actual domain. -/
theorem latticeNormalizedMeasure_eq_of_domain_measure_one
    (ν : Measure E) [IsAddHaarMeasure ν] {F : Set E}
    (hF : IsAddFundamentalDomain L F ν) (hFone : ν F = 1) :
    latticeNormalizedMeasure L μ = ν := by
  let : Countable L := inferInstance
  let : MeasurableVAdd L E := inferInstanceAs (MeasurableVAdd L.toAddSubgroup E)
  let : VAddInvariantMeasure L E ν :=
    inferInstanceAs (VAddInvariantMeasure L.toAddSubgroup E ν)
  rw [latticeNormalizedMeasure_eq L μ ν, latticeNormalizedMeasure,
    hF.covolume_eq_volume ν, hFone]
  simp only [inv_one, one_smul]

/-- Fundamental-domain averaging gives a bound for the actual normalized body volume. -/
theorem latticeNormalizedMeasure_le_two_pow_card {D : Set E}
    (hD : MeasurableSet D) (hbounded : IsBounded D) (hconvex : Convex ℝ D)
    (hsymm : ∀ x ∈ D, -x ∈ D) :
    latticeNormalizedMeasure L μ D ≤ 2 ^ Module.finrank ℝ E *
      (Nat.card {x : L | (x : E) ∈ D} : ℝ≥0∞) := by
  let : Countable L := inferInstance
  let : Countable L.toAddSubgroup := inferInstanceAs (Countable L)
  let : MeasurableVAdd L E := inferInstanceAs (MeasurableVAdd L.toAddSubgroup E)
  let : VAddInvariantMeasure L E μ :=
    inferInstanceAs (VAddInvariantMeasure L.toAddSubgroup E μ)
  let b := Module.Free.chooseBasis ℤ L
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)
  have hF := ZLattice.isAddFundamentalDomain b μ
  have h := LatticeCount.measure_le_two_pow_card_mul_fundamentalDomain
    L.toAddSubgroup hF hD hbounded hconvex hsymm
  change μ D ≤ 2 ^ Module.finrank ℝ E *
    (Nat.card {x : L | (x : E) ∈ D} : ℝ≥0∞) * μ F at h
  rw [← hF.covolume_eq_volume μ] at h
  rw [latticeNormalizedMeasure, Measure.smul_apply, smul_eq_mul]
  calc
    _ ≤ (addCovolume L E μ)⁻¹ *
        (2 ^ Module.finrank ℝ E * (Nat.card {x : L | (x : E) ∈ D} : ℝ≥0∞) *
          addCovolume L E μ) := by gcongr
    _ = _ := by
      rw [mul_left_comm, ENNReal.inv_mul_cancel
        (latticeCovolume_pos_lt_top L μ).1.ne' (latticeCovolume_pos_lt_top L μ).2.ne, mul_one]

/-- Convex frontier nullity is proved for the constructed normalized Haar measure. -/
theorem latticeNormalizedMeasure_interior {C : Set E} (hconvex : Convex ℝ C) :
    latticeNormalizedMeasure L μ (interior C) = latticeNormalizedMeasure L μ C := by
  let : IsAddHaarMeasure (latticeNormalizedMeasure L μ) :=
    latticeNormalizedMeasure_isAddHaar L μ
  exact measure_interior_of_null_frontier
    (hconvex.addHaar_frontier (latticeNormalizedMeasure L μ))

/-- The actual interior lattice points control the whole actual normalized convex volume. -/
theorem latticeNormalizedMeasure_le_two_pow_card_interior {C : Set E}
    (hbounded : IsBounded C) (hconvex : Convex ℝ C) (hsymm : ∀ x ∈ C, -x ∈ C) :
    latticeNormalizedMeasure L μ C ≤ 2 ^ Module.finrank ℝ E *
      (Nat.card {x : L | (x : E) ∈ interior C} : ℝ≥0∞) := by
  have hpre : (Homeomorph.neg E) ⁻¹' C = C := by
    ext x
    change -x ∈ C ↔ x ∈ C
    exact ⟨fun hx => by simpa using hsymm (-x) hx, hsymm x⟩
  have hsymmI (x : E) (hx : x ∈ interior C) : -x ∈ interior C := by
    change x ∈ (Homeomorph.neg E) ⁻¹' interior C
    rw [(Homeomorph.neg E).preimage_interior, hpre]
    exact hx
  rw [← latticeNormalizedMeasure_interior L μ hconvex]
  exact latticeNormalizedMeasure_le_two_pow_card L μ isOpen_interior.measurableSet
    (hbounded.subset interior_subset) hconvex.interior hsymmI

end ArakelovGeometry.GeometryOfNumbers
