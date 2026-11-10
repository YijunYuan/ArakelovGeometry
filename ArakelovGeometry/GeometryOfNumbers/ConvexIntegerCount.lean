/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.GeometryOfNumbers.IntegerFiberCount
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.Compact

/-! # Integer points of actual compact convex subsets of the real line -/

noncomputable section

open Set MeasureTheory

namespace ArakelovGeometry.ConvexIntegerCount

/-- A nonempty compact convex subset is exactly its own endpoint interval. -/
theorem eq_Icc_sInf_sSup {S : Set ℝ} (hS : IsCompact S) (hcS : Convex ℝ S)
    (hne : S.Nonempty) : S = Icc (sInf S) (sSup S) :=
  eq_Icc_of_connected_compact (hcS.isConnected hne) hS

/-- The actual Lebesgue measure is the finite endpoint length embedded in `ℝ≥0∞`. -/
theorem volume_eq_ofReal_sSup_sub_sInf {S : Set ℝ} (hS : IsCompact S)
    (hcS : Convex ℝ S) (hne : S.Nonempty) :
    volume S = ENNReal.ofReal (sSup S - sInf S) := by
  calc
    volume S = volume (Icc (sInf S) (sSup S)) :=
      congrArg volume (eq_Icc_sInf_sSup hS hcS hne)
    _ = ENNReal.ofReal (sSup S - sInf S) := Real.volume_Icc

/-- The ordinary Lebesgue length of the original nonempty set is its endpoint difference. -/
theorem volume_toReal_eq_sSup_sub_sInf {S : Set ℝ} (hS : IsCompact S)
    (hcS : Convex ℝ S) (hne : S.Nonempty) :
    (volume S).toReal = sSup S - sInf S := by
  have hab : sInf S ≤ sSup S := csInf_le_csSup hne hS.bddBelow hS.bddAbove
  rw [volume_eq_ofReal_sSup_sub_sInf hS hcS hne,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

/-- Compactness alone produces finiteness of the literal translated integer fibre. -/
theorem finite_integer_fiber {S : Set ℝ} (hS : IsCompact S) (x : ℝ) :
    {k : ℤ | (k : ℝ) + x ∈ S}.Finite := by
  obtain ⟨a, ha⟩ := hS.bddBelow
  obtain ⟨b, hb⟩ := hS.bddAbove
  exact (IntegerFiberCount.finite_integer_fiber a b x).subset fun k hk => ⟨ha hk, hb hk⟩

/-- The literal integer points of an actual compact real set are finite. -/
theorem finite_integer_points {S : Set ℝ} (hS : IsCompact S) :
    {k : ℤ | (k : ℝ) ∈ S}.Finite := by
  simpa only [add_zero] using finite_integer_fiber hS 0

/-- The translated integer count is bounded by the actual Lebesgue volume, including emptiness. -/
theorem natCard_integer_fiber_le_volume_add_one {S : Set ℝ} (hS : IsCompact S)
    (hcS : Convex ℝ S) (x : ℝ) :
    (Nat.card {k : ℤ | (k : ℝ) + x ∈ S} : ℝ) ≤ (volume S).toReal + 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hab : sInf S ≤ sSup S := csInf_le_csSup hne hS.bddBelow hS.bddAbove
    have hset : {k : ℤ | (k : ℝ) + x ∈ S} =
        {k : ℤ | sInf S ≤ (k : ℝ) + x ∧ (k : ℝ) + x ≤ sSup S} := by
      ext k
      exact Set.ext_iff.mp (eq_Icc_sInf_sSup hS hcS hne) ((k : ℝ) + x)
    rw [hset, volume_toReal_eq_sSup_sub_sInf hS hcS hne]
    exact IntegerFiberCount.natCard_integer_fiber_le_length_add_one hab

/-- The original, unshifted integer subtype is controlled by the original set's volume. -/
theorem natCard_integer_points_le_volume_add_one {S : Set ℝ} (hS : IsCompact S)
    (hcS : Convex ℝ S) :
    (Nat.card {k : ℤ | (k : ℝ) ∈ S} : ℝ) ≤ (volume S).toReal + 1 := by
  simpa only [add_zero] using natCard_integer_fiber_le_volume_add_one hS hcS 0

/-- A length majorant at least two gives the precise factor used in lattice induction. -/
theorem natCard_integer_fiber_le_three_halves_mul {S : Set ℝ} (hS : IsCompact S)
    (hcS : Convex ℝ S) (x : ℝ) {ℓ : ℝ} (hlen : (volume S).toReal ≤ ℓ) (hℓ : 2 ≤ ℓ) :
    (Nat.card {k : ℤ | (k : ℝ) + x ∈ S} : ℝ) ≤ (3 / 2 : ℝ) * ℓ := by
  have h := natCard_integer_fiber_le_volume_add_one hS hcS x
  linarith

/-- The same exact factor for the literal integer points of the compact convex set. -/
theorem natCard_integer_points_le_three_halves_mul {S : Set ℝ} (hS : IsCompact S)
    (hcS : Convex ℝ S) {ℓ : ℝ} (hlen : (volume S).toReal ≤ ℓ) (hℓ : 2 ≤ ℓ) :
    (Nat.card {k : ℤ | (k : ℝ) ∈ S} : ℝ) ≤ (3 / 2 : ℝ) * ℓ := by
  simpa only [add_zero] using natCard_integer_fiber_le_three_halves_mul hS hcS 0 hlen hℓ

end ArakelovGeometry.ConvexIntegerCount
