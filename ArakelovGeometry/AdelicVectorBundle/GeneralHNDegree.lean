/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.GeneralHNOrdered
import ArakelovGeometry.AdelicVectorBundle.GeneralHNRestriction
import ArakelovGeometry.AdelicVectorBundle.DegreeFlag
import ArakelovGeometry.AdelicVectorBundle.PositiveDegree
import ArakelovGeometry.AdelicVectorBundle.GeneralHNFlag
import ArakelovGeometry.AdelicVectorBundle.GeneralHNMeasure

/-!
# Actual general HN degree lower bounds

Minimal slopes of actual restricted bundles bound the degrees of their
actual quotients. Summing uses the accepted genuine flag degree inequality.
-/

open MeasureTheory
open scoped BigOperators

namespace ArakelovGeometry

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace AdelicVectorBundle

variable [S.IsProper] (V : AdelicVectorBundle S E)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)


/-- An actual quotient degree is bounded below by its rank times any real
lower bound on the actual source minimum; the zero quotient contributes zero. -/
theorem degree_quotient_ge_rank_mul_of_le_minimalSlope (U : Submodule K E) (b : ℝ)
    (hb : (b : EReal) ≤ V.minimalSlope hS hN) :
    (Module.finrank K (E ⧸ U) : ℝ) * b ≤ (V.quotientOfMeasurableBase U hS).degree hS hN := by
  let Q := V.quotientOfMeasurableBase U hS
  by_cases hr : Module.finrank K (E ⧸ U) = 0
  · rw [Q.degree_eq_zero_of_finrank_eq_zero hS hN hr, hr, Nat.cast_zero, zero_mul]
  · have hmean := EReal.coe_le_coe_iff.mp
      (hb.trans (V.minimalSlope_le_slope_quotient U (Nat.pos_of_ne_zero hr) hS hN))
    rw [Q.degree_eq_rank_mul_slope hS hN]
    exact mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg _)

/-- Actual consecutive quotient minima feed the genuine degree inequality
for a finite restricted flag, with repeated terms and an empty flag included. -/
theorem sum_rank_mul_le_degree_restrict_of_le_minimalSlope_flag {n : ℕ}
    (F : Fin (n + 1) → Submodule K E) (hF : Monotone F) (hzero : F 0 = ⊥)
    (b : Fin n → ℝ)
    (hb : ∀ i, (b i : EReal) ≤ (V.restrictOfMeasurableBase (F i.succ) hS).minimalSlope
      hS hN) :
    (∑ i : Fin n, (Module.finrank K
      (F i.succ ⧸ (F i.castSucc).comap (F i.succ).subtype) : ℝ) * b i) ≤
        (V.restrictOfMeasurableBase (F (Fin.last n)) hS).degree hS hN := by
  apply le_trans _ (V.sum_flagQuotient_degree_le_restrict F hF hzero hS hN)
  apply Finset.sum_le_sum
  intro i _
  exact degree_quotient_ge_rank_mul_of_le_minimalSlope
    (V.restrictOfMeasurableBase (F i.succ) hS) hS hN
      ((F i.castSucc).comap (F i.succ).subtype) (b i) (hb i)

/-- The actual full flag degree lower bound from its restricted minima. -/
theorem sum_rank_mul_le_degree_of_le_minimalSlope_flag {n : ℕ}
    (F : Fin (n + 1) → Submodule K E) (hF : Monotone F) (hzero : F 0 = ⊥)
    (htop : F (Fin.last n) = ⊤) (b : Fin n → ℝ)
    (hb : ∀ i, (b i : EReal) ≤ (V.restrictOfMeasurableBase (F i.succ) hS).minimalSlope
      hS hN) :
    (∑ i : Fin n, (Module.finrank K
      (F i.succ ⧸ (F i.castSucc).comap (F i.succ).subtype) : ℝ) * b i) ≤
        V.degree hS hN := by
  calc
    _ ≤ (V.restrictOfMeasurableBase (F (Fin.last n)) hS).degree hS hN :=
      V.sum_rank_mul_le_degree_restrict_of_le_minimalSlope_flag hS hN F hF hzero b hb
    _ = V.degree hS hN := by rw [htop, V.degree_restrict_top hS hN]

/-- The actual threshold's restricted degree dominates threshold times its
true rank; no ordinary or modified slope equality is assumed. -/
theorem rank_mul_le_degree_restrict_generalHNFiltration (t : ℝ) :
    (Module.finrank K (V.generalHNFiltration hS hN t) : ℝ) * t ≤
      (V.restrictOfMeasurableBase (V.generalHNFiltration hS hN t) hS).degree hS hN := by
  let U := V.generalHNFiltration hS hN t
  let R := V.restrictOfMeasurableBase U hS
  by_cases hr : Module.finrank K U = 0
  · rw [R.degree_eq_zero_of_finrank_eq_zero hS hN hr, hr, Nat.cast_zero, zero_mul]
  · have hmean := EReal.coe_le_coe_iff.mp
      ((V.le_minimalSlope_restrict_generalHNFiltration hS hN t).trans
        (R.minimalSlope_le_slope hS hN (Nat.pos_of_ne_zero hr)))
    rw [R.degree_eq_rank_mul_slope hS hN]
    exact mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg _)

/-- Positive degree includes the actual threshold subspace, so it dominates
threshold times that actual rank, including rank zero. -/
theorem rank_mul_le_positiveDegree_generalHNFiltration (t : ℝ) :
    ((Module.finrank K (V.generalHNFiltration hS hN t) : ℝ) * t : ℝ) ≤
      V.positiveDegree hS hN :=
  (EReal.coe_le_coe (V.rank_mul_le_degree_restrict_generalHNFiltration hS hN t)).trans
    (V.degree_restrict_le_positiveDegree hS hN (V.generalHNFiltration hS hN t))

/-- The intrinsic ordered slopes of an actual threshold term are precisely
its retained ambient prefix. Canonical completed inclusions and the actual
intrinsic filtration identity are used in both directions. -/
theorem generalHNOrderedSlope_restrict_term_eq (t : ℝ)
    (j : Fin (Module.finrank K (V.generalHNFiltration hS hN t))) :
    (V.restrictOfMeasurableBase (V.generalHNFiltration hS hN t) hS).generalHNOrderedSlope
      hS hN j = V.generalHNOrderedSlope hS hN
        (j.castLE (V.generalHNFiltration hS hN t).finrank_le) := by
  let U := V.generalHNFiltration hS hN t
  let R := V.restrictOfMeasurableBase U hS
  let k := j.castLE U.finrank_le
  let μ := V.generalHNOrderedSlope hS hN k
  have htμ : t ≤ μ :=
    (V.le_generalHNOrderedSlope_iff_lt_filtration_finrank hS hN t k).mpr j.isLt
  have heq := V.map_generalHNFiltration_restrict_term_eq hS hN t μ htμ
  have hm := Submodule.finrank_map_le U.subtype (R.generalHNFiltration hS hN μ)
  rw [heq] at hm
  have hjμ := V.lt_finrank_generalHNFiltration_orderedSlope hS hN k
  apply le_antisymm (V.generalHNOrderedSlope_restrict_le hS hN U j)
  exact (R.le_generalHNOrderedSlope_iff_lt_filtration_finrank hS hN μ j).mpr
    (hjμ.trans_le hm)

/-- The genuine ordered sum of the threshold-zero restricted bundle is
exactly the sum of all ambient positive parts, including an empty prefix. -/
theorem sum_generalHNOrderedSlope_restrict_zero_eq_sum_positive :
    (∑ j : Fin (Module.finrank K (V.generalHNFiltration hS hN 0)),
      (V.restrictOfMeasurableBase (V.generalHNFiltration hS hN 0) hS).generalHNOrderedSlope
        hS hN j) = ∑ j : Fin (Module.finrank K E), max (V.generalHNOrderedSlope hS hN j) 0 := by
  classical
  let U := V.generalHNFiltration hS hN 0
  let μ := V.generalHNOrderedSlope hS hN
  let J := Finset.univ.filter (fun j : Fin (Module.finrank K E) => j.val < Module.finrank K U)
  have hcut (j : Fin (Module.finrank K E)) :
      0 ≤ μ j ↔ j.val < Module.finrank K U :=
    V.le_generalHNOrderedSlope_iff_lt_filtration_finrank hS hN 0 j
  calc
    _ = ∑ j : Fin (Module.finrank K U), μ (j.castLE U.finrank_le) := by
      apply Finset.sum_congr rfl
      intro j _
      exact V.generalHNOrderedSlope_restrict_term_eq hS hN 0 j
    _ = ∑ j ∈ J, μ j := by
      apply Finset.sum_bij (fun j _ => j.castLE U.finrank_le)
      · intro j _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩
      · intro j _ k _ hjk
        exact Fin.ext (congrArg (fun x : Fin (Module.finrank K E) => x.val) hjk)
      · intro j hj
        have hp := (Finset.mem_filter.mp hj).2
        exact ⟨⟨j.val, hp⟩, Finset.mem_univ _, Fin.ext rfl⟩
      · intro j _
        rfl
    _ = ∑ j ∈ J, max (μ j) 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (max_eq_left ((hcut j).mpr (Finset.mem_filter.mp hj).2)).symm
    _ = ∑ j : Fin (Module.finrank K E), max (μ j) 0 := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j _ hj
      have hp : ¬ j.val < Module.finrank K U := by
        simpa only [J, Finset.mem_filter, Finset.mem_univ, true_and] using hj
      exact max_eq_right (le_of_not_ge (fun h => hp ((hcut j).mp h)))

/-- The ordinary degree dominates the full sum of actual general ordered
slopes. The actual strict flag is produced from the filtration; each true
factor degree is bounded by its actual source minimum, and the actual
rank-block sum identifies the total, without Hermitianity. -/
theorem sum_generalHNOrderedSlope_le_degree :
    (∑ j : Fin (Module.finrank K E), V.generalHNOrderedSlope hS hN j) ≤
      V.degree hS hN := by
  obtain ⟨n, U, b, hU, hz, ht, _, _, _, _, _, _, _, hmin, hsum⟩ :=
    V.exists_generalHNFlag_orderedSlope_sum hS hN
  calc
    _ = ∑ i : Fin n, (Module.finrank K
        (U i.succ ⧸ (U i.castSucc).comap (U i.succ).subtype) : ℝ) * b i :=
      hsum (fun x ↦ x)
    _ ≤ V.degree hS hN :=
      V.sum_rank_mul_le_degree_of_le_minimalSlope_flag hS hN U hU.monotone hz ht b
        (fun i ↦ (hmin i).ge)

/-- Positive degree dominates the full sum of positive parts of the actual
ordered slopes. Apply the genuine total lower bound intrinsically to the
actual threshold-zero subspace and use its produced retained prefix. -/
theorem sum_positive_generalHNOrderedSlope_le_positiveDegree :
    ((∑ j : Fin (Module.finrank K E), max (V.generalHNOrderedSlope hS hN j) 0 : ℝ) : EReal) ≤
      V.positiveDegree hS hN := by
  let U := V.generalHNFiltration hS hN 0
  let R := V.restrictOfMeasurableBase U hS
  calc
    _ = ((∑ j : Fin (Module.finrank K U), R.generalHNOrderedSlope hS hN j : ℝ) : EReal) :=
      congrArg (fun x : ℝ ↦ (x : EReal))
        (V.sum_generalHNOrderedSlope_restrict_zero_eq_sum_positive hS hN).symm
    _ ≤ (R.degree hS hN : EReal) :=
      EReal.coe_le_coe (R.sum_generalHNOrderedSlope_le_degree hS hN)
    _ ≤ V.positiveDegree hS hN := V.degree_restrict_le_positiveDegree hS hN U

/-- Source (4.66) with the genuine signed jump integral, whose actual
finite atomic first moment is integrable even in rank zero. -/
theorem neg_integral_generalHNSignedJumpMeasure_le_degree :
    -(∫ᵛ t : ℝ, t ∂<•V.generalHNSignedJumpMeasure hS hN) ≤ V.degree hS hN := by
  rw [V.integral_id_generalHNSignedJumpMeasure hS hN, neg_neg]
  exact V.sum_generalHNOrderedSlope_le_degree hS hN

/-- Source (4.67) with the genuine Lebesgue integral of the actual rank
function on the positive half-line; it is not a proxy finite sum definition. -/
theorem integral_generalHNFiltration_finrank_Ici_zero_le_positiveDegree :
    ((∫ t : ℝ in Set.Ici 0, (Module.finrank K (V.generalHNFiltration hS hN t) : ℝ) : ℝ) :
      EReal) ≤ V.positiveDegree hS hN := by
  rw [V.integral_generalHNFiltration_finrank_Ici_zero hS hN]
  exact V.sum_positive_generalHNOrderedSlope_le_positiveDegree hS hN

end AdelicVectorBundle

end

end ArakelovGeometry
