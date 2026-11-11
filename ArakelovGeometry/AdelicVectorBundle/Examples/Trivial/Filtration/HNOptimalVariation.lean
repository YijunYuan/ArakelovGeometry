/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.HNLift
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Optimal
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Destabilizing
public import ArakelovGeometry.AdelicVectorBundle.Degree.ExactSequence.Dual
public import ArakelovGeometry.AdelicVectorBundle.Subquotient.Restriction.Functor

/-!
# The actual HN-lift variation needed on Bost page 32

Chen–Moriwaki (5.13) treats general variational directions and finite families.
This module proves only the binary grade-HN direction needed for Bost page 32,
equation (48) and its following optimality argument. All expectations and
pairings retain reciprocal-rank normalization and real weights. A finite
quadratic estimate replaces the derivative argument; full CM (5.13) is omitted.

The A6 local affine upper bound (or stronger local affine identity) for the same
actual quotient and chosen bases remains an explicit arithmetic input. A8 must
separately produce a negative candidate from geometric instability. Neither
boundary, nor Bost's main theorem, is proved by this module.
-/

@[expose] public section

open Module
open scoped BigOperators TensorProduct

private theorem sum_weighted_increments {n : ℕ}
    (a : Fin (n + 1) → ℝ) (d : Fin (n + 2) → ℝ) :
    (∑ i, a i * (d i.succ - d i.castSucc)) =
      a (Fin.last n) * d (Fin.last (n + 1)) - a 0 * d 0 +
        ∑ i : Fin n, (a i.castSucc - a i.succ) * d i.succ.castSucc := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.succ_castSucc]
    rw [ih (fun i ↦ a i.castSucc) (fun i ↦ d i.castSucc)]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.castSucc_zero, Fin.succ_last, Fin.succ_castSucc]
    ring

private theorem sum_weighted_increments_nonpos {n : ℕ}
    (a : Fin n → ℝ) (d : Fin (n + 1) → ℝ) (ha : Antitone a)
    (hd : ∀ i, d i ≤ 0) (h0 : d 0 = 0) (hn : d (Fin.last n) = 0) :
    (∑ i, a i * (d i.succ - d i.castSucc)) ≤ 0 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [sum_weighted_increments, h0, hn]
    simp only [mul_zero, sub_self, zero_add]
    exact Finset.sum_nonpos fun i _ ↦
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (ha i.castSucc_le_succ)) (hd _)

namespace ArakelovGeometry.AdelicVectorBundle

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] {S : AdelicStructure K} [S.IsProper]
  (V : AdelicVectorBundle S E)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hV : V.toNormFamily.IsHermitian hN)

/-- Chosen actual grade-HN lift data. The cuts retain the actual HN filtration
on each quotient; the mean and pairing identities are supplied by A7, not
optimality assumptions. `exists_hnVariationLift` constructs this data for every
finite real filtration. No nonpositivity or arithmetic upper bound is a field. -/
structure HNVariationLift (P : ℝ → Submodule K E) where
  length : ℕ
  flag : Fin (length + 1) → Submodule K E
  monotone_flag : Monotone flag
  flag_zero : flag 0 = ⊥
  flag_top : flag (Fin.last length) = ⊤
  weight : Fin length → ℝ
  antitone_weight : Antitone weight
  reconstruct : ∀ t, P t = ⨆ (i : Fin length) (_ : t ≤ weight i), flag i.succ
  direction : ℝ → Submodule K E
  antitone_direction : Antitone direction
  direction_bot : ∃ t, direction t = ⊥
  direction_top : ∃ t, direction t = ⊤
  direction_left : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → direction s = direction t
  cuts : ∀ i t, ((direction t).comap (flag i.succ).subtype).map
      ((flag i.castSucc).comap (flag i.succ).subtype).mkQ =
    (V.flagQuotientOfMeasurableBase flag hS i).hermitianHNFiltration hS hN
      ((hV.restrict (flag i.succ)).quotient ((flag i.castSucc).comap (flag i.succ).subtype)) t
  mean : Submodule.filtrationExpectation direction = V.slope hS hN
  pairing : (finrank K E : ℝ) * Submodule.filtrationPairing P direction =
    ∑ i, weight i * (V.flagQuotientOfMeasurableBase flag hS i).degree hS hN
  primary_mean : (finrank K E : ℝ) * Submodule.filtrationExpectation P =
    ∑ i, weight i * (finrank K
      ((flag i.succ) ⧸ (flag i.castSucc).comap (flag i.succ).subtype) : ℝ)

/-- A3/A7 construct the actual lift data used in Bost p32. This is a chosen
grade-HN lift, not an assertion that the lift is the ambient HN filtration. -/
theorem exists_hnVariationLift (P : ℝ → Submodule K E)
    (hP : Antitone P) (hb : ∃ t, P t = ⊥) (ht : ∃ t, P t = ⊤)
    (hl : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → P s = P t) :
    Nonempty (V.HNVariationLift hS hN hV P) := by
  classical
  obtain ⟨n, U, a, hU, hz, htop, _, ha, _, _, _, hrec⟩ :=
    Submodule.exists_strictMono_flag_and_jumps_of_antitone hP hb ht hl
  obtain ⟨b, w, B, hB, _, hHN, hquot, hspan, hRspan, hR, hRb, hRt, hRl, hc, hm, hp⟩ :=
    V.exists_hermitianHN_quotient_lift hS hN hV U hU.monotone hz htop
  have hPspan (t : ℝ) : P t = Submodule.span K (B '' {j | t ≤ a j.1}) :=
    (hrec t).trans (Submodule.iSup_flag_eq_span_weights U B hspan a ha.antitone t)
  refine ⟨⟨n, U, hU.monotone, hz, htop, a, ha.antitone, hrec,
    _, hR, hRb, hRt, hRl, hc, hm, ?_, ?_⟩⟩
  · simpa only [← funext hrec] using hp a ha.antitone
  · rw [Submodule.filtrationExpectation_eq_sum_weights B _ hPspan]
    have hs : (∑ j : Σ i : Fin n, Fin (finrank K
        ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype)), a j.1) =
        ∑ i, a i * (finrank K
          ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype) : ℝ) := by
      simp [Fintype.sum_sigma, mul_comm]
    by_cases hzE : finrank K E = 0
    · have hcard : Fintype.card (Σ i : Fin n, Fin (finrank K
          ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype))) = 0 := by
        rw [← finrank_eq_card_basis B, hzE]
      let : IsEmpty (Σ i : Fin n, Fin (finrank K
        ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype))) :=
          Fintype.card_eq_zero_iff.mp hcard
      rw [← hs]
      simp
    · rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hzE), hs]

namespace HNVariationLift

variable {V hS hN hV} {P : ℝ → Submodule K E}

/-- Bost p32 (48), for the actual chosen grade-HN lift: semistability and
centering force nonpositive pairing. This is the special HN direction of the
CM variation argument; no full (5.13), A6 upper bound or A8 existence is used. -/
theorem pairing_nonpos (L : V.HNVariationLift hS hN hV P)
    (hsemi : V.IsMeanSlopeSemistable hS hN)
    (hcenter : Submodule.filtrationExpectation P = 0) :
    Submodule.filtrationPairing P L.direction ≤ 0 := by
  let d : Fin (L.length + 1) → ℝ := fun i ↦
    (V.restrictOfMeasurableBase (L.flag i) hS).degree hS hN -
      (finrank K (L.flag i) : ℝ) * V.slope hS hN
  have hd (i) : d i ≤ 0 := by
    dsimp only [d]
    by_cases hz : finrank K (L.flag i) = 0
    · rw [degree_eq_zero_of_finrank_eq_zero _ hS hN hz, hz]
      simp
    · rw [degree_eq_rank_mul_slope]
      exact sub_nonpos.mpr (mul_le_mul_of_nonneg_left
        (hsemi.2 (L.flag i) (Nat.pos_of_ne_zero hz)) (Nat.cast_nonneg _))
  have hzero : d 0 = 0 := by
    dsimp only [d]
    rw [L.flag_zero]
    simp only [finrank_bot, Nat.cast_zero, zero_mul, sub_zero]
    exact degree_eq_zero_of_finrank_eq_zero _ hS hN (finrank_bot K E)
  have htop : d (Fin.last L.length) = 0 := by
    dsimp only [d]
    rw [L.flag_top]
    simp only [finrank_top, V.degree_restrict_top hS hN,
      V.degree_eq_rank_mul_slope hS hN, sub_self]
  have hstep (i : Fin L.length) :
      (V.flagQuotientOfMeasurableBase L.flag hS i).degree hS hN -
        (finrank K ((L.flag i.succ) ⧸
          (L.flag i.castSucc).comap (L.flag i.succ).subtype) : ℝ) * V.slope hS hN =
        d i.succ - d i.castSucc := by
    have hle := L.monotone_flag i.castSucc_le_succ
    have hh : (V.restrictOfMeasurableBase (L.flag i.succ) hS).toNormFamily.IsHermitian hN :=
      hV.restrict _
    have he := degree_restrict_add_degree_quotient_eq_of_isHermitian
      (V.restrictOfMeasurableBase (L.flag i.succ) hS)
      ((L.flag i.castSucc).comap (L.flag i.succ).subtype) hS hN hh
    rw [V.degree_restrict_restrict _ _ hle hS hN] at he
    have hr := ((L.flag i.castSucc).comap (L.flag i.succ).subtype).finrank_quotient_add_finrank
    rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at hr
    have hr' : (finrank K ((L.flag i.succ) ⧸
        (L.flag i.castSucc).comap (L.flag i.succ).subtype) : ℝ) +
        finrank K (L.flag i.castSucc) = finrank K (L.flag i.succ) := by exact_mod_cast hr
    change (V.restrictOfMeasurableBase (L.flag i.castSucc) hS).degree hS hN +
      (V.flagQuotientOfMeasurableBase L.flag hS i).degree hS hN = _ at he
    dsimp only [d]
    rw [← hr']
    nlinarith [he]
  have hsum := sum_weighted_increments_nonpos L.weight d L.antitone_weight hd hzero htop
  simp_rw [← hstep, mul_sub, Finset.sum_sub_distrib, ← mul_assoc,
    ← Finset.sum_mul] at hsum
  rw [← L.pairing, ← L.primary_mean, hcenter] at hsum
  simp only [mul_zero, zero_mul, sub_zero] at hsum
  have hr : (0 : ℝ) < finrank K E := Nat.cast_pos.mpr hsemi.1
  nlinarith

end HNVariationLift

end ArakelovGeometry.AdelicVectorBundle
