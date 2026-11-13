/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.ExactSequence.Dual
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.HN.Lift
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Optimal.Basic
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Destabilizing
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
  (V : AdelicVectorBundle.{u} S)
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]
  [hV : V.toNormFamily.IsHermitian]

/-- Chosen actual grade-HN lift data. The cuts retain the actual HN filtration
on each quotient; the mean and pairing identities are supplied by A7, not
optimality assumptions. `exists_hnVariationLift` constructs this data for every
finite real filtration. No nonpositivity or arithmetic upper bound is a field. -/
structure HNVariationLift (P : ℝ → Submodule K V) where
  length : ℕ
  flag : Fin (length + 1) → Submodule K V
  monotone_flag : Monotone flag
  flag_zero : flag 0 = ⊥
  flag_top : flag (Fin.last length) = ⊤
  weight : Fin length → ℝ
  antitone_weight : Antitone weight
  level : ∀ i, P (weight i) = flag i.succ
  right : ∀ i, Submodule.filtrationRightLimit P (weight i) = flag i.castSucc
  reconstruct : ∀ t, P t = ⨆ (i : Fin length) (_ : t ≤ weight i), flag i.succ
  direction : ℝ → Submodule K V
  antitone_direction : Antitone direction
  direction_bot : ∃ t, direction t = ⊥
  direction_top : ∃ t, direction t = ⊤
  direction_left : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → direction s = direction t
  cuts : ∀ i t, ((direction t).comap (flag i.succ).subtype).map
      ((flag i.castSucc).comap (flag i.succ).subtype).mkQ =
    (V.flagQuotientOfMeasurableBase flag i).hermitianHNFiltration
      (hV := ((hV.restrict (flag i.succ)).quotient ((flag i.castSucc).comap (flag
          i.succ).subtype))) t
  mean : Submodule.filtrationExpectation direction = V.slope
  pairing : (finrank K V : ℝ) * Submodule.filtrationPairing P direction =
    ∑ i, weight i * (V.flagQuotientOfMeasurableBase flag i).degree
  primary_mean : (finrank K V : ℝ) * Submodule.filtrationExpectation P =
    ∑ i, weight i * (finrank K
      ((flag i.succ) ⧸ (flag i.castSucc).comap (flag i.succ).subtype) : ℝ)

/-- A3/A7 construct the actual lift data used in Bost p32. This is a chosen
grade-HN lift, not an assertion that the lift is the ambient HN filtration. -/
theorem exists_hnVariationLift (P : ℝ → Submodule K V)
    (hP : Antitone P) (hb : ∃ t, P t = ⊥) (ht : ∃ t, P t = ⊤)
    (hl : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → P s = P t) :
    Nonempty (V.HNVariationLift P) := by
  classical
  obtain ⟨n, U, a, hU, hz, htop, _, ha, _, hlevel, hright, hrec⟩ :=
    Submodule.exists_strictMono_flag_and_jumps_of_antitone hP hb ht hl
  obtain ⟨b, w, B, hB, _, hHN, hquot, hspan, hRspan, hR, hRb, hRt, hRl, hc, hm, hp⟩ :=
    V.exists_hermitianHN_quotient_lift U hU.monotone hz htop
  have hPspan (t : ℝ) : P t = Submodule.span K (B '' {j | t ≤ a j.1}) :=
    (hrec t).trans (Submodule.iSup_flag_eq_span_weights U B hspan a ha.antitone t)
  refine ⟨⟨n, U, hU.monotone, hz, htop, a, ha.antitone, hlevel, hright, hrec,
    _, hR, hRb, hRt, hRl, hc, hm, ?_, ?_⟩⟩
  · simpa only [← funext hrec] using hp a ha.antitone
  · rw [Submodule.filtrationExpectation_eq_sum_weights B _ hPspan]
    have hs : (∑ j : Σ i : Fin n, Fin (finrank K
        ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype)), a j.1) =
        ∑ i, a i * (finrank K
          ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype) : ℝ) := by
      simp [Fintype.sum_sigma, mul_comm]
    by_cases hzE : finrank K V = 0
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

variable {V hS hN hV} {P : ℝ → Submodule K V}

/-- Bost p32 (48), for the actual chosen grade-HN lift: semistability and
centering force nonpositive pairing. This is the special HN direction of the
CM variation argument; no full (5.13), A6 upper bound or A8 existence is used. -/
theorem pairing_nonpos (L : V.HNVariationLift P)
    [hsemi : V.IsMeanSlopeSemistable]
    (hcenter : Submodule.filtrationExpectation P = 0) :
    Submodule.filtrationPairing P L.direction ≤ 0 := by
  let d : Fin (L.length + 1) → ℝ := fun i ↦
    (V.restrictOfMeasurableBase (L.flag i)).degree -
      (finrank K (L.flag i) : ℝ) * V.slope
  have hd (i) : d i ≤ 0 := by
    dsimp only [d]
    by_cases hz : finrank K (L.flag i) = 0
    · rw [degree_eq_zero_of_finrank_eq_zero _ hz, hz]
      simp
    · rw [degree_eq_rank_mul_slope]
      exact sub_nonpos.mpr (mul_le_mul_of_nonneg_left
        (hsemi.2 (L.flag i) (Nat.pos_of_ne_zero hz)) (Nat.cast_nonneg _))
  have hzero : d 0 = 0 := by
    dsimp only [d]
    rw [L.flag_zero]
    simp only [finrank_bot, Nat.cast_zero, zero_mul, sub_zero]
    exact degree_eq_zero_of_finrank_eq_zero _ (finrank_bot K V)
  have htop : d (Fin.last L.length) = 0 := by
    dsimp only [d]
    rw [L.flag_top]
    simp only [finrank_top, V.degree_restrict_top,
      V.degree_eq_rank_mul_slope, sub_self]
  have hstep (i : Fin L.length) :
      (V.flagQuotientOfMeasurableBase L.flag i).degree -
        (finrank K ((L.flag i.succ) ⧸
          (L.flag i.castSucc).comap (L.flag i.succ).subtype) : ℝ) * V.slope =
        d i.succ - d i.castSucc := by
    have hle := L.monotone_flag i.castSucc_le_succ
    have hh : (V.restrictOfMeasurableBase (L.flag i.succ)).toNormFamily.IsHermitian :=
      hV.restrict _
    have he := degree_restrict_add_degree_quotient_eq_of_isHermitian
      (V.restrictOfMeasurableBase (L.flag i.succ))
      ((L.flag i.castSucc).comap (L.flag i.succ).subtype) (hV := hh)
    rw [V.degree_restrict_restrict _ _ hle] at he
    have hr := ((L.flag i.castSucc).comap (L.flag i.succ).subtype).finrank_quotient_add_finrank
    rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at hr
    have hr' : (finrank K ((L.flag i.succ) ⧸
        (L.flag i.castSucc).comap (L.flag i.succ).subtype) : ℝ) +
        finrank K (L.flag i.castSucc) = finrank K (L.flag i.succ) := by exact_mod_cast hr
    change (V.restrictOfMeasurableBase (L.flag i.castSucc)).degree +
      (V.flagQuotientOfMeasurableBase L.flag i).degree = _ at he
    dsimp only [d]
    rw [← hr']
    nlinarith [he]
  have hsum := sum_weighted_increments_nonpos L.weight d L.antitone_weight hd hzero htop
  simp_rw [← hstep, mul_sub, Finset.sum_sub_distrib, ← mul_assoc,
    ← Finset.sum_mul] at hsum
  rw [← L.pairing, ← L.primary_mean, hcenter] at hsum
  simp only [mul_zero, zero_mul, sub_zero] at hsum
  have hr : (0 : ℝ) < finrank K V := Nat.cast_pos.mpr hsemi.1
  nlinarith

end HNVariationLift

end ArakelovGeometry.AdelicVectorBundle

namespace Submodule

variable {K E F Q ι κ : Type*} [Field K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]
  [Finite ι] [Finite κ]

/-- Translation subtracts the constant from the actual mean weight in positive rank. -/
theorem filtrationExpectation_translate (b : Basis ι K E) (w : ι → ℝ)
    {P : ℝ → Submodule K E} (hP : ∀ t, P t = span K (b '' {i | t ≤ w i}))
    (hr : 0 < finrank K E) (s : ℝ) :
    filtrationExpectation (fun t ↦ P (t + s)) = filtrationExpectation P - s := by
  classical
  let := Fintype.ofFinite ι
  have hspan (t : ℝ) : P (t + s) = span K (b '' {i | t ≤ w i - s}) := by
    rw [hP]
    congr 2
    ext i
    exact le_sub_iff_add_le.symm
  rw [filtrationExpectation_eq_sum_weights b _ hspan,
    filtrationExpectation_eq_sum_weights b _ hP, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← finrank_eq_card_basis b]
  field_simp

/-- Centering the second argument subtracts the product of means. -/
theorem filtrationPairing_center_right (b : Basis ι K E) (a r : ι → ℝ)
    {P R : ℝ → Submodule K E}
    (hP : ∀ t, P t = span K (b '' {i | t ≤ a i}))
    (hR : ∀ t, R t = span K (b '' {i | t ≤ r i})) :
    filtrationPairing P (filtrationCenter R) =
      filtrationPairing P R - filtrationExpectation P * filtrationExpectation R := by
  classical
  let := Fintype.ofFinite ι
  rw [filtrationPairing_eq_sum_weights b a _ hP (filtrationCenter_eq_span_weights b r hR),
    filtrationPairing_eq_sum_weights b a r hP hR,
    filtrationExpectation_eq_sum_weights b a hP]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sub_div]
  ring

omit [FiniteDimensional K E] [FiniteDimensional K F] [FiniteDimensional K Q]
  [Finite ι] [Finite κ] in
/-- Equality of actual tensor/image cuts after centering the direction weights.
This is the translation in Bost p32, before taking any quotient expectation. -/
theorem tensor_image_variation_center_cuts (b : Basis ι K E) (d : Basis κ K F)
    (a r : ι → ℝ) (v s : κ → ℝ) (q : E ⊗[K] F →ₗ[K] Q)
    (μ ν ε t : ℝ) :
    (tensorFiltration (weightedBasisVariation b a (fun i ↦ r i - μ) ε)
      (weightedBasisVariation d v (fun j ↦ s j - ν) ε) t).map q =
    (tensorFiltration (weightedBasisVariation b a r ε)
      (weightedBasisVariation d v s ε) (t + ε * (μ + ν))).map q := by
  congr 1
  unfold weightedBasisVariation
  rw [tensorFiltration_eq_span_tensorProduct b d _ _ (fun _ ↦ rfl) (fun _ ↦ rfl),
    tensorFiltration_eq_span_tensorProduct b d _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)]
  congr 2
  ext ij
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> nlinarith

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- The expectation translation for the actual tensor quotient used by Bost
p32. The quotient is the image under the given surjection, with positive rank;
there is no replacement by an unrelated finite maximum model. -/
theorem filtrationExpectation_tensor_variation_center (b : Basis ι K E)
    (d : Basis κ K F) (a r : ι → ℝ) (v s : κ → ℝ)
    (q : E ⊗[K] F →ₗ[K] Q) (hq : Function.Surjective q)
    (hQ : 0 < finrank K Q) (μ ν ε : ℝ) :
    filtrationExpectation (fun t ↦
      (tensorFiltration (weightedBasisVariation b a (fun i ↦ r i - μ) ε)
        (weightedBasisVariation d v (fun j ↦ s j - ν) ε) t).map q) =
    filtrationExpectation (fun t ↦
      (tensorFiltration (weightedBasisVariation b a r ε)
        (weightedBasisVariation d v s ε) t).map q) - ε * (μ + ν) := by
  simp_rw [tensor_image_variation_center_cuts]
  obtain ⟨B, w, hw⟩ := exists_weighted_basis_image (b.tensorProduct d)
    (fun ij ↦ (a ij.1 + ε * r ij.1) + (v ij.2 + ε * s ij.2)) q hq
  have ht (t : ℝ) :
      (tensorFiltration (weightedBasisVariation b a r ε)
        (weightedBasisVariation d v s ε) t).map q = span K (B '' {i | t ≤ w i}) := by
    unfold weightedBasisVariation
    rw [tensorFiltration_eq_span_tensorProduct b d _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)]
    exact hw t
  exact filtrationExpectation_translate B w ht hQ (ε * (μ + ν))

section OptimalVariation

set_option quotPrecheck false in
local notation "CenteredE" => (fun P : ℝ → Submodule K E ↦
  Antitone P ∧ (∃ t, P t = ⊥) ∧ (∃ t, P t = ⊤) ∧
  (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → P s = P t) ∧ filtrationExpectation P = 0)
set_option quotPrecheck false in
local notation "CenteredF" => (fun P : ℝ → Submodule K F ↦
  Antitone P ∧ (∃ t, P t = ⊥) ∧ (∃ t, P t = ⊤) ∧
  (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → P s = P t) ∧ filtrationExpectation P = 0)

variable (b : Basis ι K E) (d : Basis κ K F) (a r : ι → ℝ) (v s : κ → ℝ)
  {P R : ℝ → Submodule K E} {T W : ℝ → Submodule K F}
  (hP : ∀ t, P t = span K (b '' {i | t ≤ a i}))
  (hR : ∀ t, R t = span K (b '' {i | t ≤ r i}))
  (hT : ∀ t, T t = span K (d '' {i | t ≤ v i}))
  (hW : ∀ t, W t = span K (d '' {i | t ≤ s i}))

include hP hR hT hW

/-- The actual centered varied pair has the quadratic energy used on Bost
p32. This fixed-basis identity preserves the reciprocal rank in each factor. -/
theorem centered_tensor_variation_energy
    (hPc : filtrationExpectation P = 0) (hTc : filtrationExpectation T = 0)
    (hunit : filtrationPairing P P + filtrationPairing T T = 1) (ε : ℝ) :
    let A := weightedBasisVariation b a (fun i ↦ r i - filtrationExpectation R) ε
    let B := weightedBasisVariation d v (fun j ↦ s j - filtrationExpectation W) ε
    filtrationPairing A A + filtrationPairing B B =
      1 + 2 * ε * (filtrationPairing P R + filtrationPairing T W) + ε ^ 2 *
        (filtrationPairing (filtrationCenter R) (filtrationCenter R) +
          filtrationPairing (filtrationCenter W) (filtrationCenter W)) := by
  dsimp only
  rw [filtrationPairing_weightedBasisVariation_self b a _ hP
      (filtrationCenter_eq_span_weights b r hR),
    filtrationPairing_weightedBasisVariation_self d v _ hT
      (filtrationCenter_eq_span_weights d s hW),
    filtrationPairing_center_right b a r hP hR,
    filtrationPairing_center_right d v s hT hW, hPc, hTc]
  nlinarith [hunit]

/-- The actual A9 global comparison gives the finite-epsilon Bost bound.
The directions here may be any common-basis directions with nonpositive
total pairing; `HNVariationLift` supplies that property without assuming it.
This is the sufficient binary specialization, not full CM (5.13). -/
theorem tensor_quotient_variation_lower_bound
    (q : E ⊗[K] F →ₗ[K] Q) (hq : Function.Surjective q) (hQ : 0 < finrank K Q)
    (hPc : filtrationExpectation P = 0) (hTc : filtrationExpectation T = 0)
    (hunit : filtrationPairing P P + filtrationPairing T T = 1)
    (c : ℝ) (hc : c < 0)
    (hmin : ∀ (A : ℝ → Submodule K E) (B : ℝ → Submodule K F),
      CenteredE A → CenteredF B → 0 < filtrationPairing A A + filtrationPairing B B →
      c ≤ filtrationExpectation (fun t ↦ (tensorFiltration A B t).map q) /
        Real.sqrt (filtrationPairing A A + filtrationPairing B B))
    (hbeta : filtrationPairing P R + filtrationPairing T W ≤ 0) :
    let β := filtrationPairing P R + filtrationPairing T W
    let D := filtrationPairing (filtrationCenter R) (filtrationCenter R) +
      filtrationPairing (filtrationCenter W) (filtrationCenter W)
    ∃ η > 0, ∀ ε, 0 < ε → ε < η →
      0 < 1 + 2 * ε * β + ε ^ 2 * D ∧
      ε * (filtrationExpectation R + filtrationExpectation W) +
          c * Real.sqrt (1 + 2 * ε * β + ε ^ 2 * D) ≤
        filtrationExpectation (fun t ↦
          (tensorFiltration (weightedBasisVariation b a r ε)
            (weightedBasisVariation d v s ε) t).map q) ∧
      c + ε * (filtrationExpectation R + filtrationExpectation W) + c * D * ε ^ 2 ≤
        filtrationExpectation (fun t ↦
          (tensorFiltration (weightedBasisVariation b a r ε)
            (weightedBasisVariation d v s ε) t).map q) := by
  dsimp only
  let β := filtrationPairing P R + filtrationPairing T W
  let D := filtrationPairing (filtrationCenter R) (filtrationCenter R) +
    filtrationPairing (filtrationCenter W) (filtrationCenter W)
  have hD : 0 ≤ D := add_nonneg
    (filtrationSelfPairing_nonneg b _ (filtrationCenter_eq_span_weights b r hR))
    (filtrationSelfPairing_nonneg d _ (filtrationCenter_eq_span_weights d s hW))
  have hden : 0 < 1 - 2 * β := by dsimp [β]; linarith
  refine ⟨1 / (1 - 2 * β), div_pos zero_lt_one hden, ?_⟩
  intro ε hε hεη
  have hsmall : ε * (1 - 2 * β) < 1 := (lt_div_iff₀ hden).mp hεη
  have hpos : 0 < 1 + 2 * ε * β + ε ^ 2 * D := by
    nlinarith [mul_nonneg (sq_nonneg ε) hD]
  let A := weightedBasisVariation b a (fun i ↦ r i - filtrationExpectation R) ε
  let B := weightedBasisVariation d v (fun j ↦ s j - filtrationExpectation W) ε
  have hAc : CenteredE A := by
    refine ⟨weightedBasisVariation_antitone b a _ ε,
      (weightedBasisVariation_attains_bot_top b a _ ε).1,
      (weightedBasisVariation_attains_bot_top b a _ ε).2,
      weightedBasisVariation_locallyConstant_left b a _ ε, ?_⟩
    rw [filtrationExpectation_weightedBasisVariation b a _ hP
      (filtrationCenter_eq_span_weights b r hR), hPc,
      filtrationExpectation_center b r hR]
    ring
  have hBc : CenteredF B := by
    refine ⟨weightedBasisVariation_antitone d v _ ε,
      (weightedBasisVariation_attains_bot_top d v _ ε).1,
      (weightedBasisVariation_attains_bot_top d v _ ε).2,
      weightedBasisVariation_locallyConstant_left d v _ ε, ?_⟩
    rw [filtrationExpectation_weightedBasisVariation d v _ hT
      (filtrationCenter_eq_span_weights d s hW), hTc,
      filtrationExpectation_center d s hW]
    ring
  have henergy : filtrationPairing A A + filtrationPairing B B =
      1 + 2 * ε * β + ε ^ 2 * D :=
    centered_tensor_variation_energy b d a r v s hP hR hT hW hPc hTc hunit ε
  have hcompare := hmin A B hAc hBc (henergy ▸ hpos)
  rw [henergy] at hcompare
  have hmul := (le_div_iff₀ (Real.sqrt_pos.mpr hpos)).mp hcompare
  have hshift := filtrationExpectation_tensor_variation_center b d a r v s q hq hQ
    (filtrationExpectation R) (filtrationExpectation W) ε
  change filtrationExpectation (fun t ↦ (tensorFiltration A B t).map q) = _ at hshift
  rw [hshift] at hmul
  have hsqrt : Real.sqrt (1 + 2 * ε * β + ε ^ 2 * D) ≤ 1 + D * ε ^ 2 := by
    have hs := Real.sq_sqrt hpos.le
    have hb : 2 * ε * β ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hbeta
    have hnon : 0 ≤ D * ε ^ 2 := mul_nonneg hD (sq_nonneg ε)
    have hn := Real.sqrt_nonneg (1 + 2 * ε * β + ε ^ 2 * D)
    nlinarith [sq_nonneg (D * ε ^ 2)]
  have hcs := mul_le_mul_of_nonpos_left hsqrt hc.le
  exact ⟨hpos, by linarith, by nlinarith⟩

end OptimalVariation

end Submodule

private theorem le_of_quadratic_lower_affine_upper (N : ℝ → ℝ) (c m δ D : ℝ)
    (hlower : ∃ η > 0, ∀ ε, 0 < ε → ε < η → c + ε * m + c * D * ε ^ 2 ≤ N ε)
    (hupper : ∃ η > 0, ∀ ε, 0 < ε → ε < η → N ε ≤ c + ε * δ) : m ≤ δ := by
  by_contra hn
  have hgap : 0 < m - δ := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨η, hη, hl⟩ := hlower
  obtain ⟨θ, hθ, hu⟩ := hupper
  let k := |c * D|
  have hk : 0 ≤ k := abs_nonneg _
  have hcap : 0 < (m - δ) / (k + 1) := div_pos hgap (by linarith)
  obtain ⟨ε, hε, hεlt⟩ := exists_between (lt_min hη (lt_min hθ hcap))
  have heη := hεlt.trans_le (min_le_left _ _)
  have heθ := hεlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hecap := hεlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hh := (hl ε hε heη).trans (hu ε hε heθ)
  have hmul : ε * (k + 1) < m - δ := (lt_div_iff₀ (by linarith : 0 < k + 1)).mp hecap
  have habs : -(c * D) ≤ k := neg_le_abs _
  have hsq : -(c * D) * ε ^ 2 ≤ k * ε ^ 2 :=
    mul_le_mul_of_nonneg_right habs (sq_nonneg ε)
  nlinarith

namespace ArakelovGeometry.AdelicVectorBundle.HNVariationLift

section Binary

open Submodule

variable {K E F Q ι κ : Type*} [Field K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]
  [Finite ι] [Finite κ] {S : AdelicStructure K} [S.IsProper]
  {V : AdelicVectorBundle.{u} S} {Z : AdelicVectorBundle S}
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]
  [hV : V.toNormFamily.IsHermitian] [hZ : Z.toNormFamily.IsHermitian]
  {P : ℝ → Submodule K V} {T : ℝ → Submodule K Z}
  (L : V.HNVariationLift (hV := hV) P) (M : Z.HNVariationLift (hV := hZ) T)
  (b : Basis ι K V) (d : Basis κ K Z) (a r : ι → ℝ) (v s : κ → ℝ)
  (hP : ∀ t, P t = span K (b '' {i | t ≤ a i}))
  (hR : ∀ t, L.direction t = span K (b '' {i | t ≤ r i}))
  (hT : ∀ t, T t = span K (d '' {i | t ≤ v i}))
  (hW : ∀ t, M.direction t = span K (d '' {i | t ≤ s i}))
  (q : V ⊗[K] Z →ₗ[K] Q) (hq : Function.Surjective q) (hQ : 0 < finrank K Q)
  [hsemiV : V.IsMeanSlopeSemistable] [hsemiZ : Z.IsMeanSlopeSemistable]
  (hPc : filtrationExpectation P = 0) (hTc : filtrationExpectation T = 0)
  (hunit : filtrationPairing P P + filtrationPairing T T = 1)

set_option quotPrecheck false in
local notation "CenteredE" => (fun A : ℝ → Submodule K V ↦
  Antitone A ∧ (∃ t, A t = ⊥) ∧ (∃ t, A t = ⊤) ∧
  (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → A s = A t) ∧ filtrationExpectation A = 0)
set_option quotPrecheck false in
local notation "CenteredF" => (fun A : ℝ → Submodule K Z ↦
  Antitone A ∧ (∃ t, A t = ⊥) ∧ (∃ t, A t = ⊤) ∧
  (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → A s = A t) ∧ filtrationExpectation A = 0)
set_option quotPrecheck false in
local notation "c" => filtrationExpectation (fun t ↦ (tensorFiltration P T t).map q)
set_option quotPrecheck false in
local notation "N" => (fun ε ↦ filtrationExpectation (fun t ↦
  (tensorFiltration (weightedBasisVariation b a r ε) (weightedBasisVariation d v s ε) t).map q))
set_option quotPrecheck false in
local notation "D" =>
  (filtrationPairing (filtrationCenter L.direction) (filtrationCenter L.direction) +
  filtrationPairing (filtrationCenter M.direction) (filtrationCenter M.direction))

variable (hc : filtrationExpectation (fun t ↦ (tensorFiltration P T t).map q) < 0)
  (hmin : ∀ (A : ℝ → Submodule K V) (B : ℝ → Submodule K Z),
    (Antitone A ∧ (∃ t, A t = ⊥) ∧ (∃ t, A t = ⊤) ∧
      (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → A s = A t) ∧ filtrationExpectation A = 0) →
    (Antitone B ∧ (∃ t, B t = ⊥) ∧ (∃ t, B t = ⊤) ∧
      (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → B s = B t) ∧ filtrationExpectation B = 0) →
    0 < filtrationPairing A A + filtrationPairing B B →
    filtrationExpectation (fun t ↦ (tensorFiltration P T t).map q) ≤
      filtrationExpectation (fun t ↦ (tensorFiltration A B t).map q) /
      Real.sqrt (filtrationPairing A A + filtrationPairing B B))

include hP hR hT hW hq hQ hsemiV hsemiZ hPc hTc hunit hc hmin

/-- Bost p32's finite-epsilon comparison on actual chosen grade-HN lifts.
This specializes the general CM variational setting to the binary HN direction:
the full (5.13) is omitted. A9 supplies the actual global comparison; the A6
affine upper bound and the A8 negative-candidate producer remain separate. -/
theorem quotient_variation_lower_bound :
    let β := filtrationPairing P L.direction + filtrationPairing T M.direction
    ∃ η > 0, ∀ ε, 0 < ε → ε < η →
      0 < 1 + 2 * ε * β + ε ^ 2 * D ∧
      ε * (V.slope + Z.slope) +
        c * Real.sqrt (1 + 2 * ε * β + ε ^ 2 * D) ≤ N ε ∧
      c + ε * (V.slope + Z.slope) + c * D * ε ^ 2 ≤ N ε := by
  have hbeta := add_nonpos (L.pairing_nonpos (hsemi := hsemiV) hPc)
    (M.pairing_nonpos (hsemi := hsemiZ) hTc)
  simpa only [L.mean, M.mean] using
    tensor_quotient_variation_lower_bound b d a r v s hP hR hT hW q hq hQ
      hPc hTc hunit c hc hmin hbeta

/-- The precise Bost p32 lower bound on the arithmetic variation coefficient.
An eventual affine upper bound for the SAME actual quotient and chosen bases
is the remaining A6 input; equality is unnecessary. Actual HN lifts prove the
pairing sign here. This does not assert full CM (5.13), A8 existence, the A6
upper bound itself, or Bost's main theorem. -/
theorem slope_sum_le_of_eventual_upper_bound (δ : ℝ)
    (hupper : ∃ η > 0, ∀ ε, 0 < ε → ε < η → N ε ≤ c + ε * δ) :
    V.slope + Z.slope ≤ δ := by
  obtain ⟨η, hη, hlow⟩ := L.quotient_variation_lower_bound M b d a r v s hP hR hT hW
    q hq hQ hPc hTc hunit hc hmin
  exact le_of_quadratic_lower_affine_upper N c _ δ D
    ⟨η, hη, fun ε hε he ↦ (hlow ε hε he).2.2⟩ hupper

/-- Bost Lemma 7.2's eventual affine identity implies the p32 lower bound.
This corollary leaves that exact A6 identity explicit and uses only its upper
inequality. Full CM (5.13), A8 existence and the Bost theorem are not asserted. -/
theorem slope_sum_le_of_eventual_affine (δ : ℝ)
    (haffine : ∃ η > 0, ∀ ε, 0 < ε → ε < η → N ε = c + ε * δ) :
    V.slope + Z.slope ≤ δ := by
  apply L.slope_sum_le_of_eventual_upper_bound M b d a r v s hP hR hT hW q hq hQ
     hPc hTc hunit hc hmin δ
  obtain ⟨η, hη, he⟩ := haffine
  exact ⟨η, hη, fun ε hε heη ↦ (he ε hε heη).le⟩

end Binary

end ArakelovGeometry.AdelicVectorBundle.HNVariationLift

namespace ArakelovGeometry.AdelicVectorBundle

open Submodule

section BinaryAssembly

universe u

variable {K : Type*} [Field K] {Q : Type*}
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]
  {S : AdelicStructure K} [S.IsProper]
  (V : AdelicVectorBundle.{u} S) (Z : AdelicVectorBundle S)
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]
  [hV : V.toNormFamily.IsHermitian] [hZ : Z.toNormFamily.IsHermitian]

set_option quotPrecheck false in
local notation "CenteredE" => (fun A : ℝ → Submodule K V ↦
  Antitone A ∧ (∃ t, A t = ⊥) ∧ (∃ t, A t = ⊤) ∧
  (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → A s = A t) ∧ filtrationExpectation A = 0)
set_option quotPrecheck false in
local notation "CenteredF" => (fun A : ℝ → Submodule K Z ↦
  Antitone A ∧ (∃ t, A t = ⊥) ∧ (∃ t, A t = ⊤) ∧
  (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → A s = A t) ∧ filtrationExpectation A = 0)

/-- The assembled A9/A7/A3 producer for Bost p32: a negative actual candidate
produces an actual unit optimizer, actual grade-HN lifts and common bases, with
the needed slope lower bound for every A6 eventual affine upper bound on those
same data. This replaces only the binary HN use of CM (5.13), not that full
inequality. The negative candidate remains the A8 boundary; proving the A6
upper bound and its comparison with the quotient's arithmetic slope remains
downstream. This theorem does not prove Bost's main theorem. -/
theorem exists_bost_hn_variation_bound
    [hsemiV : V.IsMeanSlopeSemistable] [hsemiZ : Z.IsMeanSlopeSemistable]
    (q : V ⊗[K] Z →ₗ[K] Q) (hq : Function.Surjective q) (hQ : 0 < finrank K Q)
    (P₀ : ℝ → Submodule K V) (T₀ : ℝ → Submodule K Z)
    (hP₀ : CenteredE P₀) (hT₀ : CenteredF T₀)
    (hneg₀ : filtrationExpectation (fun t ↦ (tensorFiltration P₀ T₀ t).map q) < 0) :
    ∃ (P : ℝ → Submodule K V) (T : ℝ → Submodule K Z),
      CenteredE P ∧ CenteredF T ∧ filtrationPairing P P + filtrationPairing T T = 1 ∧
      filtrationExpectation (fun t ↦ (tensorFiltration P T t).map q) < 0 ∧
      (∀ (A : ℝ → Submodule K V) (B : ℝ → Submodule K Z),
        CenteredE A → CenteredF B → 0 < filtrationPairing A A + filtrationPairing B B →
        filtrationExpectation (fun t ↦ (tensorFiltration P T t).map q) ≤
          filtrationExpectation (fun t ↦ (tensorFiltration A B t).map q) /
            Real.sqrt (filtrationPairing A A + filtrationPairing B B)) ∧
      ∃ (L : V.HNVariationLift P) (M : Z.HNVariationLift T)
        (b : Basis (Fin (finrank K V)) K V) (d : Basis (Fin (finrank K Z)) K Z)
        (a r : Fin (finrank K V) → ℝ) (v s : Fin (finrank K Z) → ℝ),
        (∀ t, P t = span K (b '' {i | t ≤ a i})) ∧
        (∀ t, L.direction t = span K (b '' {i | t ≤ r i})) ∧
        (∀ t, T t = span K (d '' {i | t ≤ v i})) ∧
        (∀ t, M.direction t = span K (d '' {i | t ≤ s i})) ∧
        ∀ δ : ℝ, (∃ η > 0, ∀ ε, 0 < ε → ε < η →
          filtrationExpectation (fun t ↦
            (tensorFiltration (weightedBasisVariation b a r ε)
              (weightedBasisVariation d v s ε) t).map q) ≤
          filtrationExpectation (fun t ↦ (tensorFiltration P T t).map q) + ε * δ) →
          V.slope + Z.slope ≤ δ := by
  obtain ⟨P, T, hP, hT, hunit, hneg, hmin⟩ :=
    exists_normalized_tensor_quotient_optimizer q hq hsemiV.1 hsemiZ.1 P₀ T₀ hP₀ hT₀ hneg₀
  obtain ⟨L⟩ := V.exists_hnVariationLift P hP.1 hP.2.1 hP.2.2.1 hP.2.2.2.1
  obtain ⟨M⟩ := Z.exists_hnVariationLift T hT.1 hT.2.1 hT.2.2.1 hT.2.2.2.1
  obtain ⟨b, a, r, hPb, hR, _, _⟩ := exists_common_weighted_basis
    hP.1 hP.2.1 hP.2.2.1 hP.2.2.2.1
    L.antitone_direction L.direction_bot L.direction_top L.direction_left
  obtain ⟨d, v, s, hTd, hW, _, _⟩ := exists_common_weighted_basis
    hT.1 hT.2.1 hT.2.2.1 hT.2.2.2.1
    M.antitone_direction M.direction_bot M.direction_top M.direction_left
  refine ⟨P, T, hP, hT, hunit, hneg, hmin, L, M, b, d, a, r, v, s, hPb, hR, hTd, hW, ?_⟩
  intro δ hu
  exact L.slope_sum_le_of_eventual_upper_bound M b d a r v s hPb hR hTd hW q hq hQ
     hP.2.2.2.2 hT.2.2.2.2 hunit hneg hmin δ hu

end BinaryAssembly

end ArakelovGeometry.AdelicVectorBundle
