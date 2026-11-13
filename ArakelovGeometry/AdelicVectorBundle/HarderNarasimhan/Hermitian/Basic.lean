/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Destabilizing

import ArakelovGeometry.AdelicVectorBundle.Degree.ExactSequence.Dual
import ArakelovGeometry.AdelicVectorBundle.Slope.Quotient
import ArakelovGeometry.AdelicVectorBundle.Subquotient.Quotient.Restriction
import ArakelovGeometry.AdelicVectorBundle.Subquotient.Restriction.Functor
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# The actual Hermitian Harder--Narasimhan flag

The rational subspace sequence is obtained by pulling back the produced
maximal destabilizing subspace of each actual quotient. Its positive-rank
steps terminate by strict rank growth, including the empty zero-rank flag.
-/

@[expose] public section

namespace ArakelovGeometry

noncomputable section

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace AdelicVectorBundle

variable [S.IsProper]

/-- A proper rational subspace has a positive-rank actual quotient. -/
theorem finrank_quotient_pos_of_ne_top (U : Submodule K E) (hU : U ≠ ⊤) :
    0 < Module.finrank K (E ⧸ U) := by
  have h := U.finrank_quotient_add_finrank
  have hl := Submodule.finrank_lt hU
  omega

variable (V : AdelicVectorBundle S)
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]
  [hV : V.toNormFamily.IsHermitian]

/-- One canonical HN step: pull back the actual quotient's produced largest
destabilizing subspace. The full subspace is a fixed point. -/
def hermitianHNStep (U : Submodule K V) : Submodule K V :=
  if hU : U = ⊤ then U else
    ((V.quotientOfNormMeasurability U).destabilizingSubspace
      (hV := (hV.quotient U)) (finrank_quotient_pos_of_ne_top U hU)).comap U.mkQ

/-- The terminal subspace stays terminal. -/
@[simp] theorem hermitianHNStep_top : V.hermitianHNStep ⊤ = ⊤ := by
  rw [hermitianHNStep, dite_eq_left rfl]

/-- Every nonterminal step is a strict increase of actual rational subspaces. -/
theorem lt_hermitianHNStep (U : Submodule K V) (hU : U ≠ ⊤) :
    U < V.hermitianHNStep U := by
  rw [hermitianHNStep, dite_eq_right hU]
  have hp := (V.quotientOfNormMeasurability U).destabilizingSubspace_finrank_pos
    (finrank_quotient_pos_of_ne_top U hU)
  have hn : (V.quotientOfNormMeasurability U).destabilizingSubspace
      (finrank_quotient_pos_of_ne_top U hU) ≠ ⊥ := by
    intro he
    rw [he, finrank_bot] at hp
    exact (Nat.lt_irrefl 0) hp
  have h := (Submodule.comap_lt_comap_iff_of_surjective U.mkQ_surjective).mpr
    (bot_lt_iff_ne_bot.mpr hn)
  simpa only [Submodule.comap_bot, Submodule.ker_mkQ] using h

/-- Steps preserve the current subspace, including the terminal step. -/
theorem le_hermitianHNStep (U : Submodule K V) : U ≤ V.hermitianHNStep U := by
  by_cases hU : U = ⊤
  · subst U
    rw [V.hermitianHNStep_top]
  · exact (V.lt_hermitianHNStep U hU).le

/-- The canonical quotient image of a nonterminal step is exactly the
produced destabilizing subspace, rather than a chosen isomorphic proxy. -/
theorem hermitianHNStep_map_mkQ (U : Submodule K V) (hU : U ≠ ⊤) :
    (V.hermitianHNStep U).map U.mkQ =
      (V.quotientOfNormMeasurability U).destabilizingSubspace
        (hV := (hV.quotient U)) (finrank_quotient_pos_of_ne_top U hU) := by
  rw [hermitianHNStep, dite_eq_right hU]
  exact Submodule.map_comap_eq_of_surjective U.mkQ_surjective _

/-- The actual subquotient selected at each nonterminal step is semistable.
Its norm is the restriction of the ambient actual quotient norm. -/
theorem isMeanSlopeSemistable_hermitianHNStep_factor (U : Submodule K V) (hU : U ≠ ⊤) :
    ((V.quotientOfNormMeasurability U).restrictOfNormMeasurability
      ((V.hermitianHNStep U).map U.mkQ)).IsMeanSlopeSemistable := by
  rw [V.hermitianHNStep_map_mkQ U hU]
  exact (V.quotientOfNormMeasurability U).isMeanSlopeSemistable_restrict_destabilizingSubspace
    (finrank_quotient_pos_of_ne_top U hU)

/-- The actual subquotient selected at each step attains the quotient's
maximal slope. -/
theorem slope_hermitianHNStep_factor_eq_maximalSlope (U : Submodule K V) (hU : U ≠ ⊤) :
    (((V.quotientOfNormMeasurability U).restrictOfNormMeasurability
      ((V.hermitianHNStep U).map U.mkQ)).slope : EReal) =
        (V.quotientOfNormMeasurability U).maximalSlope := by
  rw [V.hermitianHNStep_map_mkQ U hU]
  exact (V.quotientOfNormMeasurability U).slope_destabilizingSubspace_eq_maximalSlope
    (finrank_quotient_pos_of_ne_top U hU)

/-- The actual rational HN sequence, continued constantly after it reaches
the full space. No filtration or slope certificate is supplied as input. -/
def hermitianHNTerm : ℕ → Submodule K V :=
  Nat.rec ⊥ (fun _ U ↦ V.hermitianHNStep U)

@[simp] theorem hermitianHNTerm_zero : V.hermitianHNTerm 0 = ⊥ := rfl

theorem hermitianHNTerm_succ (n : ℕ) :
    V.hermitianHNTerm (n + 1) =
      V.hermitianHNStep (V.hermitianHNTerm n) := rfl

/-- The produced rational sequence is increasing. -/
theorem hermitianHNTerm_monotone : Monotone (V.hermitianHNTerm) := by
  apply monotone_nat_of_le_succ
  intro n
  exact V.le_hermitianHNStep _

/-- Every nonterminal term has rank at least its index. -/
theorem le_finrank_hermitianHNTerm (n : ℕ)
    (hn : V.hermitianHNTerm n ≠ ⊤) :
    n ≤ Module.finrank K (V.hermitianHNTerm n) := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have hp : V.hermitianHNTerm n ≠ ⊤ := by
      intro he
      apply hn
      rw [V.hermitianHNTerm_succ n, he, V.hermitianHNStep_top]
    have hi := ih hp
    have hr := Submodule.finrank_lt_finrank_of_lt
      (V.lt_hermitianHNStep (V.hermitianHNTerm n) hp)
    change Module.finrank K (V.hermitianHNTerm n) <
      Module.finrank K (V.hermitianHNTerm (n + 1)) at hr
    omega

/-- Strict rank growth forces the actual construction to terminate by the
ambient rank. The zero bundle terminates at its initial zero subspace. -/
theorem hermitianHNTerm_finrank_eq_top :
    V.hermitianHNTerm (Module.finrank K V) = ⊤ := by
  by_contra hn
  have hi := V.le_finrank_hermitianHNTerm (Module.finrank K V) hn
  have hr := Submodule.finrank_lt hn
  omega

/-- The first terminal index of the actual recursive construction. -/
def hermitianHNLength : ℕ :=
  Nat.find (p := fun n ↦ V.hermitianHNTerm n = ⊤)
    ⟨Module.finrank K V, V.hermitianHNTerm_finrank_eq_top⟩

/-- The length is bounded by the actual bundle rank. -/
theorem hermitianHNLength_le_finrank : V.hermitianHNLength ≤ Module.finrank K V :=
  Nat.find_min' _ (V.hermitianHNTerm_finrank_eq_top)

/-- The final term is the full space. -/
theorem hermitianHNTerm_length_eq_top :
    V.hermitianHNTerm (V.hermitianHNLength) = ⊤ :=
  Nat.find_spec (p := fun n ↦ V.hermitianHNTerm n = ⊤)
    ⟨Module.finrank K V, V.hermitianHNTerm_finrank_eq_top⟩

/-- Every earlier term is proper, making its next actual quotient nonzero. -/
theorem hermitianHNTerm_ne_top_of_lt_length (n : ℕ) (hn : n < V.hermitianHNLength) :
    V.hermitianHNTerm n ≠ ⊤ := Nat.find_min _ hn

/-- The actual sequence is strictly increasing until its first terminal term. -/
theorem hermitianHNTerm_lt (i j : ℕ) (hij : i < j) (hj : j ≤ V.hermitianHNLength) :
    V.hermitianHNTerm i < V.hermitianHNTerm j := by
  have hi := V.hermitianHNTerm_ne_top_of_lt_length i (hij.trans_le hj)
  exact lt_of_lt_of_le (V.lt_hermitianHNStep _ hi)
    (V.hermitianHNTerm_monotone (Nat.succ_le_of_lt hij))

/-- Source's finite rational HN flag, with both endpoints included. -/
def hermitianHNFlag : Fin (V.hermitianHNLength + 1) → Submodule K V :=
  fun i ↦ V.hermitianHNTerm i.val

@[simp] theorem hermitianHNFlag_zero : V.hermitianHNFlag 0 = ⊥ := rfl

/-- The actual finite HN flag ends at the full rational space. -/
theorem hermitianHNFlag_last :
    V.hermitianHNFlag (Fin.last (V.hermitianHNLength)) = ⊤ :=
  V.hermitianHNTerm_length_eq_top

/-- The actual finite HN flag has strict inclusions. -/
theorem hermitianHNFlag_strictMono : StrictMono (V.hermitianHNFlag) := by
  intro i j hij
  exact V.hermitianHNTerm_lt i.val j.val hij (Nat.le_of_lt_succ j.isLt)

/-- In rank zero the finite flag has length zero. -/
theorem hermitianHNLength_eq_zero_of_finrank_eq_zero (hE : Module.finrank K V = 0) :
    V.hermitianHNLength = 0 := by
  have h := V.hermitianHNLength_le_finrank
  omega

/-- The actual normed HN factor is the restriction of the actual quotient
norm to the next flag term's canonical quotient image. -/
abbrev hermitianHNFactor (i : Fin (V.hermitianHNLength)) :
    AdelicVectorBundle S :=
  (V.quotientOfNormMeasurability (V.hermitianHNTerm i.val)).restrictOfNormMeasurability
    ((V.hermitianHNTerm (i.val + 1)).map
      (V.hermitianHNTerm i.val).mkQ)

/-- All actual normed factors of the constructed finite flag are semistable. -/
theorem isMeanSlopeSemistable_hermitianHNFactor
    (i : Fin (V.hermitianHNLength)) :
    (V.hermitianHNFactor i).IsMeanSlopeSemistable :=
  V.isMeanSlopeSemistable_hermitianHNStep_factor _
    (V.hermitianHNTerm_ne_top_of_lt_length i.val i.isLt)

/-- Every factor has positive rank; the zero-bundle flag has no factors. -/
theorem hermitianHNFactor_finrank_pos (i : Fin (V.hermitianHNLength)) :
    0 < Module.finrank K ((V.hermitianHNTerm (i.val + 1)).map
      (V.hermitianHNTerm i.val).mkQ) :=
  (V.isMeanSlopeSemistable_hermitianHNFactor i).1

/-- Every factor retains Hermitianity with its actual quotient/restriction norm. -/
theorem isHermitian_hermitianHNFactor (i : Fin (V.hermitianHNLength)) :
    (V.hermitianHNFactor i).toNormFamily.IsHermitian :=
  (hV.quotient _).restrict _

/-- The actual mean of each HN factor attains the remaining quotient's maximum. -/
theorem slope_hermitianHNFactor_eq_maximalSlope_quotient
    (i : Fin (V.hermitianHNLength)) :
    ((V.hermitianHNFactor i).slope : EReal) =
      (V.quotientOfNormMeasurability (V.hermitianHNTerm i.val)).maximalSlope :=
  V.slope_hermitianHNStep_factor_eq_maximalSlope _
    (V.hermitianHNTerm_ne_top_of_lt_length i.val i.isLt)

/-- A subspace strictly larger than the produced largest destabilizer has
strictly smaller actual mean slope. Equality would force containment in it. -/
theorem slope_restrict_lt_slope_destabilizingSubspace_of_lt
    (hr : 0 < Module.finrank K V) (P : Submodule K V)
    (hDP : V.destabilizingSubspace hr < P) :
    (V.restrictOfNormMeasurability P).slope <
      (V.restrictOfNormMeasurability (V.destabilizingSubspace hr)).slope := by
  have hP := (V.destabilizingSubspace_finrank_pos hr).trans_le
    (Submodule.finrank_mono hDP.le)
  have hD := V.slope_destabilizingSubspace_eq_maximalSlope hr
  apply lt_of_le_of_ne (EReal.coe_le_coe_iff.mp
    ((V.slope_restrict_le_maximalSlope P hP).trans_eq hD.symm))
  intro he
  have hPmax := (congrArg (fun x : ℝ ↦ (x : EReal)) he).trans hD
  exact (not_le_of_gt hDP)
    (V.le_destabilizingSubspace_of_slope_eq_maximalSlope hr P hP hPmax)

/-- The actual quotient of a larger restricted subspace by the destabilizer
has strictly smaller mean. Hermitian exact degree additivity is load-bearing. -/
theorem slope_quotient_restrict_destabilizingSubspace_lt
    (hr : 0 < Module.finrank K V) (P : Submodule K V)
    (hDP : V.destabilizingSubspace hr < P) :
    ((V.restrictOfNormMeasurability P).quotientOfNormMeasurability
      ((V.destabilizingSubspace hr).comap P.subtype)).slope <
        (V.restrictOfNormMeasurability (V.destabilizingSubspace hr)).slope := by
  let D := V.destabilizingSubspace hr
  let I := D.comap P.subtype
  have hIrank : Module.finrank K I = Module.finrank K D :=
    (Submodule.comapSubtypeEquivOfLe hDP.le).finrank_eq
  have hrank := I.finrank_quotient_add_finrank
  rw [hIrank] at hrank
  have hDPdim := Submodule.finrank_lt_finrank_of_lt hDP
  have hQpos : 0 < Module.finrank K (P ⧸ I) := by
    apply finrank_quotient_pos_of_ne_top I
    intro he
    have hh := congrArg (fun T : Submodule K P ↦ Module.finrank K T) he
    rw [hIrank, finrank_top] at hh
    exact (ne_of_lt hDPdim) hh
  have hPpos : 0 < Module.finrank K P :=
    (V.destabilizingSubspace_finrank_pos hr).trans_le
      (Submodule.finrank_mono hDP.le)
  have hd := (V.restrictOfNormMeasurability P).degree_restrict_add_degree_quotient_eq_of_isHermitian
    I (hV := (hV.restrict P))
  rw [V.degree_restrict_restrict D P hDP.le] at hd
  rw [(V.restrictOfNormMeasurability D).degree_eq_rank_mul_slope,
    degree_eq_rank_mul_slope
      ((V.restrictOfNormMeasurability P).quotientOfNormMeasurability I),
    (V.restrictOfNormMeasurability P).degree_eq_rank_mul_slope] at hd
  have hmean := V.slope_restrict_lt_slope_destabilizingSubspace_of_lt hr P hDP
  have hQr : (0 : ℝ) < Module.finrank K (P ⧸ I) := Nat.cast_pos.mpr hQpos
  have hPr : (0 : ℝ) < Module.finrank K P := Nat.cast_pos.mpr hPpos
  have hrankr : (Module.finrank K (P ⧸ I) : ℝ) + Module.finrank K D =
      Module.finrank K P := by
    exact_mod_cast hrank
  have hβdim := congrArg (fun r : ℝ ↦ r * (V.restrictOfNormMeasurability D).slope) hrankr
  rw [add_mul] at hβdim
  have hm := mul_lt_mul_of_pos_left hmean hPr
  apply (mul_lt_mul_iff_right₀ hQr).mp
  change (Module.finrank K D : ℝ) * (V.restrictOfNormMeasurability D).slope +
    (Module.finrank K (P ⧸ I) : ℝ) *
      ((V.restrictOfNormMeasurability P).quotientOfNormMeasurability I).slope =
        (Module.finrank K P : ℝ) * (V.restrictOfNormMeasurability P).slope at hd
  change (V.restrictOfNormMeasurability P).slope <
    (V.restrictOfNormMeasurability D).slope at hmean
  nlinarith

/-- Removing the actual largest destabilizer strictly lowers the remaining
quotient's maximal slope. The zero quotient has maximum `⊥` and is included. -/
theorem maximalSlope_quotient_destabilizingSubspace_lt_slope
    (hr : 0 < Module.finrank K V) :
    (V.quotientOfNormMeasurability (V.destabilizingSubspace hr)).maximalSlope <
      ((V.restrictOfNormMeasurability (V.destabilizingSubspace hr)).slope
        : EReal) := by
  let D := V.destabilizingSubspace hr
  let Q := V.quotientOfNormMeasurability D
  by_cases hD : D = ⊤
  · have hzero : Module.finrank K (V ⧸ D) = 0 := by
      let : Subsingleton (V ⧸ D) := Submodule.Quotient.subsingleton_iff.mpr hD
      exact Module.finrank_zero_of_subsingleton
    rw [Q.maximalSlope_eq_bot_of_finrank_eq_zero hzero]
    exact EReal.bot_lt_coe _
  · have hQpos := finrank_quotient_pos_of_ne_top D hD
    let hQH := hV.quotient D
    let T := Q.destabilizingSubspace (hV := hQH) hQpos
    let P := T.comap D.mkQ
    have hTpos := Q.destabilizingSubspace_finrank_pos (hV := hQH) hQpos
    have hTne : T ≠ ⊥ := by
      intro he
      change 0 < Module.finrank K T at hTpos
      rw [he, finrank_bot] at hTpos
      exact (Nat.lt_irrefl 0) hTpos
    have hDP : D < P := by
      have h := (Submodule.comap_lt_comap_iff_of_surjective D.mkQ_surjective).mpr
        (bot_lt_iff_ne_bot.mpr hTne)
      simpa only [Submodule.comap_bot, Submodule.ker_mkQ] using h
    let g := D.mkQ.comp P.subtype
    have hgker : g.ker = D.comap P.subtype := by
      simp only [g, LinearMap.ker_comp, Submodule.ker_mkQ]
    have hgrange : g.range = T := by
      dsimp only [g]
      rw [LinearMap.range_comp, Submodule.range_subtype]
      exact Submodule.map_comap_eq_of_surjective D.mkQ_surjective T
    have hs : ((V.restrictOfNormMeasurability P).quotientOfNormMeasurability g.ker).slope =
        (Q.restrictOfNormMeasurability g.range).slope := by
      apply slope_eq_of_completed_isometry _ _ g.quotKerEquivRange
      intro ω z
      exact (V.toNormFamily.quotient_restrict_range_norm_eq P D hDP.le ω z).symm
    have hkermean := congrArg (fun I : Submodule K P ↦
      ((V.restrictOfNormMeasurability P).quotientOfNormMeasurability I).slope) hgker
    have hrangemean := congrArg (fun U : Submodule K (V ⧸ D) ↦
      (Q.restrictOfNormMeasurability U).slope) hgrange
    have hPmean := V.slope_quotient_restrict_destabilizingSubspace_lt hr P hDP
    have hTmean := (hs.trans hrangemean).symm.trans_lt (hkermean.trans_lt hPmean)
    have hTmax := Q.slope_destabilizingSubspace_eq_maximalSlope (hV := hQH) hQpos
    exact hTmax.symm.trans_lt (EReal.coe_lt_coe_iff.mpr hTmean)

/-- Every nonterminal canonical HN step strictly lowers the remaining
actual quotient's maximum. Quotient composition preserves its actual norms. -/
theorem maximalSlope_quotient_hermitianHNStep_lt (U : Submodule K V) (hU : U ≠ ⊤) :
    (V.quotientOfNormMeasurability (V.hermitianHNStep U)).maximalSlope <
      (V.quotientOfNormMeasurability U).maximalSlope := by
  let Q := V.quotientOfNormMeasurability U
  let hQ := hV.quotient U
  let hr := finrank_quotient_pos_of_ne_top U hU
  let D := Q.destabilizingSubspace (hV := hQ) hr
  have hdrop := Q.maximalSlope_quotient_destabilizingSubspace_lt_slope (hV := hQ) hr
  rw [Q.slope_destabilizingSubspace_eq_maximalSlope (hV := hQ) hr] at hdrop
  have hk : (D.mkQ.comp U.mkQ).ker = V.hermitianHNStep U := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, hermitianHNStep, dite_eq_right hU]
  have he := (V.maximalSlope_quotient_quotient_eq_quotient_ker U D).trans
    (congrArg (fun W : Submodule K V ↦ (V.quotientOfNormMeasurability W).maximalSlope) hk)
  exact he.symm.trans_lt hdrop

/-- Consecutive actual HN factors have strictly decreasing real slopes. -/
theorem slope_hermitianHNFactor_lt_of_succ
    (i j : Fin (V.hermitianHNLength)) (hij : i.val + 1 = j.val) :
    (V.hermitianHNFactor j).slope <
      (V.hermitianHNFactor i).slope := by
  have hdrop := V.maximalSlope_quotient_hermitianHNStep_lt
    (V.hermitianHNTerm i.val)
    (V.hermitianHNTerm_ne_top_of_lt_length i.val i.isLt)
  have hterms : V.hermitianHNTerm j.val =
      V.hermitianHNStep (V.hermitianHNTerm i.val) := by
    rw [← hij, V.hermitianHNTerm_succ]
  have hj := (V.slope_hermitianHNFactor_eq_maximalSlope_quotient j).trans
    (congrArg (fun U : Submodule K V ↦ (V.quotientOfNormMeasurability U).maximalSlope)
      hterms)
  have hi := V.slope_hermitianHNFactor_eq_maximalSlope_quotient i
  exact EReal.coe_lt_coe_iff.mp (hj.trans_lt (hdrop.trans_eq hi.symm))

/-- Source Proposition 4.3.37: the produced actual semistable factors have
strictly decreasing slopes throughout the entire finite flag. -/
theorem hermitianHNFactor_slope_strictAnti :
    StrictAnti (fun i ↦ (V.hermitianHNFactor i).slope) := by
  have hstep : ∀ d : ℕ, ∀ i j : Fin (V.hermitianHNLength),
      j.val = i.val + (d + 1) →
        (V.hermitianHNFactor j).slope <
          (V.hermitianHNFactor i).slope := by
    intro d
    induction d with
    | zero =>
      intro i j hij
      exact V.slope_hermitianHNFactor_lt_of_succ i j hij.symm
    | succ d ih =>
      intro i j hij
      let k : Fin (V.hermitianHNLength) := ⟨i.val + 1, by omega⟩
      have hkj : j.val = k.val + (d + 1) := by dsimp only [k]; omega
      exact (ih k j hkj).trans (V.slope_hermitianHNFactor_lt_of_succ i k rfl)
  intro i j hij
  exact hstep (j.val - i.val - 1) i j (by change i.val < j.val at hij; omega)

/-- The actual flag rank intervals partition all ambient rank positions.
The zero bundle has an empty position type. -/
theorem exists_unique_hermitianHNFactor_rank_interval (j : Fin (Module.finrank K V)) :
    ∃! i : Fin (V.hermitianHNLength),
      Module.finrank K (V.hermitianHNTerm i.val) ≤ j.val ∧
        j.val < Module.finrank K (V.hermitianHNTerm (i.val + 1)) := by
  have hlast : j.val < Module.finrank K
      (V.hermitianHNTerm (V.hermitianHNLength)) := by
    rw [V.hermitianHNTerm_length_eq_top, finrank_top]
    exact j.isLt
  let hex : ∃ n, j.val < Module.finrank K (V.hermitianHNTerm n) :=
    ⟨V.hermitianHNLength, hlast⟩
  let n := Nat.find hex
  have hn : j.val < Module.finrank K (V.hermitianHNTerm n) := Nat.find_spec hex
  have hlen : n ≤ V.hermitianHNLength := Nat.find_min' hex hlast
  have hn0 : n ≠ 0 := by
    intro he
    rw [he, V.hermitianHNTerm_zero, finrank_bot] at hn
    exact Nat.not_lt_zero _ hn
  let i : Fin (V.hermitianHNLength) := ⟨n - 1, by omega⟩
  have hi0 : Module.finrank K (V.hermitianHNTerm i.val) ≤ j.val :=
    Nat.le_of_not_gt (Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hn0) (by decide)))
  have hi1 : j.val < Module.finrank K (V.hermitianHNTerm (i.val + 1)) := by
    have hs : i.val + 1 = n := by dsimp only [i]; omega
    rwa [hs]
  refine ⟨i, ⟨hi0, hi1⟩, ?_⟩
  intro k hk
  apply Fin.ext
  by_cases hik : i.val < k.val
  · have hd : Module.finrank K (V.hermitianHNTerm (i.val + 1)) ≤
        Module.finrank K (V.hermitianHNTerm k.val) :=
      Submodule.finrank_mono (V.hermitianHNTerm_monotone (Nat.succ_le_of_lt hik))
    omega
  · by_cases hki : k.val < i.val
    · have hd : Module.finrank K (V.hermitianHNTerm (k.val + 1)) ≤
          Module.finrank K (V.hermitianHNTerm i.val) :=
        Submodule.finrank_mono (V.hermitianHNTerm_monotone (Nat.succ_le_of_lt hki))
      omega
    · omega

/-- The unique factor containing an actual ambient rank position. -/
def hermitianHNFactorIndex (j : Fin (Module.finrank K V)) :
    Fin (V.hermitianHNLength) :=
  Classical.choose (V.exists_unique_hermitianHNFactor_rank_interval j)

/-- The produced index lies in the actual flag's corresponding rank interval. -/
theorem hermitianHNFactorIndex_rank_interval (j : Fin (Module.finrank K V)) :
    Module.finrank K (V.hermitianHNTerm
      (V.hermitianHNFactorIndex j).val) ≤ j.val ∧
        j.val < Module.finrank K (V.hermitianHNTerm
          ((V.hermitianHNFactorIndex j).val + 1)) :=
  (Classical.choose_spec (V.exists_unique_hermitianHNFactor_rank_interval j)).1

/-- Actual rank intervals characterize the factor index. -/
theorem hermitianHNFactorIndex_eq_of_rank_interval (j : Fin (Module.finrank K V))
    (i : Fin (V.hermitianHNLength))
    (hi : Module.finrank K (V.hermitianHNTerm i.val) ≤ j.val ∧
      j.val < Module.finrank K (V.hermitianHNTerm (i.val + 1))) :
    V.hermitianHNFactorIndex j = i :=
  ((Classical.choose_spec
    (V.exists_unique_hermitianHNFactor_rank_interval j)).2 i hi).symm

/-- Increasing actual rank positions cannot move to an earlier HN factor. -/
theorem hermitianHNFactorIndex_monotone : Monotone (V.hermitianHNFactorIndex) := by
  intro j k hjk
  have hj := V.hermitianHNFactorIndex_rank_interval j
  have hk := V.hermitianHNFactorIndex_rank_interval k
  apply Fin.le_iff_val_le_val.mpr
  by_contra h
  have hlt := Nat.lt_of_not_ge h
  have hd : Module.finrank K (V.hermitianHNTerm
        ((V.hermitianHNFactorIndex k).val + 1)) ≤
      Module.finrank K (V.hermitianHNTerm
        (V.hermitianHNFactorIndex j).val) :=
    Submodule.finrank_mono (V.hermitianHNTerm_monotone (Nat.succ_le_of_lt hlt))
  change j.val ≤ k.val at hjk
  omega

/-- Source Definition 4.3.39: the factor mean repeated across its actual
rank interval, indexed by the ambient rank. Rank zero gives an empty list. -/
def hermitianHNOrderedSlope (j : Fin (Module.finrank K V)) : ℝ :=
  (V.hermitianHNFactor (V.hermitianHNFactorIndex j)).slope

/-- The ordered slope at an actual rank position is the actual factor mean
specified by the source's rank-interval rule. -/
theorem hermitianHNOrderedSlope_eq_of_rank_interval (j : Fin (Module.finrank K V))
    (i : Fin (V.hermitianHNLength))
    (hi : Module.finrank K (V.hermitianHNTerm i.val) ≤ j.val ∧
      j.val < Module.finrank K (V.hermitianHNTerm (i.val + 1))) :
    V.hermitianHNOrderedSlope j = (V.hermitianHNFactor i).slope := by
  exact congrArg (fun k ↦ (V.hermitianHNFactor k).slope)
    (V.hermitianHNFactorIndex_eq_of_rank_interval j i hi)

/-- The source ordered Hermitian slopes form a nonincreasing finite list. -/
theorem hermitianHNOrderedSlope_antitone : Antitone (V.hermitianHNOrderedSlope) := by
  intro j k hjk
  exact (V.hermitianHNFactor_slope_strictAnti).antitone
    (V.hermitianHNFactorIndex_monotone hjk)

/-- A positive-rank bundle has at least one actual HN factor. -/
theorem hermitianHNLength_pos_of_finrank_pos (hr : 0 < Module.finrank K V) :
    0 < V.hermitianHNLength := by
  by_contra h
  have hn := Nat.eq_zero_of_not_pos h
  have ht := V.hermitianHNTerm_length_eq_top
  rw [hn, V.hermitianHNTerm_zero] at ht
  have hd := congrArg (fun U : Submodule K V ↦ Module.finrank K U) ht
  rw [finrank_bot, finrank_top] at hd
  omega

/-- The first ambient rank position belongs to the first actual factor. -/
theorem hermitianHNFactorIndex_zero (hr : 0 < Module.finrank K V) :
    V.hermitianHNFactorIndex ⟨0, hr⟩ =
      ⟨0, V.hermitianHNLength_pos_of_finrank_pos hr⟩ := by
  apply V.hermitianHNFactorIndex_eq_of_rank_interval
  constructor
  · change Module.finrank K (V.hermitianHNTerm 0) ≤ 0
    rw [V.hermitianHNTerm_zero, finrank_bot]
  · have hlt := V.hermitianHNTerm_lt 0 1 (by decide)
      (V.hermitianHNLength_pos_of_finrank_pos hr)
    have hd := Submodule.finrank_lt_finrank_of_lt hlt
    rw [V.hermitianHNTerm_zero, finrank_bot] at hd
    exact hd

/-- Source Definition 4.3.39's first slope is the actual bundle maximum. -/
theorem hermitianHNOrderedSlope_zero_eq_maximalSlope (hr : 0 < Module.finrank K V) :
    (V.hermitianHNOrderedSlope ⟨0, hr⟩ : EReal) = V.maximalSlope := by
  let i : Fin (V.hermitianHNLength) :=
    ⟨0, V.hermitianHNLength_pos_of_finrank_pos hr⟩
  have hm : V.hermitianHNOrderedSlope ⟨0, hr⟩ =
      (V.hermitianHNFactor i).slope :=
    congrArg (fun k ↦ (V.hermitianHNFactor k).slope)
      (V.hermitianHNFactorIndex_zero hr)
  have hi : ((V.hermitianHNFactor i).slope : EReal) =
      V.maximalSlope :=
    (V.slope_hermitianHNFactor_eq_maximalSlope_quotient i).trans
      (V.maximalSlope_quotient_bot)
  exact (congrArg (fun x : ℝ ↦ (x : EReal)) hm).trans hi

/-- The number of successive factors retained at a real threshold, computed
from the actual factor means. The supremum of an empty finite set is zero. -/
def hermitianHNCut (t : ℝ) : ℕ :=
  (Finset.univ.filter (fun i ↦ t ≤ (V.hermitianHNFactor i).slope)).sup
    (fun i ↦ i.val + 1)

/-- Every real cutoff lies within the produced finite flag. -/
theorem hermitianHNCut_le_length (t : ℝ) :
    V.hermitianHNCut t ≤ V.hermitianHNLength := by
  apply Finset.sup_le_iff.mpr
  intro i _
  exact Nat.succ_le_of_lt i.isLt

/-- Exactly an initial segment of the actual factors survives a threshold. -/
theorem le_hermitianHNFactor_slope_iff_lt_cut (t : ℝ)
    (i : Fin (V.hermitianHNLength)) :
    t ≤ (V.hermitianHNFactor i).slope ↔
      i.val < V.hermitianHNCut t := by
  constructor
  · intro hi
    have hm : i ∈ Finset.univ.filter
        (fun j ↦ t ≤ (V.hermitianHNFactor j).slope) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    exact Nat.lt_of_succ_le
      (Finset.le_sup (f := fun j : Fin (V.hermitianHNLength) ↦ j.val + 1) hm)
  · intro hi
    by_contra hb
    have ht := lt_of_not_ge hb
    have hc : V.hermitianHNCut t ≤ i.val := by
      apply Finset.sup_le_iff.mpr
      intro j hj
      have hjt := (Finset.mem_filter.mp hj).2
      have hji : j.val < i.val := by
        by_contra h
        have hij : i ≤ j := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt h)
        exact (not_le_of_gt ht)
          (hjt.trans ((V.hermitianHNFactor_slope_strictAnti).antitone hij))
      exact Nat.succ_le_of_lt hji
    exact (not_lt_of_ge hc) hi

/-- Raising a threshold decreases the actual finite cutoff. -/
theorem hermitianHNCut_antitone : Antitone (V.hermitianHNCut) := by
  intro s t hst
  apply Finset.sup_le_iff.mpr
  intro i hi
  exact Nat.succ_le_of_lt
    ((V.le_hermitianHNFactor_slope_iff_lt_cut s i).mp
      (hst.trans (Finset.mem_filter.mp hi).2))

/-- Source equation (4.57): the actual HN real filtration retains exactly
the initial factors whose actual means are at least the threshold. -/
def hermitianHNFiltration (t : ℝ) : Submodule K V :=
  V.hermitianHNTerm (V.hermitianHNCut t)

/-- The actual rational HN real filtration is decreasing. -/
theorem hermitianHNFiltration_antitone : Antitone (V.hermitianHNFiltration) := by
  intro s t hst
  exact V.hermitianHNTerm_monotone (V.hermitianHNCut_antitone hst)

/-- A threshold strictly above every actual factor mean gives zero. -/
theorem hermitianHNFiltration_eq_bot_of_slope_lt (t : ℝ)
    (ht : ∀ i, (V.hermitianHNFactor i).slope < t) :
    V.hermitianHNFiltration t = ⊥ := by
  have hc : V.hermitianHNCut t ≤ 0 := by
    apply Finset.sup_le_iff.mpr
    intro i hi
    exact False.elim ((not_le_of_gt (ht i)) (Finset.mem_filter.mp hi).2)
  exact (congrArg (V.hermitianHNTerm) (Nat.eq_zero_of_le_zero hc)).trans
    (V.hermitianHNTerm_zero)

/-- A threshold at most every actual factor mean retains the whole space,
including the empty flag of a zero-rank bundle. -/
theorem hermitianHNFiltration_eq_top_of_le_slope (t : ℝ)
    (ht : ∀ i, t ≤ (V.hermitianHNFactor i).slope) :
    V.hermitianHNFiltration t = ⊤ := by
  have hc : V.hermitianHNCut t = V.hermitianHNLength := by
    apply le_antisymm (V.hermitianHNCut_le_length t)
    by_contra h
    have hlt := Nat.lt_of_not_ge h
    let i : Fin (V.hermitianHNLength) := ⟨V.hermitianHNCut t, hlt⟩
    exact (Nat.lt_irrefl _) ((V.le_hermitianHNFactor_slope_iff_lt_cut t i).mp (ht i))
  exact (congrArg (V.hermitianHNTerm) hc).trans
    (V.hermitianHNTerm_length_eq_top)

/-- The actual real filtration is separated. Its threshold is produced from
the finite list of actual factor means. -/
theorem hermitianHNFiltration_separated :
    ∃ a : ℝ, ∀ t : ℝ, a < t → V.hermitianHNFiltration t = ⊥ := by
  obtain ⟨a, ha⟩ := (Set.finite_range
    (fun i ↦ (V.hermitianHNFactor i).slope)).bddAbove
  exact ⟨a, fun t ht ↦ V.hermitianHNFiltration_eq_bot_of_slope_lt t
    (fun i ↦ (ha ⟨i, rfl⟩).trans_lt ht)⟩

/-- The actual real filtration is exhaustive. No nonzero-rank assumption is needed. -/
theorem hermitianHNFiltration_exhaustive :
    ∃ a : ℝ, ∀ t : ℝ, t ≤ a → V.hermitianHNFiltration t = ⊤ := by
  obtain ⟨a, ha⟩ := (Set.finite_range
    (fun i ↦ (V.hermitianHNFactor i).slope)).bddBelow
  exact ⟨a, fun t ht ↦ V.hermitianHNFiltration_eq_top_of_le_slope t
    (fun i ↦ ht.trans (ha ⟨i, rfl⟩))⟩

/-- The actual HN real filtration of a rank-zero bundle is identically zero. -/
theorem hermitianHNFiltration_eq_bot_of_finrank_eq_zero (hE : Module.finrank K V = 0)
    (t : ℝ) : V.hermitianHNFiltration t = ⊥ := by
  have hc := V.hermitianHNCut_le_length t
  rw [V.hermitianHNLength_eq_zero_of_finrank_eq_zero hE] at hc
  exact (congrArg (V.hermitianHNTerm) (Nat.eq_zero_of_le_zero hc)).trans
    (V.hermitianHNTerm_zero)

/-- An ordered rank position survives exactly when it lies below the rank
of the actual real-filtration subspace. -/
theorem le_hermitianHNOrderedSlope_iff_lt_filtration_finrank (t : ℝ)
    (j : Fin (Module.finrank K V)) :
    t ≤ V.hermitianHNOrderedSlope j ↔
      j.val < Module.finrank K (V.hermitianHNFiltration t) := by
  let i := V.hermitianHNFactorIndex j
  let c := V.hermitianHNCut t
  have hi := V.hermitianHNFactorIndex_rank_interval j
  change t ≤ (V.hermitianHNFactor i).slope ↔ _
  rw [V.le_hermitianHNFactor_slope_iff_lt_cut t i]
  change i.val < c ↔ j.val < Module.finrank K (V.hermitianHNTerm c)
  constructor
  · intro hic
    have hd : Module.finrank K (V.hermitianHNTerm (i.val + 1)) ≤
        Module.finrank K (V.hermitianHNTerm c) :=
      Submodule.finrank_mono (V.hermitianHNTerm_monotone (Nat.succ_le_of_lt hic))
    exact hi.2.trans_le hd
  · intro hj
    by_contra h
    have hd : Module.finrank K (V.hermitianHNTerm c) ≤
        Module.finrank K (V.hermitianHNTerm i.val) :=
      Submodule.finrank_mono (V.hermitianHNTerm_monotone (Nat.le_of_not_gt h))
    exact (not_lt_of_ge (hd.trans hi.1)) hj

/-- Source Definition 4.3.39's rank-count formula for the actual rational
real filtration and the produced ordered slope list, including rank zero. -/
theorem hermitianHNFiltration_finrank_eq_card (t : ℝ) :
    Module.finrank K (V.hermitianHNFiltration t) =
      Fintype.card {j : Fin (Module.finrank K V) // t ≤ V.hermitianHNOrderedSlope j} := by
  let A := {j : Fin (Module.finrank K V) // t ≤ V.hermitianHNOrderedSlope j}
  let r := Module.finrank K (V.hermitianHNFiltration t)
  have hr : r ≤ Module.finrank K V := (V.hermitianHNFiltration t).finrank_le
  let e : A ≃ Fin r :=
    { toFun := fun j ↦ ⟨j.val.val,
        (V.le_hermitianHNOrderedSlope_iff_lt_filtration_finrank t j.val).mp j.property⟩
      invFun := fun j ↦ ⟨⟨j.val, j.isLt.trans_le hr⟩,
        (V.le_hermitianHNOrderedSlope_iff_lt_filtration_finrank t _).mpr j.isLt⟩
      left_inv := fun j ↦ by apply Subtype.ext; apply Fin.ext; rfl
      right_inv := fun j ↦ by apply Fin.ext; rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin r) |>.symm

/-- The actual HN filtration is locally constant on the left. The positive
gap is produced from its finite list of actual factor means. -/
theorem hermitianHNFiltration_locallyConstantLeft (t : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ →
      V.hermitianHNFiltration (t - ε) =
        V.hermitianHNFiltration t := by
  let β : Fin (V.hermitianHNLength) → ℝ :=
    fun i ↦ (V.hermitianHNFactor i).slope
  let A : Finset ℝ := insert (t - 1) ((Finset.univ.filter (fun i ↦ β i < t)).image β)
  have hA : A.Nonempty := ⟨t - 1, Finset.mem_insert_self _ _⟩
  let b := A.max' hA
  have hb : b < t := by
    have hm : b ∈ A := Finset.max'_mem A hA
    rcases Finset.mem_insert.mp hm with h | h
    · rw [h]
      linarith
    · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
      rw [← he]
      exact (Finset.mem_filter.mp hi).2
  have hβ : ∀ i, β i < t → β i ≤ b := by
    intro i hi
    exact Finset.le_max' A (β i) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩))
  let δ := (t - b) / 2
  refine ⟨δ, by dsimp [δ]; linarith, ?_⟩
  intro ε hε he
  have hp : ∀ i, t - ε ≤ β i ↔ t ≤ β i := by
    intro i
    constructor
    · intro hi
      by_contra hn
      have hbi := hβ i (lt_of_not_ge hn)
      dsimp only [δ] at he
      linarith
    · intro hi
      linarith
  have hf : Finset.univ.filter (fun i ↦ t - ε ≤ β i) =
      Finset.univ.filter (fun i ↦ t ≤ β i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hp i
  have hc : V.hermitianHNCut (t - ε) = V.hermitianHNCut t :=
    congrArg (fun B : Finset (Fin (V.hermitianHNLength)) ↦
      B.sup (fun i ↦ i.val + 1)) hf
  exact congrArg (V.hermitianHNTerm) hc

/-- At an actual factor mean, the cutoff includes that factor and exactly
its predecessors. Strict decrease of the produced means is load-bearing. -/
theorem hermitianHNCut_factor_slope (i : Fin (V.hermitianHNLength)) :
    V.hermitianHNCut ((V.hermitianHNFactor i).slope) =
      i.val + 1 := by
  apply le_antisymm
  · apply Finset.sup_le_iff.mpr
    intro j hj
    have hm := (Finset.mem_filter.mp hj).2
    have hji : j ≤ i := by
      by_contra h
      exact (not_le_of_gt (V.hermitianHNFactor_slope_strictAnti
        (lt_of_not_ge h))) hm
    exact Nat.succ_le_succ (Fin.le_iff_val_le_val.mp hji)
  · exact Nat.succ_le_of_lt
      ((V.le_hermitianHNFactor_slope_iff_lt_cut _ i).mp le_rfl)

/-- The actual real filtration at a factor's mean is the upper subspace
of precisely that factor. -/
theorem hermitianHNFiltration_factor_slope (i : Fin (V.hermitianHNLength)) :
    V.hermitianHNFiltration ((V.hermitianHNFactor i).slope) =
      V.hermitianHNTerm (i.val + 1) :=
  congrArg (V.hermitianHNTerm) (V.hermitianHNCut_factor_slope i)

/-- The finite cutoff immediately to the right retains the factors whose
actual means are strictly greater than the threshold. -/
def hermitianHNRightCut (t : ℝ) : ℕ :=
  (Finset.univ.filter (fun i ↦ t < (V.hermitianHNFactor i).slope)).sup
    (fun i ↦ i.val + 1)

theorem hermitianHNRightCut_le_length (t : ℝ) :
    V.hermitianHNRightCut t ≤ V.hermitianHNLength := by
  apply Finset.sup_le_iff.mpr
  intro i _
  exact Nat.succ_le_of_lt i.isLt

/-- The factors strictly above a threshold also form an actual initial segment. -/
theorem lt_hermitianHNFactor_slope_iff_lt_rightCut (t : ℝ)
    (i : Fin (V.hermitianHNLength)) :
    t < (V.hermitianHNFactor i).slope ↔
      i.val < V.hermitianHNRightCut t := by
  constructor
  · intro hi
    have hm : i ∈ Finset.univ.filter
        (fun j ↦ t < (V.hermitianHNFactor j).slope) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    exact Nat.lt_of_succ_le
      (Finset.le_sup (f := fun j : Fin (V.hermitianHNLength) ↦ j.val + 1) hm)
  · intro hi
    by_contra hb
    have ht := le_of_not_gt hb
    have hc : V.hermitianHNRightCut t ≤ i.val := by
      apply Finset.sup_le_iff.mpr
      intro j hj
      have hjt := (Finset.mem_filter.mp hj).2
      have hji : j.val < i.val := by
        by_contra h
        have hij : i ≤ j := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt h)
        exact (not_lt_of_ge ht)
          (hjt.trans_le ((V.hermitianHNFactor_slope_strictAnti).antitone hij))
      exact Nat.succ_le_of_lt hji
    exact (not_lt_of_ge hc) hi

/-- At a factor's actual mean, the cutoff immediately to the right excludes
that factor and retains exactly its predecessors. -/
theorem hermitianHNRightCut_factor_slope (i : Fin (V.hermitianHNLength)) :
    V.hermitianHNRightCut ((V.hermitianHNFactor i).slope) =
      i.val := by
  apply le_antisymm
  · apply Finset.sup_le_iff.mpr
    intro j hj
    have hm := (Finset.mem_filter.mp hj).2
    have hji : j < i := by
      by_contra h
      exact (not_lt_of_ge
        ((V.hermitianHNFactor_slope_strictAnti).antitone (le_of_not_gt h))) hm
    exact Nat.succ_le_of_lt (Fin.lt_def.mp hji)
  · by_cases hi : i.val = 0
    · exact (le_of_eq hi).trans (Nat.zero_le _)
    · let j : Fin (V.hermitianHNLength) := ⟨i.val - 1, by omega⟩
      have hji : j < i := Fin.lt_def.mpr (by dsimp [j]; omega)
      have hj := (V.lt_hermitianHNFactor_slope_iff_lt_rightCut _ j).mp
        (V.hermitianHNFactor_slope_strictAnti hji)
      dsimp [j] at hj
      omega

/-- Source equation (4.57)'s right-limit subspace: the union of the actual
filtration subspaces at all strictly larger thresholds. -/
def hermitianHNFiltrationPlus (t : ℝ) : Submodule K V :=
  ⨆ s : {s : ℝ // t < s}, V.hermitianHNFiltration s.val

/-- The actual right-limit union is the flag term selected by the strict cutoff. -/
theorem hermitianHNFiltrationPlus_eq_term (t : ℝ) :
    V.hermitianHNFiltrationPlus t =
      V.hermitianHNTerm (V.hermitianHNRightCut t) := by
  apply le_antisymm
  · apply iSup_le
    intro s
    apply V.hermitianHNTerm_monotone
    apply Finset.sup_le_iff.mpr
    intro i hi
    exact Nat.succ_le_of_lt
      ((V.lt_hermitianHNFactor_slope_iff_lt_rightCut t i).mp
        (s.property.trans_le (Finset.mem_filter.mp hi).2))
  · let c := V.hermitianHNRightCut t
    by_cases hc : c = 0
    · change V.hermitianHNTerm c ≤ _
      rw [hc, V.hermitianHNTerm_zero]
      exact bot_le
    · have hcl := V.hermitianHNRightCut_le_length t
      let i : Fin (V.hermitianHNLength) := ⟨c - 1, by dsimp [c]; omega⟩
      have hi : i.val + 1 = c := by dsimp [i]; omega
      have ht : t < (V.hermitianHNFactor i).slope :=
        (V.lt_hermitianHNFactor_slope_iff_lt_rightCut t i).mpr (by
          change c - 1 < c
          omega)
      have hs : V.hermitianHNFiltration
          ((V.hermitianHNFactor i).slope) =
            V.hermitianHNTerm c :=
        (V.hermitianHNFiltration_factor_slope i).trans
          (congrArg (V.hermitianHNTerm) hi)
      change V.hermitianHNTerm c ≤ _
      rw [← hs]
      exact le_iSup (fun s : {s : ℝ // t < s} ↦ V.hermitianHNFiltration s.val)
        ⟨(V.hermitianHNFactor i).slope, ht⟩

/-- At an actual factor mean, the right-limit union is its lower flag subspace. -/
theorem hermitianHNFiltrationPlus_factor_slope
    (i : Fin (V.hermitianHNLength)) :
    V.hermitianHNFiltrationPlus ((V.hermitianHNFactor i).slope) =
      V.hermitianHNTerm i.val :=
  (V.hermitianHNFiltrationPlus_eq_term _).trans
    (congrArg (V.hermitianHNTerm) (V.hermitianHNRightCut_factor_slope i))

/-- The source's actual subquotient norm: first restrict to the upper HN
subspace, then quotient by the kernel of its map modulo the lower one. -/
abbrev hermitianHNSubquotient (i : Fin (V.hermitianHNLength)) :
    AdelicVectorBundle S :=
  let U := V.hermitianHNTerm (i.val + 1)
  let W := V.hermitianHNTerm i.val
  (V.restrictOfNormMeasurability U).quotientOfNormMeasurability (W.mkQ.comp U.subtype).ker

/-- Actual subquotient norms retain Hermitianity. -/
theorem isHermitian_hermitianHNSubquotient (i : Fin (V.hermitianHNLength)) :
    (V.hermitianHNSubquotient i).toNormFamily.IsHermitian :=
  (hV.restrict _).quotient _

/-- The actual quotient of the restricted norm is semistable with the
same mean as the canonical quotient-image factor. The completed norm
identity, rather than an algebraic identification alone, proves this. -/
theorem hermitianHNSubquotient_semistable_slope
    (i : Fin (V.hermitianHNLength)) :
    (V.hermitianHNSubquotient i).IsMeanSlopeSemistable ∧
      (V.hermitianHNSubquotient i).slope =
        (V.hermitianHNFactor i).slope := by
  let U := V.hermitianHNTerm (i.val + 1)
  let W := V.hermitianHNTerm i.val
  let g := W.mkQ.comp U.subtype
  let Q := (V.restrictOfNormMeasurability U).quotientOfNormMeasurability g.ker
  let R := (V.quotientOfNormMeasurability W).restrictOfNormMeasurability g.range
  have hWU : W ≤ U := V.hermitianHNTerm_monotone (Nat.le_succ i.val)
  have hn : ∀ ω z, R.toNormFamily.norm ω
      (g.quotKerEquivRange.toLinearMap.baseChange (S.ϕ ω).Completion z) =
        Q.toNormFamily.norm ω z := by
    intro ω z
    exact (V.toNormFamily.quotient_restrict_range_norm_eq U W hWU ω z).symm
  have hg : g.range = U.map W.mkQ := by
    simp only [g, LinearMap.range_comp, Submodule.range_subtype]
  have hR : R.IsMeanSlopeSemistable := by
    have he := congrArg (fun T : Submodule K (V ⧸ W) ↦
      IsMeanSlopeSemistable
        ((V.quotientOfNormMeasurability W).restrictOfNormMeasurability T)) hg
    exact Eq.mpr he (V.isMeanSlopeSemistable_hermitianHNFactor i)
  have hr : 0 < Module.finrank K (U ⧸ g.ker) := by
    rw [g.quotKerEquivRange.finrank_eq]
    exact hR.1
  have hs := Q.slope_eq_of_completed_isometry R g.quotKerEquivRange hn
  have hm := Q.maximalSlope_eq_of_completed_isometry R g.quotKerEquivRange hn
  have hRm := (R.isMeanSlopeSemistable_iff_maximalSlope_eq_slope hR.1).mp hR
  have hf : R.slope = (V.hermitianHNFactor i).slope :=
    congrArg (fun T : Submodule K (V ⧸ W) ↦
      ((V.quotientOfNormMeasurability W).restrictOfNormMeasurability T).slope) hg
  change Q.IsMeanSlopeSemistable ∧ Q.slope = _
  refine ⟨(Q.isMeanSlopeSemistable_iff_maximalSlope_eq_slope hr).mpr ?_, hs.trans hf⟩
  exact (hm.trans hRm).trans (congrArg (fun x : ℝ ↦ (x : EReal)) hs.symm)

/-- The actual right-limit subspace is contained in the threshold subspace. -/
theorem hermitianHNFiltrationPlus_le (t : ℝ) :
    V.hermitianHNFiltrationPlus t ≤ V.hermitianHNFiltration t := by
  apply iSup_le
  intro s
  exact V.hermitianHNFiltration_antitone s.property.le

/-- The actual right-limit supremum is the source's literal union over
positive increments, rather than merely a generated subspace. -/
theorem mem_hermitianHNFiltrationPlus_iff (t : ℝ) (x : V) :
    x ∈ V.hermitianHNFiltrationPlus t ↔
      ∃ ε : ℝ, 0 < ε ∧ x ∈ V.hermitianHNFiltration (t + ε) := by
  have : Nonempty {s : ℝ // t < s} := ⟨⟨t + 1, by linarith⟩⟩
  have hd : Directed (· ≤ ·)
      (fun s : {s : ℝ // t < s} ↦ V.hermitianHNFiltration s.val) := by
    intro r s
    refine ⟨⟨min r.val s.val, lt_min r.property s.property⟩, ?_, ?_⟩
    · exact V.hermitianHNFiltration_antitone (min_le_left _ _)
    · exact V.hermitianHNFiltration_antitone (min_le_right _ _)
  have hu : x ∈ V.hermitianHNFiltrationPlus t ↔
      ∃ s : {s : ℝ // t < s}, x ∈ V.hermitianHNFiltration s.val :=
    Submodule.mem_iSup_of_directed _ hd
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := hu.mp hx
    refine ⟨s.val - t, sub_pos.mpr s.property, ?_⟩
    have he : t + (s.val - t) = s.val := by ring
    simpa only [he] using hs
  · rintro ⟨ε, hε, hx⟩
    exact hu.mpr ⟨⟨t + ε, by linarith⟩, hx⟩

/-- Away from the produced factor means, the actual right-limit subspace
equals the threshold subspace. -/
theorem hermitianHNFiltrationPlus_eq_of_ne_factor_slope (t : ℝ)
    (ht : ∀ i, (V.hermitianHNFactor i).slope ≠ t) :
    V.hermitianHNFiltrationPlus t = V.hermitianHNFiltration t := by
  have hf : Finset.univ.filter
      (fun i ↦ t ≤ (V.hermitianHNFactor i).slope) =
        Finset.univ.filter (fun i ↦ t < (V.hermitianHNFactor i).slope) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hi ↦ lt_of_le_of_ne hi (ht i).symm, fun hi ↦ hi.le⟩
  have hc : V.hermitianHNCut t = V.hermitianHNRightCut t :=
    congrArg (fun B : Finset (Fin (V.hermitianHNLength)) ↦
      B.sup (fun i ↦ i.val + 1)) hf
  exact (V.hermitianHNFiltrationPlus_eq_term t).trans
    (congrArg (V.hermitianHNTerm) hc.symm)

/-- The source's actual graded adelic bundle: quotient the norm restricted
to the threshold subspace by its kernel modulo the right-limit subspace. -/
abbrev hermitianHNGradedPiece (t : ℝ) :
    AdelicVectorBundle S :=
  let U := V.hermitianHNFiltration t
  let W := V.hermitianHNFiltrationPlus t
  (V.restrictOfNormMeasurability U).quotientOfNormMeasurability (W.mkQ.comp U.subtype).ker

/-- The graded quotient uses exactly the right-limit subspace inside the
threshold subspace. This is the source's subquotient carrier. -/
theorem hermitianHNGradedPiece_ker_eq_comap (t : ℝ) :
    ((V.hermitianHNFiltrationPlus t).mkQ.comp
      (V.hermitianHNFiltration t).subtype).ker =
        (V.hermitianHNFiltrationPlus t).comap
          (V.hermitianHNFiltration t).subtype := by
  simp only [LinearMap.ker_comp, Submodule.ker_mkQ]

/-- Every actual graded subquotient retains the original Hermitian norms. -/
theorem isHermitian_hermitianHNGradedPiece (t : ℝ) :
    (V.hermitianHNGradedPiece t).toNormFamily.IsHermitian :=
  (hV.restrict _).quotient _

/-- At a produced factor mean, the source's actual graded quotient is
semistable and has precisely that actual mean. -/
theorem hermitianHNGradedPiece_factor_slope
    (i : Fin (V.hermitianHNLength)) :
    (V.hermitianHNGradedPiece
      ((V.hermitianHNFactor i).slope)).IsMeanSlopeSemistable ∧
      (V.hermitianHNGradedPiece
        ((V.hermitianHNFactor i).slope)).slope =
          (V.hermitianHNFactor i).slope := by
  let t := (V.hermitianHNFactor i).slope
  have he : (V.hermitianHNFiltration t,
      V.hermitianHNFiltrationPlus t) =
        (V.hermitianHNTerm (i.val + 1), V.hermitianHNTerm i.val) :=
    Prod.ext (V.hermitianHNFiltration_factor_slope i)
      (V.hermitianHNFiltrationPlus_factor_slope i)
  have hp := congrArg (fun p : Submodule K V × Submodule K V ↦
    IsMeanSlopeSemistable
      ((V.restrictOfNormMeasurability p.1).quotientOfNormMeasurability
        (p.2.mkQ.comp p.1.subtype).ker)) he
  have hm := congrArg (fun p : Submodule K V × Submodule K V ↦
    ((V.restrictOfNormMeasurability p.1).quotientOfNormMeasurability
      (p.2.mkQ.comp p.1.subtype).ker).slope) he
  have hq := V.hermitianHNSubquotient_semistable_slope i
  exact ⟨Eq.mpr hp hq.1, hm.trans hq.2⟩

/-- Away from the actual factor means, the actual graded quotient has
rank zero. No zero-degree or slope certificate is used. -/
theorem hermitianHNGradedPiece_finrank_eq_zero_of_ne_factor_slope (t : ℝ)
    (ht : ∀ i, (V.hermitianHNFactor i).slope ≠ t) :
    Module.finrank K ((V.hermitianHNFiltration t) ⧸
      ((V.hermitianHNFiltrationPlus t).mkQ.comp
        (V.hermitianHNFiltration t).subtype).ker) = 0 := by
  let U := V.hermitianHNFiltration t
  have he := congrArg (fun W : Submodule K V ↦
    Module.finrank K (U ⧸ (W.mkQ.comp U.subtype).ker))
      (V.hermitianHNFiltrationPlus_eq_of_ne_factor_slope t ht)
  have hg : (U.mkQ.comp U.subtype).range = ⊥ := by
    rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.mkQ_map_self]
  have hr := congrArg (fun T : Submodule K (V ⧸ U) ↦ Module.finrank K T) hg
  rw [finrank_bot] at hr
  exact he.trans ((U.mkQ.comp U.subtype).quotKerEquivRange.finrank_eq.trans hr)

/-- Every actual graded bundle is zero or is semistable of slope equal
to its index, as in the source's Hermitian HN real filtration. -/
theorem hermitianHNGradedPiece_zero_or_semistable (t : ℝ) :
    Module.finrank K ((V.hermitianHNFiltration t) ⧸
      ((V.hermitianHNFiltrationPlus t).mkQ.comp
        (V.hermitianHNFiltration t).subtype).ker) = 0 ∨
      ((V.hermitianHNGradedPiece t).IsMeanSlopeSemistable ∧
        (V.hermitianHNGradedPiece t).slope = t) := by
  by_cases ht : ∃ i, (V.hermitianHNFactor i).slope = t
  · obtain ⟨i, hi⟩ := ht
    have hq := V.hermitianHNGradedPiece_factor_slope i
    have hp := congrArg (fun s : ℝ ↦
      (V.hermitianHNGradedPiece s).IsMeanSlopeSemistable) hi
    have hm := congrArg (fun s : ℝ ↦ (V.hermitianHNGradedPiece s).slope) hi
    exact Or.inr ⟨Eq.mp hp hq.1, hm.symm.trans (hq.2.trans hi)⟩
  · exact Or.inl (V.hermitianHNGradedPiece_finrank_eq_zero_of_ne_factor_slope t
      (fun i hi ↦ ht ⟨i, hi⟩))

end AdelicVectorBundle

end

end ArakelovGeometry
