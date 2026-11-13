/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.Basic
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Game.Semistability
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Semistability
public import ArakelovGeometry.AdelicVectorBundle.Slope.Flag

import ArakelovGeometry.Order.HarderNarasimhan.Comparison
import ArakelovGeometry.Order.HarderNarasimhan.FiniteFlag

/-!
# General adelic semistability and game flags

The existing positive-rank semistability predicate agrees with game semistability.
The game supplies a unique finite flag. Direct comparison identifies its terms
with the original real-indexed filtration, without a second factor construction.
-/

@[expose] public section

open HarderNarasimhan

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S)
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]

/-- The game's semistable intervals are exactly the actual semistable subquotients.
Strictness of the interval supplies the positive-rank condition. -/
theorem isSemistable_subquotient_iff_game (I : StrictIntvl (Submodule K V)) :
    ((V.restrictOfNormMeasurability I.right).quotientOfNormMeasurability
      (I.left.comap I.right.subtype)).IsSemistable ↔
        ((V.maximalSlopePayoff).restrict I).IsSemistable := by
  have hr : 0 < Module.finrank K (I.right ⧸ I.left.comap I.right.subtype) := by
    rw [Submodule.finrank_quotient, (Submodule.comapSubtypeEquivOfLe I.lt.le).finrank_eq]
    exact Nat.sub_pos_of_lt (Submodule.finrank_lt_finrank_of_lt I.lt)
  rw [isSemistable_iff_minimalSlope_restrict_le _ hr,
    V.isSemistable_restrict_maximalSlopePayoff_iff]

/-- On a semistable flag factor, the game value is its actual modified slope. -/
theorem A_maximalSlopePayoff_flag_eq_hnMeanSlope {n : ℕ}
    (F : Fin (n + 1) → Submodule K V) (hF : StrictMono F) (i : Fin n)
    [hsemi : (V.flagQuotientOfNormMeasurability F i).IsSemistable] :
    (V.maximalSlopePayoff).A
      ⟨F i.castSucc, F i.succ, hF Fin.castSucc_lt_succ⟩ =
        ((V.flagQuotientOfNormMeasurability F i).hnMeanSlope : EReal) := by
  rw [V.A_maximalSlopePayoff_eq_minimalSlope]
  exact ((V.flagQuotientOfNormMeasurability F i).isSemistable_iff_hnMeanSlope_eq_minimalSlope
    hsemi.1).mp hsemi |>.symm

/-- The abstract game's finite-series uniqueness identifies actual adelic flags,
including the length-zero flag of a zero bundle. -/
theorem hnFlags_eq {n m : ℕ}
    (F : Fin (n + 1) → Submodule K V) (G : Fin (m + 1) → Submodule K V)
    (hF : StrictMono F) (hG : StrictMono G)
    (hF0 : F 0 = ⊥) (hG0 : G 0 = ⊥)
    (hFtop : F (Fin.last n) = ⊤) (hGtop : G (Fin.last m) = ⊤)
    [hFsemi : ∀ i, (V.flagQuotientOfNormMeasurability F i).IsSemistable]
    [hGsemi : ∀ i, (V.flagQuotientOfNormMeasurability G i).IsSemistable]
    (hFA : StrictAnti fun i ↦ (V.flagQuotientOfNormMeasurability F i).hnMeanSlope)
    (hGA : StrictAnti fun i ↦ (V.flagQuotientOfNormMeasurability G i).hnMeanSlope) :
    (⟨n, F⟩ : Σ k : ℕ, Fin (k + 1) → Submodule K V) = ⟨m, G⟩ := by
  refine PayoffFunction.finiteFlags_eq (μ := V.maximalSlopePayoff)
    F G hF hG hF0 hG0 hFtop hGtop (hFsemi := ?_) (hGsemi := ?_) ?_ ?_
  · intro i
    exact (V.isSemistable_subquotient_iff_game
      ⟨F i.castSucc, F i.succ, hF Fin.castSucc_lt_succ⟩).mp (hFsemi i)
  · intro i
    exact (V.isSemistable_subquotient_iff_game
      ⟨G i.castSucc, G i.succ, hG Fin.castSucc_lt_succ⟩).mp (hGsemi i)
  · intro i j hij
    exact (V.A_maximalSlopePayoff_flag_eq_hnMeanSlope F hF j (hsemi := (hFsemi j))).trans_lt
      ((EReal.coe_lt_coe (hFA hij)).trans_eq
        (V.A_maximalSlopePayoff_flag_eq_hnMeanSlope F hF i (hsemi := (hFsemi i))).symm)
  · intro i j hij
    exact (V.A_maximalSlopePayoff_flag_eq_hnMeanSlope G hG j (hsemi := (hGsemi j))).trans_lt
      ((EReal.coe_lt_coe (hGA hij)).trans_eq
        (V.A_maximalSlopePayoff_flag_eq_hnMeanSlope G hG i (hsemi := (hGsemi i))).symm)


/-- An actual contractive image in a semistable factor bounds the restricted minimum. -/
theorem minimalSlope_restrict_le_minimalSlope_semistable_factor
    (A B M : Submodule K V) (hMB : M ≤ B) (hMA : ¬ M ≤ A)
    [hQ : ((V.restrictOfNormMeasurability B).quotientOfNormMeasurability
      (A.comap B.subtype)).IsSemistable] :
    (V.restrictOfNormMeasurability M).minimalSlope ≤
      ((V.restrictOfNormMeasurability B).quotientOfNormMeasurability
        (A.comap B.subtype)).minimalSlope := by
  let A₀ := A ⊓ B
  have hcomap : A₀.comap B.subtype = A.comap B.subtype := by
    ext x
    exact and_iff_left x.prop
  have hnot : ¬ M ≤ A₀ := fun h ↦ hMA (h.trans inf_le_left)
  have hsup : M ⊔ A₀ ≤ B := sup_le hMB inf_le_right
  have hAB : A₀ < B := (right_lt_sup.mpr hnot).trans_le hsup
  have hM : ⊥ < M := bot_lt_iff_ne_bot.mpr (fun he ↦ hMA (he ▸ bot_le))
  let I : StrictIntvl (Submodule K V) := ⟨A₀, B, hAB⟩
  let μ := V.maximalSlopePayoff
  have hs : (μ.restrict I).IsSemistable :=
    (V.isSemistable_subquotient_iff_game I).mp (by
      change ((V.restrictOfNormMeasurability B).quotientOfNormMeasurability
        (A₀.comap B.subtype)).IsSemistable
      rwa [hcomap])
  calc
    _ = μ.A ⟨⊥, M, hM⟩ := (V.A_maximalSlopePayoff_bot M hM).symm
    _ ≤ μ.A I := hs.A_le_of_not_le hM bot_le hMB hnot
    _ = _ := by
      rw [V.A_maximalSlopePayoff_eq_minimalSlope I]
      change ((V.restrictOfNormMeasurability B).quotientOfNormMeasurability
        (A₀.comap B.subtype)).minimalSlope = _
      rw [hcomap]

/-- Every actual exhaustive decreasing semistable flag recovers the genuine filtration. -/
theorem hnFiltration_eq_of_semistableFlag {n : ℕ}
    (U : Fin (n + 1) → Submodule K V) (hU : StrictMono U) (hz : U 0 = ⊥)
    (ht : U (Fin.last n) = ⊤)
    [hsemi : ∀ i : Fin n, (V.flagQuotientOfNormMeasurability U i).IsSemistable]
    (hb : StrictAnti (fun i : Fin n ↦ (V.flagQuotientOfNormMeasurability U i).hnMeanSlope
)) (t : ℝ) :
    V.hnFiltration t =
      ⨆ (i : Fin n) (_ : t ≤ (V.flagQuotientOfNormMeasurability U i).hnMeanSlope),
        U i.succ := by
  classical
  let b : Fin n → ℝ := fun i ↦ (V.flagQuotientOfNormMeasurability U i).hnMeanSlope
  have he : ∀ i : Fin n, (V.flagQuotientOfNormMeasurability U i).minimalSlope =
      (b i : EReal) := by
    intro i
    exact ((isSemistable_iff_hnMeanSlope_eq_minimalSlope
      (V.flagQuotientOfNormMeasurability U i) (hsemi i).1).mp (hsemi i)).symm
  have hl := V.le_minimalSlope_restrict_flag_of_factor_minima U b hU.monotone hz
    hb.antitone (fun i ↦ (he i).ge)
  apply le_antisymm
  · rw [V.hnFiltration_eq_minimalSlopeSubspaceSum t]
    apply iSup_le
    intro M
    apply iSup_le
    intro hM
    apply iSup_le
    intro hmin
    let J : Finset (Fin (n + 1)) := Finset.univ.filter (fun j ↦ M ≤ U j)
    have hJ : J.Nonempty := ⟨Fin.last n, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by rw [ht]; exact le_top⟩⟩
    let k := J.min' hJ
    have hkM : M ≤ U k := (Finset.mem_filter.mp (Finset.min'_mem J hJ)).2
    have hkpos : 0 < k.val := by
      by_contra hn
      have hk0 : k = 0 := Fin.ext (by change k.val = 0; omega)
      rw [hk0, hz] at hkM
      exact hM (le_antisymm hkM bot_le)
    let i : Fin n := ⟨k.val - 1, by have h := k.isLt; omega⟩
    have hik : i.succ = k := Fin.ext (by dsimp [i]; omega)
    have hMA : ¬ M ≤ U i.castSucc := by
      intro h
      have hiJ : i.castSucc ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      have hk := Finset.min'_le J i.castSucc hiJ
      change k.val ≤ i.val at hk
      dsimp [i] at hk
      omega
    have hMB : M ≤ U i.succ := by rw [hik]; exact hkM
    have hs := V.minimalSlope_restrict_le_minimalSlope_semistable_factor
      (U i.castSucc) (U i.succ) M hMB hMA (hQ := (hsemi i))
    change (V.restrictOfNormMeasurability M).minimalSlope ≤
      (V.flagQuotientOfNormMeasurability U i).minimalSlope at hs
    rw [he i] at hs
    have hti : t ≤ b i := EReal.coe_le_coe_iff.mp (hmin.trans hs)
    exact hMB.trans (le_iSup_of_le i (le_iSup_of_le hti le_rfl))
  · apply iSup_le
    intro i
    apply iSup_le
    intro hti
    exact V.le_hnFiltration_of_le_minimalSlope_restrict (U i.succ) t
      ((EReal.coe_le_coe hti).trans (hl i))

/-- Source Theorem 4.3.58: the actual exhaustive decreasing semistable flag is unique. -/
theorem existsUnique_hnFlag :
    ∃! p : Σ n : ℕ, Fin (n + 1) → Submodule K V,
      StrictMono p.2 ∧ p.2 0 = ⊥ ∧ p.2 (Fin.last p.1) = ⊤ ∧
      (∀ i : Fin p.1, (V.flagQuotientOfNormMeasurability p.2 i).IsSemistable) ∧
      StrictAnti (fun i : Fin p.1 ↦
        (V.flagQuotientOfNormMeasurability p.2 i).hnMeanSlope) := by
  obtain ⟨n, U, hU, hz, ht, hsemi, hA⟩ :=
    (V.maximalSlopePayoff).exists_finiteFlag
  have hs : ∀ i : Fin n, (V.flagQuotientOfNormMeasurability U i).IsSemistable :=
    fun i ↦ (V.isSemistable_subquotient_iff_game
      ⟨U i.castSucc, U i.succ, hU Fin.castSucc_lt_succ⟩).mpr (hsemi i)
  have hbeta : StrictAnti (fun i : Fin n ↦
      (V.flagQuotientOfNormMeasurability U i).hnMeanSlope) := by
    intro i j hij
    apply EReal.coe_lt_coe_iff.mp
    exact (V.A_maximalSlopePayoff_flag_eq_hnMeanSlope U hU j (hsemi := (hs j))).symm.trans_lt
      ((hA hij).trans_eq (V.A_maximalSlopePayoff_flag_eq_hnMeanSlope U hU i (hsemi := (hs i))))
  refine ⟨⟨n, U⟩, ⟨hU, hz, ht, hs, hbeta⟩, ?_⟩
  rintro ⟨m, F⟩ ⟨hF, hFz, hFt, hFs, hFb⟩
  exact V.hnFlags_eq F U hF hU hFz hz hFt ht (hFsemi := hFs) (hGsemi := hs) hFb hbeta

end

end ArakelovGeometry.AdelicVectorBundle
