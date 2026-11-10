/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.GeneralHNFactors

/-!
# Uniqueness of actual general HN flags

Every flag factor carries its actual restriction and quotient norms.
The actual extension minimum bound controls initial flag terms.
Contractive images of eligible subspaces give the reverse containment.
-/

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S E)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)

/-- The actual extension minimum bound for two nested ambient restrictions. -/
theorem min_minimalSlope_restrict_le_of_le (A B : Submodule K E) (hAB : A ≤ B) :
    min ((V.restrictOfMeasurableBase A hS).minimalSlope hS hN)
      (((V.restrictOfMeasurableBase B hS).quotientOfMeasurableBase
        (A.comap B.subtype) hS).minimalSlope hS hN) ≤
    (V.restrictOfMeasurableBase B hS).minimalSlope hS hN := by
  have h := min_minimalSlope_restrict_le_minimalSlope_preimage
    (V.restrictOfMeasurableBase B hS) hS hN (A.comap B.subtype) ⊤
  simp only [Submodule.comap_top, minimalSlope_restrict_top] at h
  rw [V.minimalSlope_restrict_restrict hS hN A B hAB] at h
  exact h

/-- Decreasing actual factor minima bound every nonzero initial flag term. -/
theorem le_minimalSlope_restrict_flag_of_factor_minima {n : ℕ}
    (U : Fin (n + 1) → Submodule K E) (b : Fin n → ℝ)
    (hU : Monotone U) (hz : U 0 = ⊥) (hb : Antitone b)
    (hQ : ∀ i, (b i : EReal) ≤
      (V.flagQuotientOfMeasurableBase U hS i).minimalSlope hS hN) :
    ∀ i : Fin n, (b i : EReal) ≤
      (V.restrictOfMeasurableBase (U i.succ) hS).minimalSlope hS hN := by
  cases n with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
    intro i
    induction i using Fin.induction with
    | zero =>
      have he := min_minimalSlope_restrict_le_of_le V hS hN (U 0) (U (0 : Fin (n + 1)).succ)
        (hU (Fin.zero_le _))
      rw [hz] at he
      have hm := minimalSlope_eq_top_of_finrank_eq_zero
        (V.restrictOfMeasurableBase (⊥ : Submodule K E) hS) hS hN (finrank_bot K E)
      rw [hm, min_top_left] at he
      have hq := hQ 0
      change (b 0 : EReal) ≤ minimalSlope
        (quotientOfMeasurableBase (V.restrictOfMeasurableBase (U (0 : Fin (n + 1)).succ) hS)
          ((U 0).comap (U (0 : Fin (n + 1)).succ).subtype) hS) hS hN at hq
      rw [hz] at hq
      exact hq.trans he
    | succ i ih =>
      have he := min_minimalSlope_restrict_le_of_le V hS hN (U i.succ.castSucc) (U i.succ.succ)
        (hU i.succ.castSucc_lt_succ.le)
      have hi : i.castSucc.succ = i.succ.castSucc := Fin.ext (by rfl)
      rw [hi] at ih
      have hb' : (b i.succ : EReal) ≤ b i.castSucc := EReal.coe_le_coe
        (hb i.castSucc_lt_succ.le)
      exact (le_min (hb'.trans ih) (hQ i.succ)).trans he

/-- An actual contractive image in a semistable factor bounds the restricted minimum. -/
theorem minimalSlope_restrict_le_minimalSlope_semistable_factor
    (A B M : Submodule K E) (hMB : M ≤ B) (hMA : ¬ M ≤ A)
    (hQ : ((V.restrictOfMeasurableBase B hS).quotientOfMeasurableBase
      (A.comap B.subtype) hS).IsSemistable hS hN) :
    (V.restrictOfMeasurableBase M hS).minimalSlope hS hN ≤
      ((V.restrictOfMeasurableBase B hS).quotientOfMeasurableBase
        (A.comap B.subtype) hS).minimalSlope hS hN := by
  let I := A.comap B.subtype
  let Q := (V.restrictOfMeasurableBase B hS).quotientOfMeasurableBase I hS
  let P := V.restrictOfMeasurableBase M hS
  let j : M →ₗ[K] B := Submodule.inclusion hMB
  let g := I.mkQ.comp j
  let R := Q.restrictOfMeasurableBase g.range hS
  have hg : g ≠ 0 := by
    intro hz
    apply hMA
    intro x hx
    have he : I.mkQ (j ⟨x, hx⟩) = 0 := by
      change g ⟨x, hx⟩ = 0
      rw [hz, LinearMap.zero_apply]
    exact (Submodule.Quotient.mk_eq_zero I).mp he
  have hG : g.range ≠ ⊥ := fun hz ↦ hg (LinearMap.range_eq_bot.mp hz)
  have hgr : g.rangeRestrict ≠ 0 := by
    intro hz
    apply hg
    ext x
    exact congrArg Subtype.val (DFunLike.congr_fun hz x)
  have hh : P.mapHeight R g.rangeRestrict ≤ 0 := by
    apply P.mapHeight_le_zero_of_completed_contraction R g.rangeRestrict
    intro ω z
    have hc : g.range.subtype.comp g.rangeRestrict = g := by ext x; rfl
    have ht := DFunLike.congr_fun
      (congrArg (fun f ↦ f.baseChange (S.ϕ ω).Completion) hc) z
    simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at ht
    change Q.norm ω (g.range.subtype.baseChange (S.ϕ ω).Completion
      (g.rangeRestrict.baseChange (S.ϕ ω).Completion z)) ≤
      V.norm ω (M.subtype.baseChange (S.ϕ ω).Completion z)
    rw [ht]
    have hn := (V.toNormFamily.restrict B).quotient_norm_mk_le I ω
      (j.baseChange (S.ϕ ω).Completion z)
    have hcj : B.subtype.comp j = M.subtype := Submodule.subtype_comp_inclusion _ _ _
    have htj := DFunLike.congr_fun
      (congrArg (fun f ↦ f.baseChange (S.ϕ ω).Completion) hcj) z
    simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at htj
    simpa only [Q, quotientOfMeasurableBase_toNormFamily,
      restrictOfMeasurableBase_toNormFamily, g, LinearMap.baseChange_comp,
      LinearMap.comp_apply, NormFamily.restrict_norm, htj] using hn
  have hp := P.minimalSlope_le_minimalSlope_add_mapHeight_of_surjective R hS hN
    g.rangeRestrict g.surjective_rangeRestrict hgr
  have hs := (Q.isSemistable_iff_minimalSlope_restrict_le hS hN hQ.1).mp hQ g.range hG
  exact (hp.trans (by simpa only [add_zero] using add_le_add le_rfl hh)).trans hs


/-- Every actual exhaustive decreasing semistable flag recovers the genuine filtration. -/
theorem generalHNFiltration_eq_of_semistableFlag {n : ℕ}
    (U : Fin (n + 1) → Submodule K E) (hU : StrictMono U) (hz : U 0 = ⊥)
    (ht : U (Fin.last n) = ⊤)
    (hsemi : ∀ i : Fin n, (V.flagQuotientOfMeasurableBase U hS i).IsSemistable hS hN)
    (hb : StrictAnti (fun i : Fin n ↦ (V.flagQuotientOfMeasurableBase U hS i).modifiedSlope
      hS hN)) (t : ℝ) :
    V.generalHNFiltration hS hN t =
      ⨆ (i : Fin n) (_ : t ≤ (V.flagQuotientOfMeasurableBase U hS i).modifiedSlope hS hN),
        U i.succ := by
  classical
  let b : Fin n → ℝ := fun i ↦ (V.flagQuotientOfMeasurableBase U hS i).modifiedSlope hS hN
  have he : ∀ i : Fin n, (V.flagQuotientOfMeasurableBase U hS i).minimalSlope hS hN =
      (b i : EReal) := by
    intro i
    exact ((isSemistable_iff_modifiedSlope_eq_minimalSlope
      (V.flagQuotientOfMeasurableBase U hS i) hS hN (hsemi i).1).mp (hsemi i)).symm
  have hl := V.le_minimalSlope_restrict_flag_of_factor_minima hS hN U b hU.monotone hz
    hb.antitone (fun i ↦ (he i).ge)
  apply le_antisymm
  · rw [V.generalHNFiltration_eq_generalHNSlopeSum hS hN t]
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
    have hs := V.minimalSlope_restrict_le_minimalSlope_semistable_factor hS hN
      (U i.castSucc) (U i.succ) M hMB hMA (hsemi i)
    change (V.restrictOfMeasurableBase M hS).minimalSlope hS hN ≤
      (V.flagQuotientOfMeasurableBase U hS i).minimalSlope hS hN at hs
    rw [he i] at hs
    have hti : t ≤ b i := EReal.coe_le_coe_iff.mp (hmin.trans hs)
    exact hMB.trans (le_iSup_of_le i (le_iSup_of_le hti le_rfl))
  · apply iSup_le
    intro i
    apply iSup_le
    intro hti
    exact V.le_generalHNFiltration_of_le_minimalSlope_restrict hS hN (U i.succ) t
      ((EReal.coe_le_coe hti).trans (hl i))


/-- Every candidate term is attained at its actual factor modified mean. -/
theorem semistableFlag_succ_eq_generalHNFiltration {n : ℕ}
    (U : Fin (n + 1) → Submodule K E) (hU : StrictMono U) (hz : U 0 = ⊥)
    (ht : U (Fin.last n) = ⊤)
    (hsemi : ∀ i : Fin n, (V.flagQuotientOfMeasurableBase U hS i).IsSemistable hS hN)
    (hb : StrictAnti (fun i : Fin n ↦ (V.flagQuotientOfMeasurableBase U hS i).modifiedSlope
      hS hN)) (i : Fin n) :
    V.generalHNFiltration hS hN
      ((V.flagQuotientOfMeasurableBase U hS i).modifiedSlope hS hN) = U i.succ := by
  rw [V.generalHNFiltration_eq_of_semistableFlag hS hN U hU hz ht hsemi hb]
  apply le_antisymm
  · apply iSup_le
    intro j
    apply iSup_le
    intro hij
    have hji : j ≤ i := by
      by_contra hn
      exact (not_le_of_gt (hb (lt_of_not_ge hn))) hij
    exact hU.monotone (show j.succ ≤ i.succ by
      change j.val + 1 ≤ i.val + 1
      exact Nat.add_le_add_right hji 1)
  · exact le_iSup_of_le i (le_iSup_of_le le_rfl le_rfl)

/-- The complete actual filtration levels are exactly the candidate flag terms. -/
theorem range_generalHNFiltration_eq_of_semistableFlag {n : ℕ}
    (U : Fin (n + 1) → Submodule K E) (hU : StrictMono U) (hz : U 0 = ⊥)
    (ht : U (Fin.last n) = ⊤)
    (hsemi : ∀ i : Fin n, (V.flagQuotientOfMeasurableBase U hS i).IsSemistable hS hN)
    (hb : StrictAnti (fun i : Fin n ↦ (V.flagQuotientOfMeasurableBase U hS i).modifiedSlope
      hS hN)) :
    Set.range (V.generalHNFiltration hS hN) = Set.range U := by
  classical
  let b : Fin n → ℝ := fun i ↦ (V.flagQuotientOfMeasurableBase U hS i).modifiedSlope hS hN
  apply Set.Subset.antisymm
  · rintro W ⟨t, rfl⟩
    let J : Finset (Fin n) := Finset.univ.filter (fun i ↦ t ≤ b i)
    by_cases hJ : J.Nonempty
    · let i := J.max' hJ
      have hi : t ≤ b i := (Finset.mem_filter.mp (Finset.max'_mem J hJ)).2
      refine ⟨i.succ, ?_⟩
      symm
      rw [V.generalHNFiltration_eq_of_semistableFlag hS hN U hU hz ht hsemi hb]
      apply le_antisymm
      · apply iSup_le
        intro j
        apply iSup_le
        intro hj
        have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
        have hji := Finset.le_max' J j hjJ
        exact hU.monotone (show j.succ ≤ i.succ by
          change j.val + 1 ≤ i.val + 1
          exact Nat.add_le_add_right hji 1)
      · exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)
    · refine ⟨0, ?_⟩
      rw [hz, V.generalHNFiltration_eq_of_semistableFlag hS hN U hU hz ht hsemi hb]
      symm
      apply le_antisymm _ bot_le
      apply iSup_le
      intro i
      apply iSup_le
      intro hi
      exact (hJ ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩).elim
  · rintro W ⟨k, rfl⟩
    by_cases hk : k.val = 0
    · obtain ⟨t, ht⟩ := V.exists_generalHNFiltration_eq_bot hS hN
      refine ⟨t, ?_⟩
      rw [show k = 0 from Fin.ext hk, hz]
      exact ht
    · let i : Fin n := ⟨k.val - 1, by have h := k.isLt; omega⟩
      have hik : i.succ = k := Fin.ext (by dsimp [i]; omega)
      exact ⟨b i, (V.semistableFlag_succ_eq_generalHNFiltration
        hS hN U hU hz ht hsemi hb i).trans (congrArg U hik)⟩

/-- Source Theorem 4.3.58: the actual exhaustive decreasing semistable flag is unique. -/
theorem existsUnique_generalHNFlag :
    ∃! p : Σ n : ℕ, Fin (n + 1) → Submodule K E,
      StrictMono p.2 ∧ p.2 0 = ⊥ ∧ p.2 (Fin.last p.1) = ⊤ ∧
      (∀ i : Fin p.1, (V.flagQuotientOfMeasurableBase p.2 hS i).IsSemistable hS hN) ∧
      StrictAnti (fun i : Fin p.1 ↦
        (V.flagQuotientOfMeasurableBase p.2 hS i).modifiedSlope hS hN) := by
  obtain ⟨n, U, b, hU, hz, ht, hb, hrec, hf⟩ :=
    V.exists_generalHNFlag_semistable_factors hS hN
  have hbeta : StrictAnti (fun i : Fin n ↦
      (V.flagQuotientOfMeasurableBase U hS i).modifiedSlope hS hN) := by
    intro i j hij
    simpa only [(hf i).2.2, (hf j).2.2] using hb hij
  refine ⟨⟨n, U⟩, ⟨hU, hz, ht, fun i ↦ (hf i).1, hbeta⟩, ?_⟩
  rintro ⟨m, F⟩ ⟨hF, hFz, hFt, hFs, hFb⟩
  have hRange : Set.range F = Set.range U :=
    (V.range_generalHNFiltration_eq_of_semistableFlag hS hN F hF hFz hFt hFs hFb).symm.trans
      (V.range_generalHNFiltration_eq_of_semistableFlag hS hN U hU hz ht
        (fun i ↦ (hf i).1) hbeta)
  have hcardU := Nat.card_congr (Equiv.ofInjective U hU.injective)
  have hcardF := Nat.card_congr (Equiv.ofInjective F hF.injective)
  have hcardR := congrArg (fun Z : Set (Submodule K E) ↦ Nat.card Z) hRange
  simp only [Nat.card_fin] at hcardU hcardF
  have hmn : m = n := by omega
  subst m
  have hFU : F = U := (hF.range_inj hU).mp hRange
  cases hFU
  rfl

end

end ArakelovGeometry.AdelicVectorBundle
