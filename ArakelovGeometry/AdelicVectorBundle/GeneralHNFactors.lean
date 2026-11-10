/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.QuotientRestriction
import ArakelovGeometry.AdelicVectorBundle.SlopesExtension
import ArakelovGeometry.AdelicVectorBundle.GeneralHNSemistability
import ArakelovGeometry.AdelicVectorBundle.GeneralHNFlag

/-!
# Actual factors of general HN filtrations

The preimage of a subspace of a quotient contains the quotient kernel.
Its actual quotient and image restriction norms are canonically isometric
on completed fibres. The resulting actual extension minimum bound is used
to prove semistability of the genuine general filtration factors.
-/

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S E)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)

/-- An actual completed quotient isometry transports the genuine minimum. -/
theorem minimalSlope_quotient_restrict_range_eq (U A : Submodule K E) (hA : A ≤ U) :
    ((V.restrictOfMeasurableBase U hS).quotientOfMeasurableBase
      (A.mkQ.comp U.subtype).ker hS).minimalSlope hS hN =
    ((V.quotientOfMeasurableBase A hS).restrictOfMeasurableBase
      (A.mkQ.comp U.subtype).range hS).minimalSlope hS hN := by
  apply minimalSlope_eq_of_completed_isometry _ _ (A.mkQ.comp U.subtype).quotKerEquivRange
    hS hN
  intro ω z
  exact (V.toNormFamily.quotient_restrict_range_norm_eq U A hA ω z).symm

/-- The actual extension minimum bound on the genuine preimage of a quotient subspace. -/
theorem min_minimalSlope_restrict_le_minimalSlope_preimage
    (A : Submodule K E) (G : Submodule K (E ⧸ A)) :
    min ((V.restrictOfMeasurableBase A hS).minimalSlope hS hN)
      (((V.quotientOfMeasurableBase A hS).restrictOfMeasurableBase G hS).minimalSlope hS hN) ≤
    (V.restrictOfMeasurableBase (G.comap A.mkQ) hS).minimalSlope hS hN := by
  let U := G.comap A.mkQ
  have hAU : A ≤ U := A.le_comap_mkQ G
  let P := V.restrictOfMeasurableBase A hS
  let W := V.restrictOfMeasurableBase U hS
  let f : A →ₗ[K] U := Submodule.inclusion hAU
  have hh : P.mapHeight W f ≤ 0 := by
    apply P.mapHeight_le_zero_of_completed_contraction W f
    intro ω z
    have hc : U.subtype.comp f = A.subtype := Submodule.subtype_comp_inclusion _ _ _
    have ht := DFunLike.congr_fun
      (congrArg (fun g ↦ g.baseChange (S.ϕ ω).Completion) hc) z
    simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at ht
    change V.norm ω (U.subtype.baseChange (S.ϕ ω).Completion
      (f.baseChange (S.ϕ ω).Completion z)) ≤
      V.norm ω (A.subtype.baseChange (S.ϕ ω).Completion z)
    rw [ht]
  have hExt := P.minimalSlope_extension_lowerBound W hS hN f
  have hMin : P.minimalSlope hS hN ≤ P.minimalSlope hS hN - P.mapHeight W f := by
    simpa only [sub_zero] using EReal.sub_le_sub (le_refl (P.minimalSlope hS hN)) hh
  have hRange : (A.mkQ.comp U.subtype).range = G := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    exact Submodule.map_comap_eq_of_surjective A.mkQ_surjective G
  have hq := V.minimalSlope_quotient_restrict_range_eq hS hN U A hAU
  rw [LinearMap.ker_comp, Submodule.ker_mkQ] at hq
  have hQr := congrArg
    (fun J : Submodule K (E ⧸ A) ↦
      ((V.quotientOfMeasurableBase A hS).restrictOfMeasurableBase J hS).minimalSlope hS hN)
    hRange
  have hfR : f.range = A.comap U.subtype := Submodule.range_inclusion A U hAU
  have hQf := congrArg
    (fun J : Submodule K U ↦ (W.quotientOfMeasurableBase J hS).minimalSlope hS hN) hfR
  rw [hQf.trans (hq.trans hQr)] at hExt
  exact (min_le_min hMin le_rfl).trans hExt

/-- A subspace of a subspace has the same true minimum on its actual ambient image. -/
theorem minimalSlope_restrict_map_subtype (B : Submodule K E) (G : Submodule K B) :
    ((V.restrictOfMeasurableBase B hS).restrictOfMeasurableBase G hS).minimalSlope hS hN =
      (V.restrictOfMeasurableBase (G.map B.subtype) hS).minimalSlope hS hN := by
  have h := V.minimalSlope_restrict_restrict hS hN (G.map B.subtype) B
    (Submodule.map_subtype_le B G)
  rw [Submodule.comap_map_eq_of_injective B.subtype_injective G] at h
  exact h

/-- A true filtration cut and a strict preceding minimum force actual factor semistability. -/
private theorem generalHNFactor_semistable_of_cut (A B : Submodule K E) (hAB : A < B) (b : ℝ)
    (hB : (V.restrictOfMeasurableBase B hS).minimalSlope hS hN = (b : EReal))
    (hA : (b : EReal) < (V.restrictOfMeasurableBase A hS).minimalSlope hS hN)
    (hcut : ∀ s : ℝ, b < s → V.generalHNFiltration hS hN s ≤ A) :
    let Q := (V.restrictOfMeasurableBase B hS).quotientOfMeasurableBase
      (A.comap B.subtype) hS
    Q.IsSemistable hS hN ∧ Q.minimalSlope hS hN = (b : EReal) ∧
      Q.modifiedSlope hS hN = b := by
  let W := V.restrictOfMeasurableBase B hS
  let I := A.comap B.subtype
  let Q := W.quotientOfMeasurableBase I hS
  have hr : 0 < Module.finrank K (B ⧸ I) := by
    rw [Submodule.finrank_quotient, (Submodule.comapSubtypeEquivOfLe hAB.le).finrank_eq]
    exact Nat.sub_pos_of_lt (Submodule.finrank_lt_finrank_of_lt hAB)
  have hmin : (b : EReal) ≤ Q.minimalSlope hS hN := by
    rw [← hB]
    exact W.minimalSlope_le_minimalSlope_quotient I hS hN
  have hsmall : ∀ G : Submodule K (B ⧸ I), G ≠ ⊥ →
      (Q.restrictOfMeasurableBase G hS).minimalSlope hS hN ≤ (b : EReal) := by
    intro G hG
    by_contra hn
    have hg : (b : EReal) < (Q.restrictOfMeasurableBase G hS).minimalSlope hS hN :=
      lt_of_not_ge hn
    let M := G.comap I.mkQ
    have hp := W.min_minimalSlope_restrict_le_minimalSlope_preimage hS hN I G
    rw [V.minimalSlope_restrict_restrict hS hN A B hAB.le] at hp
    have hm : (b : EReal) < (W.restrictOfMeasurableBase M hS).minimalSlope hS hN :=
      (lt_min hA hg).trans_le hp
    rw [V.minimalSlope_restrict_map_subtype hS hN B M] at hm
    have hM : M ≠ ⊥ := by
      intro hz
      have hmap := Submodule.map_comap_eq_of_surjective I.mkQ_surjective G
      change M.map I.mkQ = G at hmap
      rw [hz, Submodule.map_bot] at hmap
      exact hG hmap.symm
    have hMe : M.map B.subtype ≠ ⊥ := by
      intro hz
      apply hM
      apply Submodule.map_injective_of_injective B.subtype_injective
      simpa only [Submodule.map_bot] using hz
    have hMr : 0 < Module.finrank K (M.map B.subtype) :=
      Nat.pos_of_ne_zero (fun hz ↦ hMe (Submodule.finrank_eq_zero.mp hz))
    obtain ⟨c, hc⟩ := exists_minimalSlope_eq_coe
      (V.restrictOfMeasurableBase (M.map B.subtype) hS) hS hN hMr
    have hbc : b < c := EReal.coe_lt_coe_iff.mp (by simpa only [hc] using hm)
    have hMA := (V.le_generalHNFiltration_of_le_minimalSlope_restrict hS hN
      (M.map B.subtype) c hc.ge).trans (hcut c hbc)
    have hMI : M ≤ I := by
      intro x hx
      exact hMA ⟨x, hx, rfl⟩
    apply hG
    apply le_antisymm _ bot_le
    intro y hy
    obtain ⟨x, hx⟩ := I.mkQ_surjective y
    have hxM : x ∈ M := by change I.mkQ x ∈ G; rw [hx]; exact hy
    have hz : I.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero I).mpr (hMI hxM)
    exact hx.symm.trans hz
  have he : Q.minimalSlope hS hN = (b : EReal) := by
    apply le_antisymm _ hmin
    have htop : (⊤ : Submodule K (B ⧸ I)) ≠ ⊥ := by
      intro hz
      have h0 : Module.finrank K (B ⧸ I) = 0 := by
        have hf := congrArg (fun U : Submodule K (B ⧸ I) ↦ Module.finrank K U) hz
        simpa only [finrank_top, finrank_bot] using hf
      omega
    simpa only [Q.minimalSlope_restrict_top hS hN] using hsmall ⊤ htop
  have hsemi := (Q.isSemistable_iff_minimalSlope_restrict_le hS hN hr).mpr
    (fun G hG ↦ (hsmall G hG).trans he.ge)
  refine ⟨hsemi, he, ?_⟩
  exact EReal.coe_eq_coe_iff.mp
    (((Q.isSemistable_iff_modifiedSlope_eq_minimalSlope hS hN hr).mp hsemi).trans he)

/-- Produce the actual strict general HN flag with semistable actual factors,
whose genuine modified means and minima are its strictly decreasing jumps.
No flag, factor semistability, or completed norm identity is assumed. -/
theorem exists_generalHNFlag_semistable_factors :
    ∃ (n : ℕ) (U : Fin (n + 1) → Submodule K E) (b : Fin n → ℝ),
    StrictMono U ∧ U 0 = ⊥ ∧ U (Fin.last n) = ⊤ ∧ StrictAnti b ∧
      (∀ t, V.generalHNFiltration hS hN t = ⨆ (i : Fin n) (_ : t ≤ b i), U i.succ) ∧
      (∀ i : Fin n, (V.flagQuotientOfMeasurableBase U hS i).IsSemistable hS hN ∧
        (V.flagQuotientOfMeasurableBase U hS i).minimalSlope hS hN = (b i : EReal) ∧
        (V.flagQuotientOfMeasurableBase U hS i).modifiedSlope hS hN = b i) := by
  obtain ⟨n, U, b, hU, hz, ht, hrange, hb, hcut, hat, hright, hrec, hblock, hmin, hsum⟩ :=
    V.exists_generalHNFlag_orderedSlope_sum hS hN
  refine ⟨n, U, b, hU, hz, ht, hb, hrec, fun i ↦ ?_⟩
  have hprev : (b i : EReal) <
      (V.restrictOfMeasurableBase (U i.castSucc) hS).minimalSlope hS hN := by
    by_cases h0 : i.val = 0
    · have he : i.castSucc = 0 := Fin.ext h0
      rw [he, hz]
      have hm := minimalSlope_eq_top_of_finrank_eq_zero
        (V.restrictOfMeasurableBase (⊥ : Submodule K E) hS) hS hN (finrank_bot K E)
      rw [hm]
      exact EReal.coe_lt_top _
    · let ip : Fin n := ⟨i.val - 1, by have hh := i.isLt; omega⟩
      have he : ip.succ = i.castSucc := Fin.ext (by dsimp [ip]; omega)
      have hm := hmin ip
      rw [he] at hm
      rw [hm]
      apply EReal.coe_lt_coe
      exact hb (show ip < i by change ip.val < i.val; dsimp [ip]; omega)
  exact V.generalHNFactor_semistable_of_cut hS hN (U i.castSucc) (U i.succ)
    (hU i.castSucc_lt_succ) (b i)
    (hmin i) hprev (fun s hs ↦ by
      rw [← hright i]
      exact le_iSup_of_le (⟨s, hs⟩ : {s : ℝ // b i < s}) le_rfl)

end

end ArakelovGeometry.AdelicVectorBundle
