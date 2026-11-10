/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HermitianHNUniqueness
public import ArakelovGeometry.AdelicVectorBundle.HermitianSemistability
public import ArakelovGeometry.AdelicVectorBundle.RestrictionFunctor
public import ArakelovGeometry.AdelicVectorBundle.SlopesChain

/-!
# Actual initial and quotient-tail Hermitian HN flags

The factors of the initial and final portions use the canonical restriction
and quotient norms on the actual completed fibres. Uniqueness identifies
these portions with the HN flags of the corresponding actual bundles.
-/

@[expose] public section

open scoped BigOperators TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace AdelicVectorBundle

variable [S.IsProper] (V : AdelicVectorBundle S E)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)

omit [S.IsProper] [FiniteDimensional K E] in
/-- The canonical quotient map on a nested restriction has exactly the
pulled-back lower-subspace kernel. -/
theorem nested_restrict_quotient_map_ker (A B C : Submodule K E) (hBC : B ≤ C) :
    ((A.comap B.subtype).mkQ.comp
      (Submodule.comapSubtypeEquivOfLe hBC).toLinearMap).ker =
        (A.comap C.subtype).comap (B.comap C.subtype).subtype := by
  ext x
  change (A.comap B.subtype).mkQ ((Submodule.comapSubtypeEquivOfLe hBC) x) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

omit [S.IsProper] in
/-- Taking a factor after restricting through an intermediate subspace
preserves the actual completed norm under the canonical quotient equivalence. -/
theorem nested_restrict_quotient_norm_eq (ξ : NormFamily S E)
    (A B C : Submodule K E) (hBC : B ≤ C) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      ((B.comap C.subtype) ⧸
        ((A.comap B.subtype).mkQ.comp
          (Submodule.comapSubtypeEquivOfLe hBC).toLinearMap).ker)) :
    let e := Submodule.comapSubtypeEquivOfLe hBC
    let π := (A.comap B.subtype).mkQ.comp e.toLinearMap
    let hπ := (A.comap B.subtype).mkQ_surjective.comp e.surjective
    ((ξ.restrict B).quotient (A.comap B.subtype)).norm ω
      ((π.quotKerEquivOfSurjective hπ).toLinearMap.baseChange (S.ϕ ω).Completion z) =
        (((ξ.restrict C).restrict (B.comap C.subtype)).quotient π.ker).norm ω z := by
  let e := Submodule.comapSubtypeEquivOfLe hBC
  let T := A.comap B.subtype
  let π := T.mkQ.comp e.toLinearMap
  let hπ := T.mkQ_surjective.comp e.surjective
  let η := (ξ.restrict C).restrict (B.comap C.subtype)
  have hp : η.pushforward e.toLinearMap e.surjective = ξ.restrict B := by
    ext ω y
    obtain ⟨x, rfl⟩ := LinearMap.baseChange_surjective (S.ϕ ω).Completion e.surjective y
    rw [η.pushforward_norm_of_injective e.toLinearMap e.surjective e.injective]
    exact ξ.restrict_restrict_norm_eq B C hBC ω x
  change ((ξ.restrict B).quotient T).norm ω
    ((π.quotKerEquivOfSurjective hπ).toLinearMap.baseChange (S.ϕ ω).Completion z) =
      (η.quotient π.ker).norm ω z
  rw [← hp]
  change ((η.pushforward e.toLinearMap e.surjective).pushforward T.mkQ T.mkQ_surjective).norm ω
    ((π.quotKerEquivOfSurjective hπ).toLinearMap.baseChange (S.ϕ ω).Completion z) = _
  rw [η.pushforward_comp_norm]
  exact η.quotient_ker_equiv_norm_eq π hπ ω z

/-- Actual factors in an initial subspace flag remain semistable and
have the original factor mean. -/
theorem nested_restrict_quotient_semistable_slope
    (A B C : Submodule K E) (hBC : B ≤ C)
    (hsemi : ((V.restrictOfMeasurableBase B hS).quotientOfMeasurableBase
      (A.comap B.subtype) hS).IsMeanSlopeSemistable hS hN) :
    let R := quotientOfMeasurableBase
      ((V.restrictOfMeasurableBase C hS).restrictOfMeasurableBase (B.comap C.subtype) hS)
      ((A.comap C.subtype).comap (B.comap C.subtype).subtype) hS
    R.IsMeanSlopeSemistable hS hN ∧ R.slope hS hN =
      ((V.restrictOfMeasurableBase B hS).quotientOfMeasurableBase
        (A.comap B.subtype) hS).slope hS hN := by
  let e := Submodule.comapSubtypeEquivOfLe hBC
  let π := (A.comap B.subtype).mkQ.comp e.toLinearMap
  let hπ := (A.comap B.subtype).mkQ_surjective.comp e.surjective
  let Q := (V.restrictOfMeasurableBase B hS).quotientOfMeasurableBase (A.comap B.subtype) hS
  let R := quotientOfMeasurableBase
    ((V.restrictOfMeasurableBase C hS).restrictOfMeasurableBase (B.comap C.subtype) hS) π.ker hS
  have hn : ∀ ω z, Q.toNormFamily.norm ω
      ((π.quotKerEquivOfSurjective hπ).toLinearMap.baseChange (S.ϕ ω).Completion z) =
        R.toNormFamily.norm ω z := by
    intro ω z
    exact nested_restrict_quotient_norm_eq V.toNormFamily A B C hBC ω z
  have hs := R.slope_eq_of_completed_isometry Q (π.quotKerEquivOfSurjective hπ) hS hN hn
  have hm := R.maximalSlope_eq_of_completed_isometry Q (π.quotKerEquivOfSurjective hπ) hS hN hn
  have hr : 0 < Module.finrank K ((B.comap C.subtype) ⧸ π.ker) := by
    rw [(π.quotKerEquivOfSurjective hπ).finrank_eq]
    exact hsemi.1
  have hQmax := (Q.isMeanSlopeSemistable_iff_maximalSlope_eq_slope hS hN hsemi.1).mp hsemi
  have hR : R.IsMeanSlopeSemistable hS hN ∧ R.slope hS hN = Q.slope hS hN :=
    ⟨(R.isMeanSlopeSemistable_iff_maximalSlope_eq_slope hS hN hr).mpr
      ((hm.trans hQmax).trans (congrArg (fun x : ℝ ↦ (x : EReal)) hs.symm)), hs⟩
  have hk := nested_restrict_quotient_map_ker A B C hBC
  have he := congrArg (fun I : Submodule K (B.comap C.subtype) ↦
    let R := quotientOfMeasurableBase
      ((V.restrictOfMeasurableBase C hS).restrictOfMeasurableBase (B.comap C.subtype) hS) I hS
    R.IsMeanSlopeSemistable hS hN ∧ R.slope hS hN = Q.slope hS hN) hk
  exact Eq.mp he hR

/-- The initial portion of a strict actual semistable flag is the
canonical HN flag of its final restricted subspace, with unchanged factor means. -/
theorem semistableFlag_initial_eq_hermitianHNTerm
    (hH : V.toNormFamily.IsHermitian hN) {n : ℕ}
    (F : Fin (n + 1) → Submodule K E) (hF : StrictMono F) (hzero : F 0 = ⊥)
    (hsemi : ∀ j, (V.flagQuotientOfMeasurableBase F hS j).IsMeanSlopeSemistable hS hN)
    (hβ : StrictAnti (fun j ↦ (V.flagQuotientOfMeasurableBase F hS j).slope hS hN))
    (k : Fin (n + 1)) :
    let C := F k
    let Q := V.restrictOfMeasurableBase C hS
    let idx : Fin (k.val + 1) → Fin (n + 1) := fun j ↦ ⟨j.val, by omega⟩
    let δ : Fin k.val → Fin n := fun j ↦ ⟨j.val, by omega⟩
    let G : Fin (k.val + 1) → Submodule K C := fun j ↦ (F (idx j)).comap C.subtype
    k.val = Q.hermitianHNLength hS hN (hH.restrict C) ∧
      (∀ j, G j = Q.hermitianHNTerm hS hN (hH.restrict C) j.val) ∧
      ∀ j, (Q.flagQuotientOfMeasurableBase G hS j).slope hS hN =
        (V.flagQuotientOfMeasurableBase F hS (δ j)).slope hS hN := by
  let C := F k
  let Q := V.restrictOfMeasurableBase C hS
  let idx : Fin (k.val + 1) → Fin (n + 1) := fun j ↦ ⟨j.val, by omega⟩
  let δ : Fin k.val → Fin n := fun j ↦ ⟨j.val, by omega⟩
  let G : Fin (k.val + 1) → Submodule K C := fun j ↦ (F (idx j)).comap C.subtype
  have hG : StrictMono G := by
    intro a b hab
    have hl : F (idx a) < F (idx b) := hF hab
    apply lt_of_le_of_ne (Submodule.comap_mono hl.le)
    intro heq
    have h : G b ≤ G a := heq.ge
    apply (not_le_of_gt hl)
    intro x hx
    have hC : F (idx b) ≤ C := hF.monotone (show idx b ≤ k by change b.val ≤ k.val; omega)
    exact h (show (⟨x, hC hx⟩ : C) ∈ G b from hx)
  have hz : G 0 = ⊥ := by
    have hi : idx 0 = 0 := Fin.ext (by rfl)
    change (F (idx 0)).comap C.subtype = ⊥
    rw [hi, hzero, Submodule.comap_bot, Submodule.ker_subtype]
  have ht : G (Fin.last k.val) = ⊤ := by
    have hi : idx (Fin.last k.val) = k := Fin.ext (by rfl)
    change (F (idx (Fin.last k.val))).comap C.subtype = ⊤
    rw [hi]
    exact Submodule.comap_subtype_self C
  have hf : ∀ j : Fin k.val,
      (Q.flagQuotientOfMeasurableBase G hS j).IsMeanSlopeSemistable hS hN ∧
      (Q.flagQuotientOfMeasurableBase G hS j).slope hS hN =
        (V.flagQuotientOfMeasurableBase F hS (δ j)).slope hS hN := by
    intro j
    have hBC : F (δ j).succ ≤ C := hF.monotone (show (δ j).succ ≤ k by
      change j.val + 1 ≤ k.val
      omega)
    have hs := V.nested_restrict_quotient_semistable_slope hS hN
      (F (δ j).castSucc) (F (δ j).succ) C hBC (hsemi (δ j))
    have hu : (F (δ j).succ).comap C.subtype = G j.succ := by
      apply congrArg (fun l : Fin (n + 1) ↦ (F l).comap C.subtype)
      apply Fin.ext
      rfl
    have hl : (F (δ j).castSucc).comap C.subtype = G j.castSucc := by
      apply congrArg (fun l : Fin (n + 1) ↦ (F l).comap C.subtype)
      apply Fin.ext
      rfl
    have hp : ((F (δ j).succ).comap C.subtype, (F (δ j).castSucc).comap C.subtype) =
        (G j.succ, G j.castSucc) := Prod.ext hu hl
    have he := congrArg (fun p : Submodule K C × Submodule K C ↦
      let R := quotientOfMeasurableBase (Q.restrictOfMeasurableBase p.1 hS)
        (p.2.comap p.1.subtype) hS
      R.IsMeanSlopeSemistable hS hN ∧ R.slope hS hN =
        (V.flagQuotientOfMeasurableBase F hS (δ j)).slope hS hN) hp
    exact Eq.mp he hs
  have hb : StrictAnti (fun j ↦ (Q.flagQuotientOfMeasurableBase G hS j).slope hS hN) := by
    intro a b hab
    change (Q.flagQuotientOfMeasurableBase G hS b).slope hS hN <
      (Q.flagQuotientOfMeasurableBase G hS a).slope hS hN
    rw [(hf a).2, (hf b).2]
    exact hβ hab
  have he := Q.semistableFlag_eq_hermitianHNTerm hS hN (hH.restrict C)
    G hG hz ht (fun j ↦ (hf j).1) hb
  exact ⟨he.1, he.2, fun j ↦ (hf j).2⟩

/-- The final portion of a complete strict actual semistable flag is the
canonical HN flag of the quotient by its first term, with unchanged factor means. -/
theorem semistableFlag_tail_eq_hermitianHNTerm
    (hH : V.toNormFamily.IsHermitian hN) {n : ℕ}
    (F : Fin (n + 1) → Submodule K E) (hF : StrictMono F)
    (htop : F (Fin.last n) = ⊤)
    (hsemi : ∀ j, (V.flagQuotientOfMeasurableBase F hS j).IsMeanSlopeSemistable hS hN)
    (hβ : StrictAnti (fun j ↦ (V.flagQuotientOfMeasurableBase F hS j).slope hS hN))
    (k : Fin (n + 1)) :
    let D := F k
    let Q := V.quotientOfMeasurableBase D hS
    let m := n - k.val
    let idx : Fin (m + 1) → Fin (n + 1) := fun j ↦ ⟨j.val + k.val, by omega⟩
    let δ : Fin m → Fin n := fun j ↦ ⟨j.val + k.val, by omega⟩
    let G : Fin (m + 1) → Submodule K (E ⧸ D) := fun j ↦ (F (idx j)).map D.mkQ
    m = Q.hermitianHNLength hS hN (hH.quotient D) ∧
      (∀ j, G j = Q.hermitianHNTerm hS hN (hH.quotient D) j.val) ∧
      ∀ j, (Q.flagQuotientOfMeasurableBase G hS j).slope hS hN =
        (V.flagQuotientOfMeasurableBase F hS (δ j)).slope hS hN := by
  let D := F k
  let Q := V.quotientOfMeasurableBase D hS
  let m := n - k.val
  let idx : Fin (m + 1) → Fin (n + 1) := fun j ↦ ⟨j.val + k.val, by omega⟩
  let δ : Fin m → Fin n := fun j ↦ ⟨j.val + k.val, by omega⟩
  let G : Fin (m + 1) → Submodule K (E ⧸ D) := fun j ↦ (F (idx j)).map D.mkQ
  have hG : StrictMono G := by
    intro a b hab
    have hl : F (idx a) < F (idx b) := hF (show idx a < idx b by
      change a.val + k.val < b.val + k.val
      exact Nat.add_lt_add_right hab k.val)
    have ha : D ≤ F (idx a) := hF.monotone (show k ≤ idx a by
      change k.val ≤ a.val + k.val
      omega)
    have hb : D ≤ F (idx b) := hF.monotone (show k ≤ idx b by
      change k.val ≤ b.val + k.val
      omega)
    apply lt_of_le_of_ne (Submodule.map_mono hl.le)
    intro heq
    have he := congrArg (fun U : Submodule K (E ⧸ D) ↦ U.comap D.mkQ) heq
    rw [Submodule.comap_map_eq_self (show D.mkQ.ker ≤ F (idx a) by
      rw [Submodule.ker_mkQ]; exact ha),
      Submodule.comap_map_eq_self (show D.mkQ.ker ≤ F (idx b) by
        rw [Submodule.ker_mkQ]; exact hb)] at he
    exact (ne_of_lt hl) he
  have hz : G 0 = ⊥ := by
    have hi : idx 0 = k := Fin.ext (by simp [idx])
    change (F (idx 0)).map D.mkQ = ⊥
    rw [hi]
    exact Submodule.mkQ_map_self D
  have ht : G (Fin.last m) = ⊤ := by
    have hi : idx (Fin.last m) = Fin.last n := Fin.ext (by dsimp [idx, m]; omega)
    change (F (idx (Fin.last m))).map D.mkQ = ⊤
    rw [hi, htop, Submodule.map_top, LinearMap.range_eq_top.mpr D.mkQ_surjective]
  have hf : ∀ j : Fin m,
      (Q.flagQuotientOfMeasurableBase G hS j).IsMeanSlopeSemistable hS hN ∧
      (Q.flagQuotientOfMeasurableBase G hS j).slope hS hN =
        (V.flagQuotientOfMeasurableBase F hS (δ j)).slope hS hN := by
    intro j
    have hDA : D ≤ F (δ j).castSucc := hF.monotone (show k ≤ (δ j).castSucc by
      change k.val ≤ j.val + k.val
      omega)
    have hAB : F (δ j).castSucc ≤ F (δ j).succ :=
      hF.monotone (Fin.castSucc_le_succ (δ j))
    have hs := V.nested_quotient_map_semistable_slope hS hN
      D (F (δ j).castSucc) (F (δ j).succ) hDA hAB (hsemi (δ j))
    have hu : (F (δ j).succ).map D.mkQ = G j.succ := by
      apply congrArg (fun l : Fin (n + 1) ↦ (F l).map D.mkQ)
      apply Fin.ext
      dsimp [δ, idx]
      omega
    have hl : (F (δ j).castSucc).map D.mkQ = G j.castSucc := by
      apply congrArg (fun l : Fin (n + 1) ↦ (F l).map D.mkQ)
      apply Fin.ext
      rfl
    have hp : ((F (δ j).succ).map D.mkQ, (F (δ j).castSucc).map D.mkQ) =
        (G j.succ, G j.castSucc) := Prod.ext hu hl
    have he := congrArg (fun p : Submodule K (E ⧸ D) × Submodule K (E ⧸ D) ↦
      let R := quotientOfMeasurableBase (Q.restrictOfMeasurableBase p.1 hS)
        (p.2.comap p.1.subtype) hS
      R.IsMeanSlopeSemistable hS hN ∧ R.slope hS hN =
        (V.flagQuotientOfMeasurableBase F hS (δ j)).slope hS hN) hp
    exact Eq.mp he hs
  have hb : StrictAnti (fun j ↦ (Q.flagQuotientOfMeasurableBase G hS j).slope hS hN) := by
    intro a b hab
    change (Q.flagQuotientOfMeasurableBase G hS b).slope hS hN <
      (Q.flagQuotientOfMeasurableBase G hS a).slope hS hN
    rw [(hf a).2, (hf b).2]
    apply hβ
    change a.val + k.val < b.val + k.val
    exact Nat.add_lt_add_right hab k.val
  have he := Q.semistableFlag_eq_hermitianHNTerm hS hN (hH.quotient D)
    G hG hz ht (fun j ↦ (hf j).1) hb
  exact ⟨he.1, he.2, fun j ↦ (hf j).2⟩

/-- The canonical HN flag quotients are actual nonzero semistable bundles. -/
theorem isMeanSlopeSemistable_hermitianHNFlag_quotient
    (hH : V.toNormFamily.IsHermitian hN) (i : Fin (V.hermitianHNLength hS hN hH)) :
    (V.flagQuotientOfMeasurableBase
      (V.hermitianHNFlag hS hN hH) hS i).IsMeanSlopeSemistable hS hN := by
  let U := V.hermitianHNTerm hS hN hH (i.val + 1)
  let W := V.hermitianHNTerm hS hN hH i.val
  have hk : (W.mkQ.comp U.subtype).ker = W.comap U.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have he := congrArg (fun I : Submodule K U ↦
    IsMeanSlopeSemistable
      ((V.restrictOfMeasurableBase U hS).quotientOfMeasurableBase I hS) hS hN) hk
  exact Eq.mp he (V.hermitianHNSubquotient_semistable_slope hS hN hH i).1

/-- The canonical HN flag quotient means are strictly decreasing. -/
theorem hermitianHNFlag_quotient_slope_strictAnti
    (hH : V.toNormFamily.IsHermitian hN) :
    StrictAnti (fun i ↦
      (V.flagQuotientOfMeasurableBase (V.hermitianHNFlag hS hN hH) hS i).slope hS hN) := by
  intro i j hij
  change (V.flagQuotientOfMeasurableBase (V.hermitianHNFlag hS hN hH) hS j).slope hS hN <
    (V.flagQuotientOfMeasurableBase (V.hermitianHNFlag hS hN hH) hS i).slope hS hN
  rw [V.slope_hermitianHNFlag_quotient_eq_factor hS hN hH i,
    V.slope_hermitianHNFlag_quotient_eq_factor hS hN hH j]
  exact V.hermitianHNFactor_slope_strictAnti hS hN hH hij

/-- Restricting to the k-th actual HN term gives precisely its initial
k-term HN flag on the canonical rational subspaces. -/
theorem hermitianHN_restrict_initial_flag
    (hH : V.toNormFamily.IsHermitian hN) (k : Fin (V.hermitianHNLength hS hN hH + 1)) :
    let C := V.hermitianHNTerm hS hN hH k.val
    let Q := V.restrictOfMeasurableBase C hS
    k.val = Q.hermitianHNLength hS hN (hH.restrict C) ∧
      ∀ j : Fin (k.val + 1),
        (V.hermitianHNTerm hS hN hH j.val).comap C.subtype =
          Q.hermitianHNTerm hS hN (hH.restrict C) j.val := by
  have he := V.semistableFlag_initial_eq_hermitianHNTerm hS hN hH
    (V.hermitianHNFlag hS hN hH) (V.hermitianHNFlag_strictMono hS hN hH)
    (V.hermitianHNFlag_zero hS hN hH)
    (V.isMeanSlopeSemistable_hermitianHNFlag_quotient hS hN hH)
    (V.hermitianHNFlag_quotient_slope_strictAnti hS hN hH) k
  exact ⟨he.1, he.2.1⟩

/-- Quotienting by the k-th actual HN term gives precisely the actual
remaining HN flag, with its canonical quotient images. -/
theorem hermitianHN_quotient_tail_flag
    (hH : V.toNormFamily.IsHermitian hN) (k : Fin (V.hermitianHNLength hS hN hH + 1)) :
    let D := V.hermitianHNTerm hS hN hH k.val
    let Q := V.quotientOfMeasurableBase D hS
    V.hermitianHNLength hS hN hH - k.val = Q.hermitianHNLength hS hN (hH.quotient D) ∧
      ∀ j : Fin (V.hermitianHNLength hS hN hH - k.val + 1),
        (V.hermitianHNTerm hS hN hH (j.val + k.val)).map D.mkQ =
          Q.hermitianHNTerm hS hN (hH.quotient D) j.val := by
  have he := V.semistableFlag_tail_eq_hermitianHNTerm hS hN hH
    (V.hermitianHNFlag hS hN hH) (V.hermitianHNFlag_strictMono hS hN hH)
    (V.hermitianHNFlag_last hS hN hH)
    (V.isMeanSlopeSemistable_hermitianHNFlag_quotient hS hN hH)
    (V.hermitianHNFlag_quotient_slope_strictAnti hS hN hH) k
  exact ⟨he.1, he.2.1⟩

/-- Every factor mean of an actual HN initial restriction is the
corresponding original factor mean, under the produced length equality. -/
theorem slope_hermitianHNFactor_restrict_term_eq
    (hH : V.toNormFamily.IsHermitian hN) (k : Fin (V.hermitianHNLength hS hN hH + 1))
    (j : Fin k.val) :
    let C := V.hermitianHNTerm hS hN hH k.val
    let Q := V.restrictOfMeasurableBase C hS
    let hlen := (V.hermitianHN_restrict_initial_flag hS hN hH k).1
    (Q.hermitianHNFactor hS hN (hH.restrict C) (Fin.cast hlen j)).slope hS hN =
      (V.hermitianHNFactor hS hN hH ⟨j.val, by omega⟩).slope hS hN := by
  let C := V.hermitianHNTerm hS hN hH k.val
  let Q := V.restrictOfMeasurableBase C hS
  let hlen := (V.hermitianHN_restrict_initial_flag hS hN hH k).1
  let jQ := Fin.cast hlen j
  let i : Fin (V.hermitianHNLength hS hN hH) := ⟨j.val, by omega⟩
  let G : Fin (k.val + 1) → Submodule K C := fun l ↦
    (V.hermitianHNTerm hS hN hH l.val).comap C.subtype
  have ht := (V.hermitianHN_restrict_initial_flag hS hN hH k).2
  have hp : (G j.succ, G j.castSucc) =
      ((Q.hermitianHNFlag hS hN (hH.restrict C)) jQ.succ,
        (Q.hermitianHNFlag hS hN (hH.restrict C)) jQ.castSucc) :=
    Prod.ext (ht j.succ) (ht j.castSucc)
  have hc := congrArg (fun p : Submodule K C × Submodule K C ↦
    (quotientOfMeasurableBase (Q.restrictOfMeasurableBase p.1 hS)
      (p.2.comap p.1.subtype) hS).slope hS hN) hp
  have he := V.semistableFlag_initial_eq_hermitianHNTerm hS hN hH
    (V.hermitianHNFlag hS hN hH) (V.hermitianHNFlag_strictMono hS hN hH)
    (V.hermitianHNFlag_zero hS hN hH)
    (V.isMeanSlopeSemistable_hermitianHNFlag_quotient hS hN hH)
    (V.hermitianHNFlag_quotient_slope_strictAnti hS hN hH) k
  exact (Q.slope_hermitianHNFlag_quotient_eq_factor hS hN (hH.restrict C) jQ).symm.trans
    (hc.symm.trans ((he.2.2 j).trans (V.slope_hermitianHNFlag_quotient_eq_factor hS hN hH i)))

/-- Every factor mean of an actual HN quotient tail is the corresponding
original factor mean, under the produced length equality. -/
theorem slope_hermitianHNFactor_quotient_term_eq
    (hH : V.toNormFamily.IsHermitian hN) (k : Fin (V.hermitianHNLength hS hN hH + 1))
    (j : Fin (V.hermitianHNLength hS hN hH - k.val)) :
    let D := V.hermitianHNTerm hS hN hH k.val
    let Q := V.quotientOfMeasurableBase D hS
    let hlen := (V.hermitianHN_quotient_tail_flag hS hN hH k).1
    (Q.hermitianHNFactor hS hN (hH.quotient D) (Fin.cast hlen j)).slope hS hN =
      (V.hermitianHNFactor hS hN hH ⟨j.val + k.val, by omega⟩).slope hS hN := by
  let D := V.hermitianHNTerm hS hN hH k.val
  let Q := V.quotientOfMeasurableBase D hS
  let hlen := (V.hermitianHN_quotient_tail_flag hS hN hH k).1
  let jQ := Fin.cast hlen j
  let i : Fin (V.hermitianHNLength hS hN hH) := ⟨j.val + k.val, by omega⟩
  let G : Fin (V.hermitianHNLength hS hN hH - k.val + 1) → Submodule K (E ⧸ D) :=
    fun l ↦ (V.hermitianHNTerm hS hN hH (l.val + k.val)).map D.mkQ
  have ht := (V.hermitianHN_quotient_tail_flag hS hN hH k).2
  have hp : (G j.succ, G j.castSucc) =
      ((Q.hermitianHNFlag hS hN (hH.quotient D)) jQ.succ,
        (Q.hermitianHNFlag hS hN (hH.quotient D)) jQ.castSucc) :=
    Prod.ext (ht j.succ) (ht j.castSucc)
  have hc := congrArg (fun p : Submodule K (E ⧸ D) × Submodule K (E ⧸ D) ↦
    (quotientOfMeasurableBase (Q.restrictOfMeasurableBase p.1 hS)
      (p.2.comap p.1.subtype) hS).slope hS hN) hp
  have he := V.semistableFlag_tail_eq_hermitianHNTerm hS hN hH
    (V.hermitianHNFlag hS hN hH) (V.hermitianHNFlag_strictMono hS hN hH)
    (V.hermitianHNFlag_last hS hN hH)
    (V.isMeanSlopeSemistable_hermitianHNFlag_quotient hS hN hH)
    (V.hermitianHNFlag_quotient_slope_strictAnti hS hN hH) k
  exact (Q.slope_hermitianHNFlag_quotient_eq_factor hS hN (hH.quotient D) jQ).symm.trans
    (hc.symm.trans ((he.2.2 j).trans (V.slope_hermitianHNFlag_quotient_eq_factor hS hN hH i)))

/-- The actual remaining quotient above an HN threshold has maximal
slope strictly below that threshold, including the zero quotient. -/
theorem maximalSlope_quotient_hermitianHNFiltration_lt
    (hH : V.toNormFamily.IsHermitian hN) (t : ℝ) :
    (V.quotientOfMeasurableBase (V.hermitianHNFiltration hS hN hH t) hS).maximalSlope hS hN <
      (t : EReal) := by
  let c := V.hermitianHNCut hS hN hH t
  have hcl := V.hermitianHNCut_le_length hS hN hH t
  by_cases hc : c = V.hermitianHNLength hS hN hH
  · have hU : V.hermitianHNFiltration hS hN hH t = ⊤ :=
      (congrArg (V.hermitianHNTerm hS hN hH) hc).trans
        (V.hermitianHNTerm_length_eq_top hS hN hH)
    have hr : Module.finrank K (E ⧸ V.hermitianHNFiltration hS hN hH t) = 0 := by
      have h := (V.hermitianHNFiltration hS hN hH t).finrank_quotient_add_finrank
      have hF := congrArg (fun U : Submodule K E ↦ Module.finrank K U) hU
      rw [finrank_top] at hF
      omega
    rw [maximalSlope_eq_bot_of_finrank_eq_zero _ hS hN hr]
    exact EReal.bot_lt_coe t
  · let i : Fin (V.hermitianHNLength hS hN hH) := ⟨c, by dsimp [c] at *; omega⟩
    have ht : (V.hermitianHNFactor hS hN hH i).slope hS hN < t := by
      apply lt_of_not_ge
      intro hi
      have hb := (V.le_hermitianHNFactor_slope_iff_lt_cut hS hN hH t i).mp hi
      exact (Nat.lt_irrefl c) hb
    have hm := V.slope_hermitianHNFactor_eq_maximalSlope_quotient hS hN hH i
    exact hm.symm.trans_lt (EReal.coe_lt_coe_iff.mpr ht)

/-- Actual inclusion tails have nonpositive height, so the accepted chain
inequality bounds a restricted endpoint by the actual means of semistable factors. -/
theorem le_minimalSlope_restrict_last_of_semistableFlag
    (hH : V.toNormFamily.IsHermitian hN) {n : ℕ}
    (F : Fin (n + 1) → Submodule K E) (hF : Monotone F) (hzero : F 0 = ⊥)
    (hsemi : ∀ i, (V.flagQuotientOfMeasurableBase F hS i).IsMeanSlopeSemistable hS hN)
    (t : ℝ) (hμ : ∀ i, t ≤ (V.flagQuotientOfMeasurableBase F hS i).slope hS hN) :
    (t : EReal) ≤ (V.restrictOfMeasurableBase (F (Fin.last n)) hS).minimalSlope hS hN := by
  let A : Fin (n + 1) → Type w := fun i ↦ F i
  let W : ∀ i, AdelicVectorBundle S (A i) := fun i ↦ V.restrictOfMeasurableBase (F i) hS
  let α : ∀ i : Fin n, A i.castSucc →ₗ[K] A i.succ :=
    fun i ↦ Submodule.inclusion (hF (Fin.castSucc_le_succ i))
  have htail : ∀ i : Fin (n + 1), linearChainTailMap A α i =
      Submodule.inclusion (hF (Fin.le_last i)) := by
    intro i
    induction i using Fin.reverseInduction with
    | last =>
      rw [linearChainTailMap_last]
      ext x
      rfl
    | cast i ih =>
      rw [linearChainTailMap_castSucc, ih]
      ext x
      rfl
  have hheight : ∀ i : Fin (n + 1),
      (W i).mapHeight (W (Fin.last n)) (linearChainTailMap A α i) ≤ 0 := by
    intro i
    apply mapHeight_le_zero_of_completed_contraction
    intro ω z
    rw [htail i]
    let f := Submodule.inclusion (hF (Fin.le_last i))
    have he : (F (Fin.last n)).subtype.comp f = (F i).subtype := by
      ext x
      rfl
    have hz := DFunLike.congr_fun
      (congrArg (fun f ↦ f.baseChange (S.ϕ ω).Completion) he) z
    rw [LinearMap.baseChange_comp, LinearMap.comp_apply] at hz
    change V.toNormFamily.norm ω
      ((F (Fin.last n)).subtype.baseChange (S.ϕ ω).Completion (f.baseChange _ z)) ≤
        V.toNormFamily.norm ω ((F i).subtype.baseChange (S.ϕ ω).Completion z)
    exact le_of_eq (congrArg (V.toNormFamily.norm ω) hz)
  have h0 : Module.finrank K (A 0) = 0 :=
    (congrArg (fun U : Submodule K E ↦ Module.finrank K U) hzero).trans (finrank_bot K E)
  have hc := minimalSlope_linearChain_lowerBound A W α hS hN h0
  refine (le_iInf fun i ↦ ?_).trans hc
  let j := i.val
  let R := (W j.succ).quotientOfMeasurableBase (α j).range hS
  have hrange : (α j).range = (F j.castSucc).comap (F j.succ).subtype :=
    Submodule.range_inclusion _ _ (hF (Fin.castSucc_le_succ j))
  have hp := congrArg (fun I : Submodule K (F j.succ) ↦
    IsMeanSlopeSemistable ((W j.succ).quotientOfMeasurableBase I hS) hS hN) hrange
  have hs : R.IsMeanSlopeSemistable hS hN := Eq.mpr hp (hsemi j)
  have hm := (R.isMeanSlopeSemistable_iff_minimalSlope_eq_slope_of_isHermitian hS hN
    ((hH.restrict (F j.succ)).quotient (α j).range) hs.1).mp hs
  have he := congrArg (fun I : Submodule K (F j.succ) ↦
    ((W j.succ).quotientOfMeasurableBase I hS).slope hS hN) hrange
  have ht : (t : EReal) ≤ R.minimalSlope hS hN := by
    rw [hm]
    exact EReal.coe_le_coe_iff.mpr ((hμ j).trans_eq he.symm)
  calc
    (t : EReal) ≤ R.minimalSlope hS hN := ht
    _ = R.minimalSlope hS hN - 0 := by simp
    _ ≤ R.minimalSlope hS hN -
        (W j.succ).mapHeight (W (Fin.last n)) (linearChainTailMap A α j.succ) :=
      EReal.sub_le_sub le_rfl (hheight j.succ)

/-- The actual restricted subspace retained at an HN threshold has minimal
slope at least that threshold; the zero retained subspace has minimal slope top. -/
theorem le_minimalSlope_restrict_hermitianHNFiltration
    (hH : V.toNormFamily.IsHermitian hN) (t : ℝ) :
    (t : EReal) ≤
      (V.restrictOfMeasurableBase (V.hermitianHNFiltration hS hN hH t) hS).minimalSlope hS hN := by
  let c := V.hermitianHNCut hS hN hH t
  have hcl := V.hermitianHNCut_le_length hS hN hH t
  by_cases hc : c = 0
  · have hU : V.hermitianHNFiltration hS hN hH t = ⊥ :=
      (congrArg (V.hermitianHNTerm hS hN hH) hc).trans (V.hermitianHNTerm_zero hS hN hH)
    have hr : Module.finrank K (V.hermitianHNFiltration hS hN hH t) = 0 :=
      (congrArg (fun U : Submodule K E ↦ Module.finrank K U) hU).trans (finrank_bot K E)
    rw [minimalSlope_eq_top_of_finrank_eq_zero _ hS hN hr]
    exact le_top
  · let F : Fin (c + 1) → Submodule K E := fun j ↦ V.hermitianHNTerm hS hN hH j.val
    let δ : Fin c → Fin (V.hermitianHNLength hS hN hH) := fun j ↦ ⟨j.val, by omega⟩
    have hF : Monotone F := fun _ _ h ↦ V.hermitianHNTerm_monotone hS hN hH h
    have hz : F 0 = ⊥ := V.hermitianHNTerm_zero hS hN hH
    have hs : ∀ j, (V.flagQuotientOfMeasurableBase F hS j).IsMeanSlopeSemistable hS hN := by
      intro j
      exact V.isMeanSlopeSemistable_hermitianHNFlag_quotient hS hN hH (δ j)
    have hμ : ∀ j, t ≤ (V.flagQuotientOfMeasurableBase F hS j).slope hS hN := by
      intro j
      change t ≤ (V.flagQuotientOfMeasurableBase (V.hermitianHNFlag hS hN hH) hS (δ j)).slope hS hN
      rw [V.slope_hermitianHNFlag_quotient_eq_factor hS hN hH (δ j)]
      exact (V.le_hermitianHNFactor_slope_iff_lt_cut hS hN hH t (δ j)).mpr j.isLt
    exact V.le_minimalSlope_restrict_last_of_semistableFlag hS hN hH F hF hz hs t hμ

end AdelicVectorBundle

end

end ArakelovGeometry
