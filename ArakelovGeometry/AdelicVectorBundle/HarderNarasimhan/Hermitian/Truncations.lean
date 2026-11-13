/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.Basic
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Basic
public import ArakelovGeometry.AdelicVectorBundle.Slope.Subquotient

import ArakelovGeometry.AdelicVectorBundle.Degree.Supermodular
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Semistability
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Uniqueness
import ArakelovGeometry.AdelicVectorBundle.Slope.Chain
import ArakelovGeometry.AdelicVectorBundle.Slope.Quotient
import ArakelovGeometry.AdelicVectorBundle.Subquotient.Restriction.Functor
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

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

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace AdelicVectorBundle

variable [S.IsProper] (V : AdelicVectorBundle S)
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]


/-- Actual factors in an initial subspace flag remain semistable and
have the original factor mean. -/
theorem nested_restrict_quotient_semistable_slope
    (A B C : Submodule K V) (hBC : B ≤ C)
    [hsemi : ((V.restrictOfNormMeasurability B).quotientOfNormMeasurability
      (A.comap B.subtype)).IsMeanSlopeSemistable] :
    let R := quotientOfNormMeasurability
      ((V.restrictOfNormMeasurability C).restrictOfNormMeasurability (B.comap C.subtype))
      ((A.comap C.subtype).comap (B.comap C.subtype).subtype)
    R.IsMeanSlopeSemistable ∧ R.slope =
      ((V.restrictOfNormMeasurability B).quotientOfNormMeasurability
        (A.comap B.subtype)).slope := by
  let e := Submodule.comapSubtypeEquivOfLe hBC
  let π := (A.comap B.subtype).mkQ.comp e.toLinearMap
  let hπ := (A.comap B.subtype).mkQ_surjective.comp e.surjective
  let Q := (V.restrictOfNormMeasurability B).quotientOfNormMeasurability (A.comap B.subtype)
  let R := quotientOfNormMeasurability
    ((V.restrictOfNormMeasurability C).restrictOfNormMeasurability (B.comap C.subtype)) π.ker
  have hn : ∀ ω z, Q.toNormFamily.norm ω
      ((π.quotKerEquivOfSurjective hπ).toLinearMap.baseChange (S.ϕ ω).Completion z) =
        R.toNormFamily.norm ω z := by
    intro ω z
    exact nested_restrict_quotient_norm_eq V.toNormFamily A B C hBC ω z
  have hs := R.slope_eq_of_completed_isometry Q (π.quotKerEquivOfSurjective hπ) hn
  have hm := R.maximalSlope_eq_of_completed_isometry Q (π.quotKerEquivOfSurjective hπ) hn
  have hr : 0 < Module.finrank K ((B.comap C.subtype) ⧸ π.ker) := by
    rw [(π.quotKerEquivOfSurjective hπ).finrank_eq]
    exact hsemi.1
  have hQmax := (Q.isMeanSlopeSemistable_iff_maximalSlope_eq_slope hsemi.1).mp hsemi
  have hR : R.IsMeanSlopeSemistable ∧ R.slope = Q.slope :=
    ⟨(R.isMeanSlopeSemistable_iff_maximalSlope_eq_slope hr).mpr
      ((hm.trans hQmax).trans (congrArg (fun x : ℝ ↦ (x : EReal)) hs.symm)), hs⟩
  have hk := nested_restrict_quotient_map_ker A B C hBC
  have he := congrArg (fun I : Submodule K (B.comap C.subtype) ↦
    let R := quotientOfNormMeasurability
      ((V.restrictOfNormMeasurability C).restrictOfNormMeasurability (B.comap C.subtype)) I
    R.IsMeanSlopeSemistable ∧ R.slope = Q.slope) hk
  exact Eq.mp he hR

/-- The initial portion of a strict actual semistable flag is the
canonical HN flag of its final restricted subspace, with unchanged factor means. -/
theorem semistableFlag_initial_eq_hermitianHNTerm
    [hH : V.toNormFamily.IsHermitian] {n : ℕ}
    (F : Fin (n + 1) → Submodule K V) (hF : StrictMono F) (hzero : F 0 = ⊥)
    [hsemi : ∀ j, (V.flagQuotientOfNormMeasurability F j).IsMeanSlopeSemistable]
    (hβ : StrictAnti (fun j ↦ (V.flagQuotientOfNormMeasurability F j).slope))
    (k : Fin (n + 1)) :
    let C := F k
    let Q := V.restrictOfNormMeasurability C
    let idx : Fin (k.val + 1) → Fin (n + 1) := fun j ↦ ⟨j.val, by omega⟩
    let δ : Fin k.val → Fin n := fun j ↦ ⟨j.val, by omega⟩
    let G : Fin (k.val + 1) → Submodule K C := fun j ↦ (F (idx j)).comap C.subtype
    k.val = Q.hermitianHNLength (hV := (hH.restrict C)) ∧
      (∀ j, G j = Q.hermitianHNTerm (hV := (hH.restrict C)) j.val) ∧
      ∀ j, (Q.flagQuotientOfNormMeasurability G j).slope =
        (V.flagQuotientOfNormMeasurability F (δ j)).slope := by
  let C := F k
  let Q := V.restrictOfNormMeasurability C
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
      (Q.flagQuotientOfNormMeasurability G j).IsMeanSlopeSemistable ∧
      (Q.flagQuotientOfNormMeasurability G j).slope =
        (V.flagQuotientOfNormMeasurability F (δ j)).slope := by
    intro j
    have hBC : F (δ j).succ ≤ C := hF.monotone (show (δ j).succ ≤ k by
      change j.val + 1 ≤ k.val
      omega)
    have hs := V.nested_restrict_quotient_semistable_slope
      (F (δ j).castSucc) (F (δ j).succ) C hBC (hsemi := (hsemi (δ j)))
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
      let R := quotientOfNormMeasurability (Q.restrictOfNormMeasurability p.1)
        (p.2.comap p.1.subtype)
      R.IsMeanSlopeSemistable ∧ R.slope =
        (V.flagQuotientOfNormMeasurability F (δ j)).slope) hp
    exact Eq.mp he hs
  have hb : StrictAnti (fun j ↦ (Q.flagQuotientOfNormMeasurability G j).slope) := by
    intro a b hab
    change (Q.flagQuotientOfNormMeasurability G b).slope <
      (Q.flagQuotientOfNormMeasurability G a).slope
    rw [(hf a).2, (hf b).2]
    exact hβ hab
  have he := Q.semistableFlag_eq_hermitianHNTerm (hH := (hH.restrict C))
    G hG hz ht (hsemi := (fun j ↦ (hf j).1)) hb
  exact ⟨he.1, he.2, fun j ↦ (hf j).2⟩

/-- The final portion of a complete strict actual semistable flag is the
canonical HN flag of the quotient by its first term, with unchanged factor means. -/
theorem semistableFlag_tail_eq_hermitianHNTerm
    [hH : V.toNormFamily.IsHermitian] {n : ℕ}
    (F : Fin (n + 1) → Submodule K V) (hF : StrictMono F)
    (htop : F (Fin.last n) = ⊤)
    [hsemi : ∀ j, (V.flagQuotientOfNormMeasurability F j).IsMeanSlopeSemistable]
    (hβ : StrictAnti (fun j ↦ (V.flagQuotientOfNormMeasurability F j).slope))
    (k : Fin (n + 1)) :
    let D := F k
    let Q := V.quotientOfNormMeasurability D
    let m := n - k.val
    let idx : Fin (m + 1) → Fin (n + 1) := fun j ↦ ⟨j.val + k.val, by omega⟩
    let δ : Fin m → Fin n := fun j ↦ ⟨j.val + k.val, by omega⟩
    let G : Fin (m + 1) → Submodule K (V ⧸ D) := fun j ↦ (F (idx j)).map D.mkQ
    m = Q.hermitianHNLength (hV := (hH.quotient D)) ∧
      (∀ j, G j = Q.hermitianHNTerm (hV := (hH.quotient D)) j.val) ∧
      ∀ j, (Q.flagQuotientOfNormMeasurability G j).slope =
        (V.flagQuotientOfNormMeasurability F (δ j)).slope := by
  let D := F k
  let Q := V.quotientOfNormMeasurability D
  let m := n - k.val
  let idx : Fin (m + 1) → Fin (n + 1) := fun j ↦ ⟨j.val + k.val, by omega⟩
  let δ : Fin m → Fin n := fun j ↦ ⟨j.val + k.val, by omega⟩
  let G : Fin (m + 1) → Submodule K (V ⧸ D) := fun j ↦ (F (idx j)).map D.mkQ
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
    have he := congrArg (fun U : Submodule K (V ⧸ D) ↦ U.comap D.mkQ) heq
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
      (Q.flagQuotientOfNormMeasurability G j).IsMeanSlopeSemistable ∧
      (Q.flagQuotientOfNormMeasurability G j).slope =
        (V.flagQuotientOfNormMeasurability F (δ j)).slope := by
    intro j
    have hDA : D ≤ F (δ j).castSucc := hF.monotone (show k ≤ (δ j).castSucc by
      change k.val ≤ j.val + k.val
      omega)
    have hAB : F (δ j).castSucc ≤ F (δ j).succ :=
      hF.monotone (Fin.castSucc_le_succ (δ j))
    have hs := V.nested_quotient_map_semistable_slope
      D (F (δ j).castSucc) (F (δ j).succ) hDA hAB (hsemi := (hsemi (δ j)))
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
    have he := congrArg (fun p : Submodule K (V ⧸ D) × Submodule K (V ⧸ D) ↦
      let R := quotientOfNormMeasurability (Q.restrictOfNormMeasurability p.1)
        (p.2.comap p.1.subtype)
      R.IsMeanSlopeSemistable ∧ R.slope =
        (V.flagQuotientOfNormMeasurability F (δ j)).slope) hp
    exact Eq.mp he hs
  have hb : StrictAnti (fun j ↦ (Q.flagQuotientOfNormMeasurability G j).slope) := by
    intro a b hab
    change (Q.flagQuotientOfNormMeasurability G b).slope <
      (Q.flagQuotientOfNormMeasurability G a).slope
    rw [(hf a).2, (hf b).2]
    apply hβ
    change a.val + k.val < b.val + k.val
    exact Nat.add_lt_add_right hab k.val
  have he := Q.semistableFlag_eq_hermitianHNTerm (hH := (hH.quotient D))
    G hG hz ht (hsemi := (fun j ↦ (hf j).1)) hb
  exact ⟨he.1, he.2, fun j ↦ (hf j).2⟩

/-- The canonical HN flag quotients are actual nonzero semistable bundles. -/
theorem isMeanSlopeSemistable_hermitianHNFlag_quotient
    [hH : V.toNormFamily.IsHermitian] (i : Fin (V.hermitianHNLength)) :
    (V.flagQuotientOfNormMeasurability
      (V.hermitianHNFlag) i).IsMeanSlopeSemistable := by
  let U := V.hermitianHNTerm (i.val + 1)
  let W := V.hermitianHNTerm i.val
  have hk : (W.mkQ.comp U.subtype).ker = W.comap U.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have he := congrArg (fun I : Submodule K U ↦
    IsMeanSlopeSemistable
      ((V.restrictOfNormMeasurability U).quotientOfNormMeasurability I)) hk
  exact Eq.mp he (V.hermitianHNSubquotient_semistable_slope i).1

/-- The canonical HN flag quotient means are strictly decreasing. -/
theorem hermitianHNFlag_quotient_slope_strictAnti
    [hH : V.toNormFamily.IsHermitian] :
    StrictAnti (fun i ↦
      (V.flagQuotientOfNormMeasurability (V.hermitianHNFlag) i).slope) := by
  intro i j hij
  change (V.flagQuotientOfNormMeasurability (V.hermitianHNFlag) j).slope <
    (V.flagQuotientOfNormMeasurability (V.hermitianHNFlag) i).slope
  rw [V.slope_hermitianHNFlag_quotient_eq_factor i,
    V.slope_hermitianHNFlag_quotient_eq_factor j]
  exact V.hermitianHNFactor_slope_strictAnti hij

/-- Restricting to the k-th actual HN term gives precisely its initial
k-term HN flag on the canonical rational subspaces. -/
theorem hermitianHN_restrict_initial_flag
    [hH : V.toNormFamily.IsHermitian] (k : Fin (V.hermitianHNLength + 1)) :
    let C := V.hermitianHNTerm k.val
    let Q := V.restrictOfNormMeasurability C
    k.val = Q.hermitianHNLength (hV := (hH.restrict C)) ∧
      ∀ j : Fin (k.val + 1),
        (V.hermitianHNTerm j.val).comap C.subtype =
          Q.hermitianHNTerm (hV := (hH.restrict C)) j.val := by
  have he := V.semistableFlag_initial_eq_hermitianHNTerm
    (V.hermitianHNFlag) (V.hermitianHNFlag_strictMono)
    (V.hermitianHNFlag_zero)
    (hsemi := (V.isMeanSlopeSemistable_hermitianHNFlag_quotient))
    (V.hermitianHNFlag_quotient_slope_strictAnti) k
  exact ⟨he.1, he.2.1⟩

/-- Quotienting by the k-th actual HN term gives precisely the actual
remaining HN flag, with its canonical quotient images. -/
theorem hermitianHN_quotient_tail_flag
    [hH : V.toNormFamily.IsHermitian] (k : Fin (V.hermitianHNLength + 1)) :
    let D := V.hermitianHNTerm k.val
    let Q := V.quotientOfNormMeasurability D
    V.hermitianHNLength - k.val = Q.hermitianHNLength (hV := (hH.quotient D)) ∧
      ∀ j : Fin (V.hermitianHNLength - k.val + 1),
        (V.hermitianHNTerm (j.val + k.val)).map D.mkQ =
          Q.hermitianHNTerm (hV := (hH.quotient D)) j.val := by
  have he := V.semistableFlag_tail_eq_hermitianHNTerm
    (V.hermitianHNFlag) (V.hermitianHNFlag_strictMono)
    (V.hermitianHNFlag_last)
    (hsemi := (V.isMeanSlopeSemistable_hermitianHNFlag_quotient))
    (V.hermitianHNFlag_quotient_slope_strictAnti) k
  exact ⟨he.1, he.2.1⟩

/-- Every factor mean of an actual HN initial restriction is the
corresponding original factor mean, under the produced length equality. -/
theorem slope_hermitianHNFactor_restrict_term_eq
    [hH : V.toNormFamily.IsHermitian] (k : Fin (V.hermitianHNLength + 1))
    (j : Fin k.val) :
    let C := V.hermitianHNTerm k.val
    let Q := V.restrictOfNormMeasurability C
    let hlen := (V.hermitianHN_restrict_initial_flag k).1
    (Q.hermitianHNFactor (hV := (hH.restrict C)) (Fin.cast hlen j)).slope =
      (V.hermitianHNFactor ⟨j.val, by omega⟩).slope := by
  let C := V.hermitianHNTerm k.val
  let Q := V.restrictOfNormMeasurability C
  let hlen := (V.hermitianHN_restrict_initial_flag k).1
  let jQ := Fin.cast hlen j
  let i : Fin (V.hermitianHNLength) := ⟨j.val, by omega⟩
  let G : Fin (k.val + 1) → Submodule K C := fun l ↦
    (V.hermitianHNTerm l.val).comap C.subtype
  have ht := (V.hermitianHN_restrict_initial_flag k).2
  have hp : (G j.succ, G j.castSucc) =
      ((Q.hermitianHNFlag (hV := (hH.restrict C))) jQ.succ,
        (Q.hermitianHNFlag (hV := (hH.restrict C))) jQ.castSucc) :=
    Prod.ext (ht j.succ) (ht j.castSucc)
  have hc := congrArg (fun p : Submodule K C × Submodule K C ↦
    (quotientOfNormMeasurability (Q.restrictOfNormMeasurability p.1)
      (p.2.comap p.1.subtype)).slope) hp
  have he := V.semistableFlag_initial_eq_hermitianHNTerm
    (V.hermitianHNFlag) (V.hermitianHNFlag_strictMono)
    (V.hermitianHNFlag_zero)
    (hsemi := (V.isMeanSlopeSemistable_hermitianHNFlag_quotient))
    (V.hermitianHNFlag_quotient_slope_strictAnti) k
  exact (Q.slope_hermitianHNFlag_quotient_eq_factor (hH := (hH.restrict C)) jQ).symm.trans
    (hc.symm.trans ((he.2.2 j).trans (V.slope_hermitianHNFlag_quotient_eq_factor i)))

/-- Every factor mean of an actual HN quotient tail is the corresponding
original factor mean, under the produced length equality. -/
theorem slope_hermitianHNFactor_quotient_term_eq
    [hH : V.toNormFamily.IsHermitian] (k : Fin (V.hermitianHNLength + 1))
    (j : Fin (V.hermitianHNLength - k.val)) :
    let D := V.hermitianHNTerm k.val
    let Q := V.quotientOfNormMeasurability D
    let hlen := (V.hermitianHN_quotient_tail_flag k).1
    (Q.hermitianHNFactor (hV := (hH.quotient D)) (Fin.cast hlen j)).slope =
      (V.hermitianHNFactor ⟨j.val + k.val, by omega⟩).slope := by
  let D := V.hermitianHNTerm k.val
  let Q := V.quotientOfNormMeasurability D
  let hlen := (V.hermitianHN_quotient_tail_flag k).1
  let jQ := Fin.cast hlen j
  let i : Fin (V.hermitianHNLength) := ⟨j.val + k.val, by omega⟩
  let G : Fin (V.hermitianHNLength - k.val + 1) → Submodule K (V ⧸ D) :=
    fun l ↦ (V.hermitianHNTerm (l.val + k.val)).map D.mkQ
  have ht := (V.hermitianHN_quotient_tail_flag k).2
  have hp : (G j.succ, G j.castSucc) =
      ((Q.hermitianHNFlag (hV := (hH.quotient D))) jQ.succ,
        (Q.hermitianHNFlag (hV := (hH.quotient D))) jQ.castSucc) :=
    Prod.ext (ht j.succ) (ht j.castSucc)
  have hc := congrArg (fun p : Submodule K (V ⧸ D) × Submodule K (V ⧸ D) ↦
    (quotientOfNormMeasurability (Q.restrictOfNormMeasurability p.1)
      (p.2.comap p.1.subtype)).slope) hp
  have he := V.semistableFlag_tail_eq_hermitianHNTerm
    (V.hermitianHNFlag) (V.hermitianHNFlag_strictMono)
    (V.hermitianHNFlag_last)
    (hsemi := (V.isMeanSlopeSemistable_hermitianHNFlag_quotient))
    (V.hermitianHNFlag_quotient_slope_strictAnti) k
  exact (Q.slope_hermitianHNFlag_quotient_eq_factor (hH := (hH.quotient D)) jQ).symm.trans
    (hc.symm.trans ((he.2.2 j).trans (V.slope_hermitianHNFlag_quotient_eq_factor i)))

/-- The actual remaining quotient above an HN threshold has maximal
slope strictly below that threshold, including the zero quotient. -/
theorem maximalSlope_quotient_hermitianHNFiltration_lt
    [hH : V.toNormFamily.IsHermitian] (t : ℝ) :
    (V.quotientOfNormMeasurability (V.hermitianHNFiltration t)).maximalSlope <
      (t : EReal) := by
  let c := V.hermitianHNCut t
  have hcl := V.hermitianHNCut_le_length t
  by_cases hc : c = V.hermitianHNLength
  · have hU : V.hermitianHNFiltration t = ⊤ :=
      (congrArg (V.hermitianHNTerm) hc).trans
        (V.hermitianHNTerm_length_eq_top)
    have hr : Module.finrank K (V ⧸ V.hermitianHNFiltration t) = 0 := by
      have h := (V.hermitianHNFiltration t).finrank_quotient_add_finrank
      have hF := congrArg (fun U : Submodule K V ↦ Module.finrank K U) hU
      rw [finrank_top] at hF
      omega
    rw [maximalSlope_eq_bot_of_finrank_eq_zero _ hr]
    exact EReal.bot_lt_coe t
  · let i : Fin (V.hermitianHNLength) := ⟨c, by dsimp [c] at *; omega⟩
    have ht : (V.hermitianHNFactor i).slope < t := by
      apply lt_of_not_ge
      intro hi
      have hb := (V.le_hermitianHNFactor_slope_iff_lt_cut t i).mp hi
      exact (Nat.lt_irrefl c) hb
    have hm := V.slope_hermitianHNFactor_eq_maximalSlope_quotient i
    exact hm.symm.trans_lt (EReal.coe_lt_coe_iff.mpr ht)

/-- Actual inclusion tails have nonpositive height, so the accepted chain
inequality bounds a restricted endpoint by the actual means of semistable factors. -/
theorem le_minimalSlope_restrict_last_of_semistableFlag
    [hH : V.toNormFamily.IsHermitian] {n : ℕ}
    (F : Fin (n + 1) → Submodule K V) (hF : Monotone F) (hzero : F 0 = ⊥)
    [hsemi : ∀ i, (V.flagQuotientOfNormMeasurability F i).IsMeanSlopeSemistable]
    (t : ℝ) (hμ : ∀ i, t ≤ (V.flagQuotientOfNormMeasurability F i).slope) :
    (t : EReal) ≤ (V.restrictOfNormMeasurability (F (Fin.last n))).minimalSlope := by
  let A : Fin (n + 1) → Type _ := fun i ↦ F i
  let W : ∀ i, AdelicVectorBundle S := fun i ↦ V.restrictOfNormMeasurability (F i)
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
    (congrArg (fun U : Submodule K V ↦ Module.finrank K U) hzero).trans (finrank_bot K V)
  have hc := minimalSlope_linearChain_lowerBound W α h0
  refine (le_iInf fun i ↦ ?_).trans hc
  let j := i.val
  let R := (W j.succ).quotientOfNormMeasurability (α j).range
  have hrange : (α j).range = (F j.castSucc).comap (F j.succ).subtype :=
    Submodule.range_inclusion _ _ (hF (Fin.castSucc_le_succ j))
  have hp := congrArg (fun I : Submodule K (F j.succ) ↦
    IsMeanSlopeSemistable ((W j.succ).quotientOfNormMeasurability I)) hrange
  have hs : R.IsMeanSlopeSemistable := Eq.mpr hp (hsemi j)
  have hm := (R.isMeanSlopeSemistable_iff_minimalSlope_eq_slope_of_isHermitian
    (hV := ((hH.restrict (F j.succ)).quotient (α j).range)) hs.1).mp hs
  have he := congrArg (fun I : Submodule K (F j.succ) ↦
    ((W j.succ).quotientOfNormMeasurability I).slope) hrange
  have ht : (t : EReal) ≤ R.minimalSlope := by
    rw [hm]
    exact EReal.coe_le_coe_iff.mpr ((hμ j).trans_eq he.symm)
  calc
    (t : EReal) ≤ R.minimalSlope := ht
    _ = R.minimalSlope - 0 := by simp
    _ ≤ R.minimalSlope -
        (W j.succ).mapHeight (W (Fin.last n)) (linearChainTailMap A α j.succ) :=
      EReal.sub_le_sub le_rfl (hheight j.succ)

/-- The actual restricted subspace retained at an HN threshold has minimal
slope at least that threshold; the zero retained subspace has minimal slope top. -/
theorem le_minimalSlope_restrict_hermitianHNFiltration
    [hH : V.toNormFamily.IsHermitian] (t : ℝ) :
    (t : EReal) ≤
      (V.restrictOfNormMeasurability (V.hermitianHNFiltration t)).minimalSlope := by
  let c := V.hermitianHNCut t
  have hcl := V.hermitianHNCut_le_length t
  by_cases hc : c = 0
  · have hU : V.hermitianHNFiltration t = ⊥ :=
      (congrArg (V.hermitianHNTerm) hc).trans (V.hermitianHNTerm_zero)
    have hr : Module.finrank K (V.hermitianHNFiltration t) = 0 :=
      (congrArg (fun U : Submodule K V ↦ Module.finrank K U) hU).trans (finrank_bot K V)
    rw [minimalSlope_eq_top_of_finrank_eq_zero _ hr]
    exact le_top
  · let F : Fin (c + 1) → Submodule K V := fun j ↦ V.hermitianHNTerm j.val
    let δ : Fin c → Fin (V.hermitianHNLength) := fun j ↦ ⟨j.val, by omega⟩
    have hF : Monotone F := fun _ _ h ↦ V.hermitianHNTerm_monotone h
    have hz : F 0 = ⊥ := V.hermitianHNTerm_zero
    have hs : ∀ j, (V.flagQuotientOfNormMeasurability F j).IsMeanSlopeSemistable := by
      intro j
      exact V.isMeanSlopeSemistable_hermitianHNFlag_quotient (δ j)
    have hμ : ∀ j, t ≤ (V.flagQuotientOfNormMeasurability F j).slope := by
      intro j
      change t ≤ (V.flagQuotientOfNormMeasurability (V.hermitianHNFlag) (δ j)).slope
      rw [V.slope_hermitianHNFlag_quotient_eq_factor (δ j)]
      exact (V.le_hermitianHNFactor_slope_iff_lt_cut t (δ j)).mpr j.isLt
    exact V.le_minimalSlope_restrict_last_of_semistableFlag F hF hz (hsemi := hs) t hμ

end AdelicVectorBundle

end

end ArakelovGeometry
