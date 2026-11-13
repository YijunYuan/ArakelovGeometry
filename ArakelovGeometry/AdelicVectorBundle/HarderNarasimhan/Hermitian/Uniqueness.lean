/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.Basic
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Basic

import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.SemistableFlagDegree
import ArakelovGeometry.AdelicVectorBundle.Slope.Quotient
import ArakelovGeometry.AdelicVectorBundle.Subquotient.Quotient.Restriction
import ArakelovGeometry.LinearAlgebra.FiniteFiltration
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Uniqueness of the actual Hermitian Harder--Narasimhan filtration

Actual completed quotient and restriction isometries transport semistable
factors through quotient tails. The first term is characterized using the
actual degree bound for subspaces of a semistable flag.
-/

@[expose] public section

open scoped BigOperators TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace AdelicVectorBundle

variable [S.IsProper] (V : AdelicVectorBundle.{w} S)
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]

/-- The actual quotient by zero has the same mean, through the canonical
completed quotient isometry. -/
theorem slope_quotient_bot :
    (V.quotientOfMeasurableBase ⊥).slope = V.slope := by
  let e : V ≃ₗ[K] V ⧸ (⊥ : Submodule K V) :=
    LinearEquiv.ofBijective (⊥ : Submodule K V).mkQ
      ⟨LinearMap.ker_eq_bot.mp (Submodule.ker_mkQ ⊥), Submodule.mkQ_surjective ⊥⟩
  symm
  apply slope_eq_of_completed_isometry _ _ e
  intro ω z
  exact V.toNormFamily.quotient_bot_norm_mk ω z

/-- The first actual flag quotient has precisely the mean of the first
restricted subspace when the preceding flag term is zero. -/
theorem slope_first_flagQuotient_eq_restrict {n : ℕ}
    (F : Fin (n + 2) → Submodule K V) (hzero : F 0 = ⊥) :
    (V.flagQuotientOfMeasurableBase F (0 : Fin (n + 1))).slope =
      (V.restrictOfMeasurableBase (F (0 : Fin (n + 1)).succ)).slope := by
  let W := F (0 : Fin (n + 1)).succ
  have hz : (F (0 : Fin (n + 1)).castSucc).comap W.subtype = ⊥ := by
    change (F 0).comap W.subtype = ⊥
    simp only [hzero, Submodule.comap_bot, Submodule.ker_subtype]
  have he := congrArg (fun I : Submodule K W ↦
    ((V.restrictOfMeasurableBase W).quotientOfMeasurableBase I).slope) hz
  exact he.trans ((V.restrictOfMeasurableBase W).slope_quotient_bot)

/-- The first mean of a complete actual semistable flag bounds the actual
ambient maximal slope when all later factor means are no larger. -/
theorem maximalSlope_le_first_semistableFlag
    [hH : V.toNormFamily.IsHermitian] {n : ℕ}
    (F : Fin (n + 2) → Submodule K V) (hF : Monotone F) (hzero : F 0 = ⊥)
    (htop : F (Fin.last (n + 1)) = ⊤)
    [hsemi : ∀ i, (V.flagQuotientOfMeasurableBase F i).IsMeanSlopeSemistable]
    (hβ : Antitone (fun i ↦ (V.flagQuotientOfMeasurableBase F i).slope)) :
    V.maximalSlope ≤
      ((V.flagQuotientOfMeasurableBase F (0 : Fin (n + 1))).slope : EReal) := by
  apply V.maximalSlope_le
  intro U hU
  let k : Fin (n + 1) → ℕ := fun i ↦
    Module.finrank K (U ⊓ F i.succ : Submodule K V) -
      Module.finrank K (U ⊓ F i.castSucc : Submodule K V)
  let β : Fin (n + 1) → ℝ := fun i ↦ (V.flagQuotientOfMeasurableBase F i).slope
  have hk : (∑ i, (k i : ℝ)) = (Module.finrank K U : ℝ) := by
    exact_mod_cast sum_intersection_rank_increment_eq F hF hzero htop U
  have hd := V.degree_restrict_le_sum_intersection_rank_mul_slope_of_semistableFlag
    F hF hzero htop U
  change (V.restrictOfMeasurableBase U).degree ≤ ∑ i, (k i : ℝ) * β i at hd
  have hu : (∑ i, (k i : ℝ) * β i) ≤ (Module.finrank K U : ℝ) * β 0 := by
    calc
      _ ≤ ∑ i, (k i : ℝ) * β 0 := Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_left (hβ (Fin.zero_le i)) (Nat.cast_nonneg _)
      _ = (Module.finrank K U : ℝ) * β 0 := by rw [← Finset.sum_mul, hk]
  have hp : 0 < (Module.finrank K U : ℝ) := Nat.cast_pos.mpr hU
  rw [degree_eq_rank_mul_slope] at hd
  apply EReal.coe_le_coe_iff.mpr
  change (V.restrictOfMeasurableBase U).slope ≤ β 0
  nlinarith [hd.trans hu]

/-- The first mean of a complete actual semistable flag is the ambient
maximal slope when its actual factor means are nonincreasing. -/
theorem maximalSlope_eq_first_semistableFlag
    [hH : V.toNormFamily.IsHermitian] {n : ℕ}
    (F : Fin (n + 2) → Submodule K V) (hF : Monotone F) (hzero : F 0 = ⊥)
    (htop : F (Fin.last (n + 1)) = ⊤)
    [hsemi : ∀ i, (V.flagQuotientOfMeasurableBase F i).IsMeanSlopeSemistable]
    (hβ : Antitone (fun i ↦ (V.flagQuotientOfMeasurableBase F i).slope)) :
    V.maximalSlope =
      ((V.flagQuotientOfMeasurableBase F (0 : Fin (n + 1))).slope : EReal) := by
  apply le_antisymm (V.maximalSlope_le_first_semistableFlag F hF hzero htop hβ)
  let W := F (0 : Fin (n + 1)).succ
  let I := (F (0 : Fin (n + 1)).castSucc).comap W.subtype
  have hq := (hsemi (0 : Fin (n + 1))).1
  change 0 < Module.finrank K (W ⧸ I) at hq
  have hr := I.finrank_quotient_add_finrank
  have hp : 0 < Module.finrank K W := by omega
  have hm := V.slope_first_flagQuotient_eq_restrict F hzero
  exact (congrArg (fun x : ℝ ↦ (x : EReal)) hm).trans_le
    (V.slope_restrict_le_maximalSlope W hp)

/-- The first subspace of any complete actual semistable flag with
strictly decreasing actual means is the produced largest destabilizer. -/
theorem first_semistableFlag_eq_destabilizingSubspace
    [hH : V.toNormFamily.IsHermitian] (hr : 0 < Module.finrank K V) {n : ℕ}
    (F : Fin (n + 2) → Submodule K V) (hF : Monotone F) (hzero : F 0 = ⊥)
    (htop : F (Fin.last (n + 1)) = ⊤)
    [hsemi : ∀ i, (V.flagQuotientOfMeasurableBase F i).IsMeanSlopeSemistable]
    (hβ : StrictAnti (fun i ↦ (V.flagQuotientOfMeasurableBase F i).slope)) :
    F (0 : Fin (n + 1)).succ = V.destabilizingSubspace hr := by
  let D := V.destabilizingSubspace hr
  let W := F (0 : Fin (n + 1)).succ
  let β : Fin (n + 1) → ℝ := fun i ↦ (V.flagQuotientOfMeasurableBase F i).slope
  have hmax := V.maximalSlope_eq_first_semistableFlag F hF hzero htop hβ.antitone
  let I := (F (0 : Fin (n + 1)).castSucc).comap W.subtype
  have hq := (hsemi (0 : Fin (n + 1))).1
  change 0 < Module.finrank K (W ⧸ I) at hq
  have hIr := I.finrank_quotient_add_finrank
  have hWpos : 0 < Module.finrank K W := by omega
  have hWmean := V.slope_first_flagQuotient_eq_restrict F hzero
  have hWD : W ≤ D :=
    V.le_destabilizingSubspace_of_slope_eq_maximalSlope hr W hWpos
      ((congrArg (fun x : ℝ ↦ (x : EReal)) hWmean.symm).trans hmax.symm)
  let k : Fin (n + 1) → ℕ := fun i ↦
    Module.finrank K (D ⊓ F i.succ : Submodule K V) -
      Module.finrank K (D ⊓ F i.castSucc : Submodule K V)
  have hkN : (∑ i, k i) = Module.finrank K D :=
    sum_intersection_rank_increment_eq F hF hzero htop D
  have hkR : (∑ i, (k i : ℝ)) = (Module.finrank K D : ℝ) := by exact_mod_cast hkN
  have hDmean : (V.restrictOfMeasurableBase D).slope = β 0 :=
    EReal.coe_injective ((V.slope_destabilizingSubspace_eq_maximalSlope hr).trans hmax)
  have hd := V.degree_restrict_le_sum_intersection_rank_mul_slope_of_semistableFlag
    F hF hzero htop D
  change (V.restrictOfMeasurableBase D).degree ≤ ∑ i, (k i : ℝ) * β i at hd
  rw [degree_eq_rank_mul_slope, hDmean] at hd
  have hp : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))),
      (k i : ℝ) * β i ≤ (k i : ℝ) * β 0 :=
    fun i _ ↦ mul_le_mul_of_nonneg_left (hβ.antitone (Fin.zero_le i)) (Nat.cast_nonneg _)
  have hu : (∑ i, (k i : ℝ) * β 0) = (Module.finrank K D : ℝ) * β 0 := by
    rw [← Finset.sum_mul, hkR]
  have hs : (∑ i, (k i : ℝ) * β i) = ∑ i, (k i : ℝ) * β 0 := by
    apply le_antisymm (Finset.sum_le_sum hp)
    exact hu.trans_le hd
  have he := (Finset.sum_eq_sum_iff_of_le hp).mp hs
  have hz : ∀ i : Fin (n + 1), i ≠ 0 → k i = 0 := by
    intro i hi
    by_contra hk
    have hi0 : (0 : Fin (n + 1)) < i := lt_of_le_of_ne (Fin.zero_le i) hi.symm
    have hne : (k i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    have hsame : β i = β 0 := mul_left_cancel₀ hne (he i (Finset.mem_univ i))
    exact (ne_of_lt (hβ hi0)) hsame
  have hsN : (∑ i, k i) = k 0 := by
    apply Finset.sum_eq_single 0
    · intro i _ hi
      exact hz i hi
    · intro h
      exact False.elim (h (Finset.mem_univ 0))
  have hk0 : k 0 = Module.finrank K D := hsN.symm.trans hkN
  change Module.finrank K (D ⊓ W : Submodule K V) -
    Module.finrank K (D ⊓ F 0 : Submodule K V) = Module.finrank K D at hk0
  have hzeroD : Module.finrank K (D ⊓ F 0 : Submodule K V) = 0 :=
    (congrArg (fun T : Submodule K V ↦ Module.finrank K (D ⊓ T : Submodule K V)) hzero).trans
      ((congrArg (fun T : Submodule K V ↦ Module.finrank K T)
        (show D ⊓ (⊥ : Submodule K V) = ⊥ from inf_bot_eq D)).trans (finrank_bot K V))
  rw [hzeroD, Nat.sub_zero] at hk0
  have hDW : D ⊓ W = D := Submodule.eq_of_le_of_finrank_eq inf_le_left hk0
  apply le_antisymm hWD
  exact hDW ▸ (show D ⊓ W ≤ W from inf_le_right)

omit [FiniteDimensional K E] in
/-- The canonical map from a restricted subspace, modulo a containing
lower subspace, has exactly the expected kernel after an earlier quotient. -/
theorem nested_quotient_restrict_map_ker (D A B : Submodule K E) (hDA : D ≤ A) :
    (((A.map D.mkQ).comap (D.mkQ.comp B.subtype).range.subtype).mkQ.comp
      (D.mkQ.comp B.subtype).rangeRestrict).ker = A.comap B.subtype := by
  ext x
  change ((A.map D.mkQ).comap (D.mkQ.comp B.subtype).range.subtype).mkQ
    ((D.mkQ.comp B.subtype).rangeRestrict x) = 0 ↔ (x : E) ∈ A
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  change (x : E) ∈ (A.map D.mkQ).comap D.mkQ ↔ (x : E) ∈ A
  rw [Submodule.comap_map_eq_self (by simpa only [Submodule.ker_mkQ] using hDA)]

omit [S.IsProper] in
omit hS hN in
/-- Restriction after an ambient quotient and then a further quotient is
the actual pushforward of the original restriction along the composite map,
on every completed vector. -/
theorem nested_quotient_restrict_norm_eq (ξ : NormFamily S E)
    (D B : Submodule K E) (hDB : D ≤ B)
    (T : Submodule K (D.mkQ.comp B.subtype).range) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      (B ⧸ (T.mkQ.comp (D.mkQ.comp B.subtype).rangeRestrict).ker)) :
    let π := T.mkQ.comp (D.mkQ.comp B.subtype).rangeRestrict
    let hπ := T.mkQ_surjective.comp (D.mkQ.comp B.subtype).surjective_rangeRestrict
    (((ξ.quotient D).restrict (D.mkQ.comp B.subtype).range).quotient T).norm ω
      ((π.quotKerEquivOfSurjective hπ).toLinearMap.baseChange (S.ϕ ω).Completion z) =
        ((ξ.restrict B).quotient π.ker).norm ω z := by
  let g := D.mkQ.comp B.subtype
  let f := g.rangeRestrict
  let π := T.mkQ.comp f
  have hf := g.surjective_rangeRestrict
  have hπ := T.mkQ_surjective.comp hf
  have hnorm : (ξ.restrict B).pushforward f hf = (ξ.quotient D).restrict g.range := by
    ext ω y
    exact ξ.pushforward_restrict_range_norm_eq D.mkQ D.mkQ_surjective B
      (by simpa only [Submodule.ker_mkQ] using hDB) ω y
  change (((ξ.quotient D).restrict g.range).quotient T).norm ω
    ((π.quotKerEquivOfSurjective hπ).toLinearMap.baseChange (S.ϕ ω).Completion z) =
      ((ξ.restrict B).quotient π.ker).norm ω z
  rw [← hnorm]
  change (((ξ.restrict B).pushforward f hf).pushforward T.mkQ T.mkQ_surjective).norm ω
    ((π.quotKerEquivOfSurjective hπ).toLinearMap.baseChange (S.ϕ ω).Completion z) = _
  rw [(ξ.restrict B).pushforward_comp_norm]
  exact (ξ.restrict B).quotient_ker_equiv_norm_eq π hπ ω z

/-- Passing a containing lower subspace through an earlier ambient quotient
preserves the actual restricted factor's semistability and actual mean. -/
theorem nested_quotient_restrict_semistable_slope (D A B : Submodule K V)
    (hDA : D ≤ A) (hAB : A ≤ B)
    [hsemi : ((V.restrictOfMeasurableBase B).quotientOfMeasurableBase
      (A.comap B.subtype)).IsMeanSlopeSemistable] :
    let g := D.mkQ.comp B.subtype
    let T := (A.map D.mkQ).comap g.range.subtype
    let R := quotientOfMeasurableBase
      ((V.quotientOfMeasurableBase D).restrictOfMeasurableBase g.range) T
    R.IsMeanSlopeSemistable ∧ R.slope =
      ((V.restrictOfMeasurableBase B).quotientOfMeasurableBase
        (A.comap B.subtype)).slope := by
  let g := D.mkQ.comp B.subtype
  let T := (A.map D.mkQ).comap g.range.subtype
  let π := T.mkQ.comp g.rangeRestrict
  let hπ := T.mkQ_surjective.comp g.surjective_rangeRestrict
  let Q := (V.restrictOfMeasurableBase B).quotientOfMeasurableBase π.ker
  let R := quotientOfMeasurableBase
    ((V.quotientOfMeasurableBase D).restrictOfMeasurableBase g.range) T
  have hk : π.ker = A.comap B.subtype := nested_quotient_restrict_map_ker D A B hDA
  have hp := congrArg (fun I : Submodule K B ↦
    IsMeanSlopeSemistable
      ((V.restrictOfMeasurableBase B).quotientOfMeasurableBase I)) hk
  have hQ : Q.IsMeanSlopeSemistable := Eq.mpr hp hsemi
  have hn : ∀ ω z, R.toNormFamily.norm ω
      ((π.quotKerEquivOfSurjective hπ).toLinearMap.baseChange (S.ϕ ω).Completion z) =
        Q.toNormFamily.norm ω z := by
    intro ω z
    exact nested_quotient_restrict_norm_eq V.toNormFamily D B (hDA.trans hAB) T ω z
  have hs := Q.slope_eq_of_completed_isometry R (π.quotKerEquivOfSurjective hπ) hn
  have hm := Q.maximalSlope_eq_of_completed_isometry R (π.quotKerEquivOfSurjective hπ) hn
  have hr : 0 < Module.finrank K (g.range ⧸ T) := by
    rw [← (π.quotKerEquivOfSurjective hπ).finrank_eq]
    exact hQ.1
  have hQmax := (Q.isMeanSlopeSemistable_iff_maximalSlope_eq_slope hQ.1).mp hQ
  have hf := congrArg (fun I : Submodule K B ↦
    ((V.restrictOfMeasurableBase B).quotientOfMeasurableBase I).slope) hk
  change R.IsMeanSlopeSemistable ∧ R.slope = _
  refine ⟨(R.isMeanSlopeSemistable_iff_maximalSlope_eq_slope hr).mpr ?_, hs.symm.trans hf⟩
  exact (hm.symm.trans hQmax).trans (congrArg (fun x : ℝ ↦ (x : EReal)) hs)

/-- Actual nested flag factors may be expressed on the canonical quotient image. -/
theorem nested_quotient_map_semistable_slope
    (D A B : Submodule K V) (hDA : D ≤ A) (hAB : A ≤ B)
    [hsemi : ((V.restrictOfMeasurableBase B).quotientOfMeasurableBase
      (A.comap B.subtype)).IsMeanSlopeSemistable] :
    let Q := V.quotientOfMeasurableBase D
    let R := quotientOfMeasurableBase
      (Q.restrictOfMeasurableBase (B.map D.mkQ))
      ((A.map D.mkQ).comap (B.map D.mkQ).subtype)
    R.IsMeanSlopeSemistable ∧ R.slope =
      ((V.restrictOfMeasurableBase B).quotientOfMeasurableBase
        (A.comap B.subtype)).slope := by
  have hs := V.nested_quotient_restrict_semistable_slope D A B hDA hAB
  have hr : (D.mkQ.comp B.subtype).range = B.map D.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  let Q := V.quotientOfMeasurableBase D
  have he := congrArg (fun U : Submodule K (V ⧸ D) ↦
    let R := quotientOfMeasurableBase (Q.restrictOfMeasurableBase U)
      ((A.map D.mkQ).comap U.subtype)
    R.IsMeanSlopeSemistable ∧ R.slope =
      ((V.restrictOfMeasurableBase B).quotientOfMeasurableBase
        (A.comap B.subtype)).slope) hr
  exact Eq.mp he hs

/-- Every successor in a complete actual semistable flag with strictly
decreasing means is the canonical HN step of its predecessor. -/
theorem semistableFlag_step_eq_hermitianHNStep
    [hH : V.toNormFamily.IsHermitian] {n : ℕ}
    (F : Fin (n + 1) → Submodule K V) (hF : StrictMono F)
    (htop : F (Fin.last n) = ⊤)
    [hsemi : ∀ j, (V.flagQuotientOfMeasurableBase F j).IsMeanSlopeSemistable]
    (hβ : StrictAnti (fun j ↦ (V.flagQuotientOfMeasurableBase F j).slope))
    (i : Fin n) :
    F i.succ = V.hermitianHNStep (F i.castSucc) := by
  let D := F i.castSucc
  have hD : D ≠ ⊤ := by
    have hi : i.castSucc < Fin.last n := by change i.val < n; exact i.isLt
    have hl := hF hi
    rw [htop] at hl
    exact ne_of_lt hl
  let Q := V.quotientOfMeasurableBase D
  let m := n - i.val - 1
  have hsize : n = m + i.val + 1 := by dsimp [m]; omega
  let idx : Fin (m + 2) → Fin (n + 1) :=
    fun j ↦ ⟨j.val + i.val, by omega⟩
  let δ : Fin (m + 1) → Fin n := fun j ↦ ⟨j.val + i.val, by omega⟩
  let G : Fin (m + 2) → Submodule K (V ⧸ D) := fun j ↦ (F (idx j)).map D.mkQ
  have hG : Monotone G := by
    intro a b hab
    apply Submodule.map_mono
    apply hF.monotone
    change a.val + i.val ≤ b.val + i.val
    exact Nat.add_le_add_right hab i.val
  have hz : G 0 = ⊥ := by
    have hi : idx 0 = i.castSucc := Fin.ext (by dsimp [idx]; omega)
    change (F (idx 0)).map D.mkQ = ⊥
    rw [hi]
    exact Submodule.mkQ_map_self D
  have ht : G (Fin.last (m + 1)) = ⊤ := by
    have hi : idx (Fin.last (m + 1)) = Fin.last n := Fin.ext (by dsimp [idx]; omega)
    change (F (idx (Fin.last (m + 1)))).map D.mkQ = ⊤
    rw [hi, htop, Submodule.map_top, LinearMap.range_eq_top.mpr D.mkQ_surjective]
  have hf : ∀ j : Fin (m + 1),
      (Q.flagQuotientOfMeasurableBase G j).IsMeanSlopeSemistable ∧
      (Q.flagQuotientOfMeasurableBase G j).slope =
        (V.flagQuotientOfMeasurableBase F (δ j)).slope := by
    intro j
    have hDA : D ≤ F (δ j).castSucc := by
      apply hF.monotone
      change i.val ≤ j.val + i.val
      omega
    have hAB : F (δ j).castSucc ≤ F (δ j).succ :=
      hF.monotone (Fin.castSucc_le_succ (δ j))
    have hs := V.nested_quotient_map_semistable_slope
      D (F (δ j).castSucc) (F (δ j).succ) hDA hAB (hsemi := (hsemi (δ j)))
    have hu : (F (δ j).succ).map D.mkQ = G j.succ := by
      apply congrArg (fun k : Fin (n + 1) ↦ (F k).map D.mkQ)
      apply Fin.ext
      dsimp [δ, idx]
      omega
    have hl : (F (δ j).castSucc).map D.mkQ = G j.castSucc := by
      apply congrArg (fun k : Fin (n + 1) ↦ (F k).map D.mkQ)
      apply Fin.ext
      rfl
    have hp : ((F (δ j).succ).map D.mkQ, (F (δ j).castSucc).map D.mkQ) =
        (G j.succ, G j.castSucc) := Prod.ext hu hl
    have he := congrArg (fun p : Submodule K (V ⧸ D) × Submodule K (V ⧸ D) ↦
      let R := quotientOfMeasurableBase (Q.restrictOfMeasurableBase p.1)
        (p.2.comap p.1.subtype)
      R.IsMeanSlopeSemistable ∧ R.slope =
        (V.flagQuotientOfMeasurableBase F (δ j)).slope) hp
    exact Eq.mp he hs
  have hb : StrictAnti (fun j ↦ (Q.flagQuotientOfMeasurableBase G j).slope) := by
    intro a b hab
    change (Q.flagQuotientOfMeasurableBase G b).slope <
      (Q.flagQuotientOfMeasurableBase G a).slope
    rw [(hf a).2, (hf b).2]
    apply hβ
    change a.val + i.val < b.val + i.val
    exact Nat.add_lt_add_right hab i.val
  have hr := finrank_quotient_pos_of_ne_top D hD
  have he := Q.first_semistableFlag_eq_destabilizingSubspace
    (hH := (hH.quotient D)) hr G hG hz ht (hsemi := (fun j ↦ (hf j).1)) hb
  have hi : idx (0 : Fin (m + 1)).succ = i.succ := Fin.ext (by simp [idx, Nat.add_comm])
  have hu : (F i.succ).map D.mkQ = Q.destabilizingSubspace (hV := (hH.quotient D)) hr := by
    have hg : G (0 : Fin (m + 1)).succ = (F i.succ).map D.mkQ :=
      congrArg (fun k : Fin (n + 1) ↦ (F k).map D.mkQ) hi
    exact hg.symm.trans he
  have hc := congrArg (fun U : Submodule K (V ⧸ D) ↦ U.comap D.mkQ) hu
  rw [hermitianHNStep, dite_eq_right hD]
  exact (Submodule.comap_map_eq_self
    (show D.mkQ.ker ≤ F i.succ by
      rw [Submodule.ker_mkQ]
      exact hF.monotone (Fin.castSucc_le_succ i))).symm.trans hc

/-- A complete actual semistable flag with strictly decreasing means has
the canonical HN length and every canonical rational subspace, including rank zero. -/
theorem semistableFlag_eq_hermitianHNTerm
    [hH : V.toNormFamily.IsHermitian] {n : ℕ}
    (F : Fin (n + 1) → Submodule K V) (hF : StrictMono F) (hzero : F 0 = ⊥)
    (htop : F (Fin.last n) = ⊤)
    [hsemi : ∀ j, (V.flagQuotientOfMeasurableBase F j).IsMeanSlopeSemistable]
    (hβ : StrictAnti (fun j ↦ (V.flagQuotientOfMeasurableBase F j).slope)) :
    n = V.hermitianHNLength ∧
      ∀ j, F j = V.hermitianHNTerm j.val := by
  have hs := V.semistableFlag_step_eq_hermitianHNStep F hF htop hβ
  have hf : ∀ k (hk : k ≤ n),
      F ⟨k, by omega⟩ = V.hermitianHNTerm k := by
    intro k
    induction k with
    | zero =>
      intro hk
      change F 0 = V.hermitianHNTerm 0
      rw [hzero, V.hermitianHNTerm_zero]
    | succ k ih =>
      intro hk
      let j : Fin n := ⟨k, by omega⟩
      calc
        F ⟨k + 1, by omega⟩ = V.hermitianHNStep (F ⟨k, by omega⟩) := hs j
        _ = V.hermitianHNStep (V.hermitianHNTerm k) :=
          congrArg (V.hermitianHNStep) (ih (by omega))
        _ = V.hermitianHNTerm (k + 1) :=
          (V.hermitianHNTerm_succ k).symm
  have ht : V.hermitianHNTerm n = ⊤ := (hf n le_rfl).symm.trans htop
  have hl : V.hermitianHNLength = n := by
    apply Nat.le_antisymm
    · by_contra h
      exact (V.hermitianHNTerm_ne_top_of_lt_length n (Nat.lt_of_not_ge h)) ht
    · by_contra h
      have hh : V.hermitianHNLength < n := Nat.lt_of_not_ge h
      let j : Fin (n + 1) := ⟨V.hermitianHNLength, by omega⟩
      have hj : j < Fin.last n := hh
      have hlt := hF hj
      have he : F j = ⊤ :=
        (hf _ (le_of_lt hh)).trans (V.hermitianHNTerm_length_eq_top)
      rw [he, htop] at hlt
      exact (lt_irrefl (⊤ : Submodule K V)) hlt
  refine ⟨hl.symm, fun j ↦ ?_⟩
  exact hf j.val (by omega)

/-- The actual canonical HN flag quotient has the same mean as its
quotient-image factor, by the checked completed subquotient isometry. -/
theorem slope_hermitianHNFlag_quotient_eq_factor
    [hH : V.toNormFamily.IsHermitian] (i : Fin (V.hermitianHNLength)) :
    (V.flagQuotientOfMeasurableBase (V.hermitianHNFlag) i).slope =
      (V.hermitianHNFactor i).slope := by
  let U := V.hermitianHNTerm (i.val + 1)
  let W := V.hermitianHNTerm i.val
  have hk : (W.mkQ.comp U.subtype).ker = W.comap U.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have he := congrArg (fun I : Submodule K U ↦
    ((V.restrictOfMeasurableBase U).quotientOfMeasurableBase I).slope) hk
  exact he.symm.trans (V.hermitianHNSubquotient_semistable_slope i).2

/-- The actual HN threshold subspace is reconstructed from its retained
rational flag terms and their actual factor means. -/
theorem hermitianHNFiltration_eq_iSup
    [hH : V.toNormFamily.IsHermitian] (t : ℝ) :
    V.hermitianHNFiltration t =
      ⨆ i : Fin (V.hermitianHNLength),
        ⨆ (_ : t ≤ (V.hermitianHNFactor i).slope),
          V.hermitianHNTerm (i.val + 1) := by
  let c := V.hermitianHNCut t
  change V.hermitianHNTerm c = _
  apply le_antisymm
  · by_cases hc : c = 0
    · rw [hc, V.hermitianHNTerm_zero]
      exact bot_le
    · have hcl := V.hermitianHNCut_le_length t
      let i : Fin (V.hermitianHNLength) := ⟨c - 1, by dsimp [c]; omega⟩
      have hi : i.val + 1 = c := by dsimp [i]; omega
      have ht : t ≤ (V.hermitianHNFactor i).slope :=
        (V.le_hermitianHNFactor_slope_iff_lt_cut t i).mpr (by
          change c - 1 < c
          omega)
      rw [← hi]
      exact le_iSup_of_le i (le_iSup_of_le ht le_rfl)
  · apply iSup_le
    intro i
    apply iSup_le
    intro hi
    apply V.hermitianHNTerm_monotone
    exact Nat.succ_le_of_lt ((V.le_hermitianHNFactor_slope_iff_lt_cut t i).mp hi)

/-- Any separated, exhaustive, left-continuous decreasing real filtration
whose actual nonzero graded quotients are semistable of their threshold
mean is the actual Hermitian HN filtration. -/
theorem hermitianHNFiltration_unique
    [hH : V.toNormFamily.IsHermitian]
    (F : ℝ → Submodule K V) (hF : Antitone F)
    (hbot : ∃ t, F t = ⊥) (htop : ∃ t, F t = ⊤)
    (hleft : ∀ t, ∃ ε : ℝ, 0 < ε ∧ ∀ s, t - ε < s → s ≤ t → F s = F t)
    (hgraded : ∀ t,
      let W := ⨆ s : {s : ℝ // t < s}, F s.val
      let Q := quotientOfMeasurableBase (V.restrictOfMeasurableBase (F t))
        (W.comap (F t).subtype)
      Module.finrank K ((F t) ⧸ W.comap (F t).subtype) = 0 ∨
        Q.IsMeanSlopeSemistable ∧ Q.slope = t) :
    F = V.hermitianHNFiltration := by
  obtain ⟨n, U, b, hU, hzero, hlast, _, hb, _, hat, hright, hreconstruct⟩ :=
    Submodule.exists_strictMono_flag_and_jumps_of_antitone hF hbot htop hleft
  have hfac : ∀ i : Fin n,
      (V.flagQuotientOfMeasurableBase U i).IsMeanSlopeSemistable ∧
      (V.flagQuotientOfMeasurableBase U i).slope = b i := by
    intro i
    have hp : (F (b i), ⨆ s : {s : ℝ // b i < s}, F s.val) =
        (U i.succ, U i.castSucc) := Prod.ext (hat i) (hright i)
    have he := congrArg (fun p : Submodule K V × Submodule K V ↦
      let Q := quotientOfMeasurableBase (V.restrictOfMeasurableBase p.1)
        (p.2.comap p.1.subtype)
      Module.finrank K (p.1 ⧸ p.2.comap p.1.subtype) = 0 ∨
        Q.IsMeanSlopeSemistable ∧ Q.slope = b i) hp
    have hg := Eq.mp he (hgraded (b i))
    have hl : U i.castSucc < U i.succ := hU Fin.castSucc_lt_succ
    have hr : 0 < Module.finrank K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype) := by
      have hneq : (U i.castSucc).comap (U i.succ).subtype ≠ ⊤ := by
        intro ht
        have hle : U i.succ ≤ U i.castSucc := by
          intro x hx
          have hm : (⟨x, hx⟩ : U i.succ) ∈ (U i.castSucc).comap (U i.succ).subtype := by
            rw [ht]
            exact Submodule.mem_top
          exact hm
        exact (not_le_of_gt hl) hle
      exact finrank_quotient_pos_of_ne_top _ hneq
    exact hg.resolve_left (Nat.ne_of_gt hr)
  have hmeans : StrictAnti (fun i ↦ (V.flagQuotientOfMeasurableBase U i).slope) := by
    intro i j hij
    change (V.flagQuotientOfMeasurableBase U j).slope <
      (V.flagQuotientOfMeasurableBase U i).slope
    rw [(hfac i).2, (hfac j).2]
    exact hb hij
  obtain ⟨hlen, hterms⟩ := V.semistableFlag_eq_hermitianHNTerm
    U hU hzero hlast (hsemi := (fun i ↦ (hfac i).1)) hmeans
  subst n
  have hflag : U = V.hermitianHNFlag := funext hterms
  have hmean : b = fun i ↦ (V.hermitianHNFactor i).slope := by
    funext i
    have he := congrArg (fun G : Fin (V.hermitianHNLength + 1) → Submodule K V ↦
      (V.flagQuotientOfMeasurableBase G i).slope) hflag
    exact (hfac i).2.symm.trans
      (he.trans (V.slope_hermitianHNFlag_quotient_eq_factor i))
  funext t
  calc
    F t = ⨆ i : Fin (V.hermitianHNLength), ⨆ (_ : t ≤ b i), U i.succ :=
      hreconstruct t
    _ = ⨆ i : Fin (V.hermitianHNLength),
        ⨆ (_ : t ≤ (V.hermitianHNFactor i).slope),
          V.hermitianHNTerm (i.val + 1) := by
      rw [hmean, hflag]
      rfl
    _ = V.hermitianHNFiltration t :=
      (V.hermitianHNFiltration_eq_iSup t).symm

end AdelicVectorBundle

end

end ArakelovGeometry
