/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.Filtration.Defs

import HarderNarasimhan.Filtration.Unique

/-!
# Finite Harder–Narasimhan flags

Upstream relation series give existence and uniqueness of finite flags. This
includes the zero-length flag when the lattice is subsingleton.
-/

@[expose] public section

open HarderNarasimhan

namespace HarderNarasimhan.PayoffFunction

variable {L C : Type*} [Lattice L] [BoundedOrder L]
  [WellFoundedGT L] [CompleteLinearOrder C]
  {μ : PayoffFunction L C} [μ.ADCC] [μ.IsConvex]

omit [BoundedOrder L] [WellFoundedGT L] [μ.ADCC] [μ.IsConvex] in
open Fin.NatCast in
/-- Decreasing interval values supply the successive-value condition in the
upstream finite-series uniqueness theorem. -/
theorem relSeries_not_A_le_succ_of_strictAnti (s : RelSeries μ.semistableRel)
    (hA : StrictAnti fun i : Fin s.length ↦
      μ.A ⟨s.toFun i.castSucc, s.toFun i.succ, (s.step i).choose⟩) :
    ∀ i : ℕ, (hi : i + 1 < s.length) →
      ¬ μ.A ⟨s.toFun ↑i, s.toFun ↑(i + 1), relSeries_step_lt s hi⟩ ≤
        μ.A ⟨s.toFun ↑(i + 1), s.toFun ↑(i + 2), relSeries_succ_step_lt s hi⟩ := by
  intro i hi
  have hlt := hA (show (⟨i, by omega⟩ : Fin s.length) < ⟨i + 1, hi⟩ from Nat.lt_add_one i)
  apply not_le_of_gt
  simpa only [Fin.castSucc_mk, Fin.succ_mk,
    Fin.natCast_eq_mk (show i < s.length + 1 by omega),
    Fin.natCast_eq_mk (show i + 1 < s.length + 1 by omega),
    Fin.natCast_eq_mk (show i + 1 + 1 < s.length + 1 by omega)] using hlt

omit [BoundedOrder L] [WellFoundedGT L] [μ.ADCC] [μ.IsConvex] in
open Fin.NatCast in
/-- The successive-value condition on a relation series gives strictly decreasing values. -/
theorem relSeries_strictAnti_A (s : RelSeries μ.semistableRel)
    (hA : ∀ i : ℕ, (hi : i + 1 < s.length) →
      ¬ μ.A ⟨s.toFun ↑i, s.toFun ↑(i + 1), relSeries_step_lt s hi⟩ ≤
        μ.A ⟨s.toFun ↑(i + 1), s.toFun ↑(i + 2), relSeries_succ_step_lt s hi⟩) :
    StrictAnti fun i : Fin s.length ↦
      μ.A ⟨s.toFun i.castSucc, s.toFun i.succ, (s.step i).choose⟩ := by
  rcases s with ⟨n, F, hF⟩
  cases n with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
    apply Fin.strictAnti_iff_succ_lt.mpr
    rintro ⟨i, hi⟩
    have h := hA i (Nat.succ_lt_succ hi)
    apply lt_of_not_ge
    simpa only [Fin.castSucc_mk, Fin.succ_mk,
      Fin.natCast_eq_mk (show i < n + 1 + 1 by omega),
      Fin.natCast_eq_mk (show i + 1 < n + 1 + 1 by omega),
      Fin.natCast_eq_mk (show i + 1 + 1 < n + 1 + 1 by omega)] using h

/-- Every convex game satisfying the chain conditions admits a finite semistable flag,
including the zero-length flag of a subsingleton lattice. -/
theorem exists_finiteFlag :
    ∃ (n : ℕ) (F : Fin (n + 1) → L) (hF : StrictMono F),
      F 0 = ⊥ ∧ F (Fin.last n) = ⊤ ∧
      (∀ i : Fin n,
        (μ.restrict ⟨F i.castSucc, F i.succ, hF Fin.castSucc_lt_succ⟩).IsSemistable) ∧
      StrictAnti (fun i : Fin n ↦
        μ.A ⟨F i.castSucc, F i.succ, hF Fin.castSucc_lt_succ⟩) := by
  cases subsingleton_or_nontrivial L with
  | inl hL =>
    let := hL
    let hF : StrictMono (fun _ : Fin 1 ↦ (⊥ : L)) := by
      intro i j hij
      exact (hij.ne (Subsingleton.elim i j)).elim
    exact ⟨0, fun _ ↦ ⊥, hF, rfl, Subsingleton.elim _ _,
      (fun i ↦ Fin.elim0 i), fun i ↦ Fin.elim0 i⟩
  | inr hL =>
    let := hL
    obtain ⟨s, hs0, hstop, hsA⟩ := μ.exists_relSeries_semistableRel
    exact ⟨s.length, s.toFun, relSeries_strictMono s, hs0, hstop,
      (fun i ↦ (s.step i).choose_spec), relSeries_strictAnti_A s hsA⟩

/-- Finite semistable flags with decreasing game values are equal, including
their lengths. -/
theorem finiteFlags_eq {n m : ℕ} (F : Fin (n + 1) → L) (G : Fin (m + 1) → L)
    (hF : StrictMono F) (hG : StrictMono G)
    (hF0 : F 0 = ⊥) (hG0 : G 0 = ⊥)
    (hFtop : F (Fin.last n) = ⊤) (hGtop : G (Fin.last m) = ⊤)
    [hFsemi : ∀ i : Fin n,
      (μ.restrict ⟨F i.castSucc, F i.succ, hF Fin.castSucc_lt_succ⟩).IsSemistable]
    [hGsemi : ∀ i : Fin m,
      (μ.restrict ⟨G i.castSucc, G i.succ, hG Fin.castSucc_lt_succ⟩).IsSemistable]
    (hFA : StrictAnti fun i : Fin n ↦
      μ.A ⟨F i.castSucc, F i.succ, hF Fin.castSucc_lt_succ⟩)
    (hGA : StrictAnti fun i : Fin m ↦
      μ.A ⟨G i.castSucc, G i.succ, hG Fin.castSucc_lt_succ⟩) :
    (⟨n, F⟩ : Σ k : ℕ, Fin (k + 1) → L) = ⟨m, G⟩ := by
  cases subsingleton_or_nontrivial L with
  | inl hL =>
    let := hL
    have hn : n = 0 := by
      have h := congrArg Fin.val (hF.injective (Subsingleton.elim (F (Fin.last n)) (F 0)))
      simpa only [Fin.val_last, Fin.val_zero] using h
    have hm : m = 0 := by
      have h := congrArg Fin.val (hG.injective (Subsingleton.elim (G (Fin.last m)) (G 0)))
      simpa only [Fin.val_last, Fin.val_zero] using h
    subst n m
    exact congrArg (fun f : Fin 1 → L ↦ (⟨0, f⟩ : Σ k : ℕ, Fin (k + 1) → L))
      (Subsingleton.elim F G)
  | inr hL =>
    let := hL
    let sF : RelSeries μ.semistableRel :=
      ⟨n, F, fun i ↦ ⟨hF Fin.castSucc_lt_succ, hFsemi i⟩⟩
    let sG : RelSeries μ.semistableRel :=
      ⟨m, G, fun i ↦ ⟨hG Fin.castSucc_lt_succ, hGsemi i⟩⟩
    obtain ⟨s, hs, hunique⟩ := μ.existsUnique_relSeries_semistableRel
    have heq : sF = sG :=
      (hunique sF ⟨hF0, hFtop, relSeries_not_A_le_succ_of_strictAnti sF hFA⟩).trans
        (hunique sG ⟨hG0, hGtop, relSeries_not_A_le_succ_of_strictAnti sG hGA⟩).symm
    exact congrArg (fun t : RelSeries μ.semistableRel ↦
      (⟨t.length, t.toFun⟩ : Σ k : ℕ, Fin (k + 1) → L)) heq

end HarderNarasimhan.PayoffFunction
