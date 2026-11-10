/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Order.Preorder.Chain
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.Topology.Order.Basic

/-!
# Finite flags of real subspace filtrations

A decreasing filtration of a finite-dimensional vector space has finite image.
If it attains zero and the whole space and is locally constant on the left,
its nonzero levels have included real upper endpoints. These endpoints recover
the strict finite flag and the literal right-limit union at every jump.
-/

@[expose] public section

open Module

namespace Submodule

variable {K E : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- Enumerate all distinct filtration levels by a strict complete flag. -/
theorem exists_strictMono_flag_of_antitone {F : ℝ → Submodule K E}
    (hF : Antitone F) (hbot : ∃ t, F t = ⊥) (htop : ∃ t, F t = ⊤) :
    ∃ (n : ℕ) (U : Fin (n + 1) → Submodule K E),
      StrictMono U ∧ U 0 = ⊥ ∧ U (Fin.last n) = ⊤ ∧ Set.range U = Set.range F := by
  classical
  let S := Set.range F
  let : LinearOrder S := hF.isChain_range.lt_of_le.linearOrder
  let : Fintype S := hF.isChain_range.lt_of_le.finite_of_wellFoundedLT_of_wellFoundedGT.fintype
  let : Nonempty S := ⟨⟨F 0, 0, rfl⟩⟩
  let n := Fintype.card S - 1
  have hcard : Fintype.card S = n + 1 := by
    have := Fintype.card_pos (α := S)
    dsimp [n]
    omega
  let e := Fintype.orderIsoFinOfCardEq S hcard
  let U : Fin (n + 1) → Submodule K E := fun i => (e i).val
  have hU : StrictMono U := by
    intro i j hij
    exact e.strictMono hij
  refine ⟨n, U, hU, ?_, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hbot
    let z : S := ⟨⊥, t, ht⟩
    apply le_antisymm _ bot_le
    have h := hU.monotone (Fin.zero_le (e.symm z))
    simpa only [U, e.apply_symm_apply] using h
  · obtain ⟨t, ht⟩ := htop
    let z : S := ⟨⊤, t, ht⟩
    apply le_antisymm le_top
    have h := hU.monotone (Fin.le_last (e.symm z))
    simpa only [U, e.apply_symm_apply] using h
  · ext V
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hV
      obtain ⟨i, hi⟩ := e.surjective ⟨V, hV⟩
      exact ⟨i, congrArg Subtype.val hi⟩

/-- The intrinsic upper endpoint of the parameters containing a given level.
The endpoint theorem below applies to attained nonzero levels. -/
noncomputable def filtrationJump (F : ℝ → Submodule K E) (U : Submodule K E) : ℝ :=
  sSup {t | U ≤ F t}

omit [FiniteDimensional K E] in
/-- An attained nonzero level has an included upper endpoint. -/
theorem le_filtration_iff_le_jump {F : ℝ → Submodule K E} (hF : Antitone F)
    (hbot : ∃ t, F t = ⊥)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t)
    {U : Submodule K E} (hU : U ∈ Set.range F) (hne : U ≠ ⊥) (t : ℝ) :
    U ≤ F t ↔ t ≤ filtrationJump F U := by
  let A : Set ℝ := {s | U ≤ F s}
  have hnonempty : A.Nonempty := by
    obtain ⟨s, hs⟩ := hU
    exact ⟨s, le_of_eq hs.symm⟩
  have hbounded : BddAbove A := by
    obtain ⟨z, hz⟩ := hbot
    refine ⟨z, ?_⟩
    intro s hs
    by_contra hsz
    have hle : U ≤ ⊥ := (hs.trans (hF (le_of_lt (lt_of_not_ge hsz)))).trans
      (le_of_eq hz)
    exact hne (le_antisymm hle bot_le)
  have hbelow : ∀ s < filtrationJump F U, U ≤ F s := by
    intro s hs
    obtain ⟨z, hz, hsz⟩ := exists_lt_of_lt_csSup hnonempty hs
    exact hz.trans (hF hsz.le)
  have hat : U ≤ F (filtrationJump F U) := by
    obtain ⟨ε, hε, hconst⟩ := hleft (filtrationJump F U)
    have h1 : filtrationJump F U - ε < filtrationJump F U - ε / 2 := by linarith
    have h2 : filtrationJump F U - ε / 2 < filtrationJump F U := by linarith
    have hc := hconst (filtrationJump F U - ε / 2) h1 h2.le
    exact hc ▸ hbelow _ h2
  constructor
  · exact fun ht => le_csSup hbounded ht
  · exact fun ht => hat.trans (hF ht)

/-- Recover all real jump values and both sides of every jump from the actual
filtration. No finite-image or finite-flag hypothesis is supplied. -/
theorem exists_strictMono_flag_and_jumps_of_antitone {F : ℝ → Submodule K E}
    (hF : Antitone F) (hbot : ∃ t, F t = ⊥) (htop : ∃ t, F t = ⊤)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t) :
    ∃ (n : ℕ) (U : Fin (n + 1) → Submodule K E) (b : Fin n → ℝ),
      StrictMono U ∧ U 0 = ⊥ ∧ U (Fin.last n) = ⊤ ∧
      Set.range U = Set.range F ∧ StrictAnti b ∧
      (∀ i t, U i.succ ≤ F t ↔ t ≤ b i) ∧
      (∀ i, F (b i) = U i.succ) ∧
      (∀ i, (⨆ s : {s : ℝ // b i < s}, F s.val) = U i.castSucc) ∧
      (∀ t, F t = ⨆ (i : Fin n) (_ : t ≤ b i), U i.succ) := by
  obtain ⟨n, U, hU, hzero, htopU, hrange⟩ :=
    exists_strictMono_flag_of_antitone hF hbot htop
  let b : Fin n → ℝ := fun i => filtrationJump F (U i.succ)
  have hcut : ∀ i t, U i.succ ≤ F t ↔ t ≤ b i := by
    intro i t
    apply le_filtration_iff_le_jump hF hbot hleft
    · rw [← hrange]
      exact ⟨i.succ, rfl⟩
    · intro hi
      have hz : U i.succ = U 0 := hi.trans hzero.symm
      exact Fin.succ_ne_zero i (hU.injective hz)
  have hb : StrictAnti b := by
    intro i j hij
    obtain ⟨t, ht⟩ : U i.succ ∈ Set.range F := by
      rw [← hrange]
      exact ⟨i.succ, rfl⟩
    have hit : t ≤ b i := (hcut i t).mp (le_of_eq ht.symm)
    have hjt : ¬ t ≤ b j := by
      intro h
      have hle : U j.succ ≤ U i.succ := (hcut j t).mpr h |>.trans (le_of_eq ht)
      have hji := hU.le_iff_le.mp hle
      have hvals := Fin.succ_le_succ_iff.mp hji
      exact (not_le_of_gt hij) hvals
    exact lt_of_lt_of_le (lt_of_not_ge hjt) hit
  have hat : ∀ i, F (b i) = U i.succ := by
    intro i
    apply le_antisymm _ ((hcut i (b i)).mpr le_rfl)
    obtain ⟨j, hj⟩ : F (b i) ∈ Set.range U := by
      rw [hrange]
      exact ⟨b i, rfl⟩
    rw [← hj]
    apply hU.monotone
    by_contra hji
    have hij : i.succ < j := lt_of_not_ge hji
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · exact (not_lt_of_ge (Fin.zero_le _)) hij
    · have hik : i < k := by simpa only [Fin.succ_lt_succ_iff] using hij
      have hmem : b i ≤ b k := (hcut k (b i)).mp (le_of_eq hj)
      exact (not_le_of_gt (hb hik)) hmem
  have hright : ∀ i, (⨆ s : {s : ℝ // b i < s}, F s.val) = U i.castSucc := by
    intro i
    apply le_antisymm
    · apply iSup_le
      intro s
      obtain ⟨j, hj⟩ : F s.val ∈ Set.range U := by
        rw [hrange]
        exact ⟨s.val, rfl⟩
      rw [← hj]
      apply hU.monotone
      by_contra hji
      have hij : i.succ ≤ j := by
        have hvals : i.val < j.val := lt_of_not_ge hji
        change i.val + 1 ≤ j.val
        omega
      have hmem : U i.succ ≤ F s.val := (hU.monotone hij).trans (le_of_eq hj)
      exact (not_le_of_gt s.property) ((hcut i s.val).mp hmem)
    · rcases Fin.eq_zero_or_eq_succ i.castSucc with hz | ⟨j, hj⟩
      · rw [hz, hzero]
        exact bot_le
      · have hji : j < i := by
          have hv := congrArg Fin.val hj
          change j.val < i.val
          simp only [Fin.val_castSucc, Fin.val_succ] at hv
          omega
        have hbj : b i < b j := hb hji
        have hle : U i.castSucc ≤ F (b j) := by rw [hj, hat]
        exact le_iSup_of_le ⟨b j, hbj⟩ hle
  have hreconstruct : ∀ t, F t = ⨆ (i : Fin n) (_ : t ≤ b i), U i.succ := by
    intro t
    apply le_antisymm
    · obtain ⟨j, hj⟩ : F t ∈ Set.range U := by
        rw [hrange]
        exact ⟨t, rfl⟩
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
      · rw [← hj, hzero]
        exact bot_le
      · have ht : t ≤ b i := (hcut i t).mp (le_of_eq hj)
        rw [← hj]
        exact le_iSup_of_le i (le_iSup_of_le ht le_rfl)
    · exact iSup_le fun i => iSup_le fun hi => (hcut i t).mpr hi
  exact ⟨n, U, b, hU, hzero, htopU, hrange, hb, hcut, hat, hright, hreconstruct⟩

omit [FiniteDimensional K E] in
/-- A containment cut determines its jump intrinsically. -/
theorem filtrationJump_eq_of_cut {F : ℝ → Submodule K E} {U : Submodule K E}
    {b : ℝ} (hcut : ∀ t, U ≤ F t ↔ t ≤ b) : filtrationJump F U = b := by
  have hset : {t | U ≤ F t} = Set.Iic b := Set.ext hcut
  simp only [filtrationJump, hset, csSup_Iic]

omit [FiniteDimensional K E] in
/-- Distinct strict enumerations of the same levels have the same length. -/
theorem strictMono_flag_length_eq_of_range_eq {n m : ℕ}
    {U : Fin (n + 1) → Submodule K E} {V : Fin (m + 1) → Submodule K E}
    (hU : StrictMono U) (hV : StrictMono V) (h : Set.range U = Set.range V) : n = m := by
  let e := ((Equiv.ofInjective U hU.injective).trans (Set.equivOfEq h)).trans
    (Equiv.ofInjective V hV.injective).symm
  have hc := Fintype.card_congr e
  simpa only [Fintype.card_fin, Nat.add_right_cancel_iff] using hc

omit [FiniteDimensional K E] in
/-- The increasing enumeration of all levels is unique. -/
theorem strictMono_flag_eq_of_range_eq {n : ℕ}
    {U V : Fin (n + 1) → Submodule K E}
    (hU : StrictMono U) (hV : StrictMono V) (h : Set.range U = Set.range V) : U = V := by
  classical
  let S := Set.range U
  let : LinearOrder S := hU.monotone.isChain_range.lt_of_le.linearOrder
  let u : Fin (n + 1) → S := fun i => ⟨U i, i, rfl⟩
  let v : Fin (n + 1) → S := fun i => ⟨V i, by dsimp [S]; rw [h]; exact ⟨i, rfl⟩⟩
  have hu : StrictMono u := by intro i j hij; exact hU hij
  have hv : StrictMono v := by intro i j hij; exact hV hij
  let s := Finset.univ.image u
  have hs : s.card = n + 1 := by
    simpa only [s, Finset.card_univ, Fintype.card_fin] using
      Finset.card_image_of_injective Finset.univ hu.injective
  have humem : ∀ i, u i ∈ s := by
    intro i
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hvmem : ∀ i, v i ∈ s := by
    intro i
    obtain ⟨j, hj⟩ : V i ∈ Set.range U := (v i).property
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, Subtype.ext hj⟩
  have huv : u = v := (Finset.orderEmbOfFin_unique hs humem hu).trans
    (Finset.orderEmbOfFin_unique hs hvmem hv).symm
  funext i
  exact congrArg Subtype.val (congrFun huv i)

omit [FiniteDimensional K E] in
/-- Both levels and their real jump values are intrinsic to the filtration. -/
theorem strictMono_flag_and_jumps_unique {F : ℝ → Submodule K E} {n : ℕ}
    {U V : Fin (n + 1) → Submodule K E} {b c : Fin n → ℝ}
    (hU : StrictMono U) (hV : StrictMono V)
    (hrU : Set.range U = Set.range F) (hrV : Set.range V = Set.range F)
    (hb : ∀ i t, U i.succ ≤ F t ↔ t ≤ b i)
    (hc : ∀ i t, V i.succ ≤ F t ↔ t ≤ c i) : U = V ∧ b = c := by
  have hUV := strictMono_flag_eq_of_range_eq hU hV (hrU.trans hrV.symm)
  refine ⟨hUV, ?_⟩
  subst V
  funext i
  exact (filtrationJump_eq_of_cut (hb i)).symm.trans (filtrationJump_eq_of_cut (hc i))

omit [FiniteDimensional K E] in
/-- The only strict flag in the zero space is empty. -/
theorem strictMono_flag_length_eq_zero [Subsingleton E] {n : ℕ}
    {U : Fin (n + 1) → Submodule K E} (hU : StrictMono U) : n = 0 := by
  have heq : (0 : Fin (n + 1)) = Fin.last n := hU.injective (Subsingleton.elim _ _)
  have hv := congrArg Fin.val heq
  simpa using hv.symm

omit [FiniteDimensional K E] in
/-- Away from the extracted jumps the literal right-limit union equals the
filtration value. -/
theorem rightLimit_eq_of_not_jump {F : ℝ → Submodule K E} (hF : Antitone F)
    {n : ℕ} {U : Fin (n + 1) → Submodule K E} {b : Fin n → ℝ}
    (hzero : U 0 = ⊥) (hrange : Set.range U = Set.range F)
    (hcut : ∀ i t, U i.succ ≤ F t ↔ t ≤ b i) {t : ℝ}
    (ht : ∀ i, t ≠ b i) : (⨆ s : {s : ℝ // t < s}, F s.val) = F t := by
  apply le_antisymm
  · exact iSup_le fun s => hF s.property.le
  · obtain ⟨j, hj⟩ : F t ∈ Set.range U := by
      rw [hrange]
      exact ⟨t, rfl⟩
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
    · rw [← hj, hzero]
      exact bot_le
    · have hti : t < b i := lt_of_le_of_ne ((hcut i t).mp (le_of_eq hj)) (ht i)
      exact le_iSup_of_le ⟨b i, hti⟩ ((le_of_eq hj.symm).trans ((hcut i (b i)).mpr le_rfl))

omit [FiniteDimensional K E] in
/-- The right-limit supremum of a decreasing filtration is literally the
positive-increment union, with no span closure added. -/
theorem mem_rightLimit_iff {F : ℝ → Submodule K E} (hF : Antitone F) (t : ℝ) (x : E) :
    x ∈ (⨆ s : {s : ℝ // t < s}, F s.val) ↔ ∃ ε > 0, x ∈ F (t + ε) := by
  let : Nonempty {s : ℝ // t < s} := ⟨⟨t + 1, by linarith⟩⟩
  have hd : Directed (· ≤ ·) (fun s : {s : ℝ // t < s} => F s.val) := by
    intro s u
    refine ⟨⟨min s.val u.val, lt_min s.property u.property⟩, ?_, ?_⟩
    · exact hF (min_le_left _ _)
    · exact hF (min_le_right _ _)
  rw [mem_iSup_of_directed _ hd]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s.val - t, sub_pos.mpr s.property, ?_⟩
    simpa only [add_sub_cancel] using hs
  · rintro ⟨ε, hε, hx⟩
    exact ⟨⟨t + ε, by linarith⟩, hx⟩

end Submodule
