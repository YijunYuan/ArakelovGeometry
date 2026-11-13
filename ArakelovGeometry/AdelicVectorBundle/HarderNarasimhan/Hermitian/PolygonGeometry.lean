/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Polygon

import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Order.Interval.Set.Union

/-!
# Convex geometry of the Hermitian Harder–Narasimhan polygon

The convex hull of actual subspace degree points lies in the polygon hypograph.
-/

@[expose] public section

open scoped BigOperators
namespace ArakelovGeometry.AdelicVectorBundle
noncomputable section
universe u v w
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (V : AdelicVectorBundle.{w} S)
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]
  [hV : V.toNormFamily.IsHermitian]

/-- The convex hull of all actual rational subspace degree points lies
in the polygon's hypograph over the genuine rank interval. -/
theorem convexHull_degreePoints_subset_hermitianHNPolygon_hypograph :
    convexHull ℝ (Set.range (fun U : Submodule K V ↦
      ((Module.finrank K U : ℝ), (V.restrictOfMeasurableBase U).degree))) ⊆
        {p : ℝ × ℝ | p.1 ∈ Set.Icc 0 (Module.finrank K V : ℝ) ∧
          p.2 ≤ V.hermitianHNPolygon p.1} := by
  apply convexHull_min
  · rintro p ⟨U, rfl⟩
    exact ⟨⟨Nat.cast_nonneg _, Nat.cast_le.mpr U.finrank_le⟩,
      V.degree_restrict_le_hermitianHNPolygon U⟩
  · exact ((V.concaveOn_hermitianHNPolygon).subset
      (Set.subset_univ _) (convex_Icc 0 (Module.finrank K V : ℝ))).convex_hypograph

/-- On every actual unit rank interval, the polygon has the source's
actual ordered slope as its affine coefficient. -/
theorem hermitianHNPolygon_affine_unit (j : Fin (Module.finrank K V)) (x : ℝ)
    (hx : x ∈ Set.Icc (j.val : ℝ) ((j.val : ℝ) + 1)) :
    V.hermitianHNPolygon x =
      V.hermitianHNPolygon j.val +
        (x - (j.val : ℝ)) * V.hermitianHNOrderedSlope j := by
  let i := V.hermitianHNFactorIndex j
  have hi := V.hermitianHNFactorIndex_rank_interval j
  have hl : (Module.finrank K (V.hermitianHNTerm i.val) : ℝ) ≤ j.val :=
    Nat.cast_le.mpr hi.1
  have hu : (j.val : ℝ) + 1 ≤
      (Module.finrank K (V.hermitianHNTerm (i.val + 1)) : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hi.2
  have hPx := V.hermitianHNPolygon_affine_factor i x
    ⟨hl.trans hx.1, hx.2.trans hu⟩
  have hPj := V.hermitianHNPolygon_affine_factor i j.val
    ⟨hl, (by linarith : (j.val : ℝ) ≤ _).trans hu⟩
  change _ = _ + (x - (j.val : ℝ)) * (V.hermitianHNFactor i).slope
  rw [hPx, hPj]
  ring

/-- The difference of the actual polygon at consecutive integral ranks
is exactly the corresponding actual ordered slope. -/
theorem hermitianHNPolygon_unit_difference (j : Fin (Module.finrank K V)) :
    V.hermitianHNPolygon ((j.val : ℝ) + 1) -
      V.hermitianHNPolygon j.val = V.hermitianHNOrderedSlope j := by
  have h := V.hermitianHNPolygon_affine_unit j ((j.val : ℝ) + 1)
    ⟨by linarith, le_rfl⟩
  linarith

/-- Every real point of the positive-rank domain lies in an actual
HN factor's closed rank interval. -/
theorem exists_hermitianHNFactor_real_rank_interval
    (hr : 0 < Module.finrank K V) (x : ℝ)
    (hx : x ∈ Set.Icc 0 (Module.finrank K V : ℝ)) :
    ∃ i : Fin (V.hermitianHNLength),
      x ∈ Set.Icc (Module.finrank K (V.hermitianHNTerm i.val) : ℝ)
        (Module.finrank K (V.hermitianHNTerm (i.val + 1)) : ℝ) := by
  have hp := V.hermitianHNLength_pos_of_finrank_pos hr
  have hzRank : (Module.finrank K (V.hermitianHNTerm 0) : ℝ) = 0 := by
    have h := congrArg (fun U : Submodule K V ↦ (Module.finrank K U : ℝ))
      (V.hermitianHNTerm_zero)
    exact h.trans (by exact_mod_cast (finrank_bot K V))
  have hnRank :
      (Module.finrank K (V.hermitianHNTerm
        (V.hermitianHNLength)) : ℝ) = (Module.finrank K V : ℝ) := by
    have h := congrArg (fun U : Submodule K V ↦ (Module.finrank K U : ℝ))
      (V.hermitianHNTerm_length_eq_top)
    exact h.trans (by exact_mod_cast (finrank_top K V))
  by_cases hx0 : x = 0
  · subst x
    refine ⟨⟨0, hp⟩, ?_⟩
    change (Module.finrank K (V.hermitianHNTerm 0) : ℝ) ≤ 0 ∧
      0 ≤ (Module.finrank K (V.hermitianHNTerm 1) : ℝ)
    exact ⟨le_of_eq hzRank, Nat.cast_nonneg _⟩
  · let r : ℕ → ℝ := fun m ↦ Module.finrank K (V.hermitianHNTerm m)
    have h0 : r 0 = 0 := hzRank
    have hn : r (V.hermitianHNLength) = (Module.finrank K V : ℝ) := hnRank
    have hi : x ∈ Set.Ioc (r 0) (r (V.hermitianHNLength)) := by
      rw [h0, hn]
      exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), hx.2⟩
    have hu := Ioc_subset_biUnion_Ioc (V.hermitianHNLength) r hi
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hu
    obtain ⟨hmn, hxmem⟩ := Set.mem_iUnion.mp hm
    exact ⟨⟨m, Finset.mem_range.mp hmn⟩, hxmem.1.le, hxmem.2⟩

/-- Every actual graph point is in the convex hull of genuine
rational-subspace degree points. -/
theorem hermitianHNPolygon_graph_mem_convexHull_degreePoints (x : ℝ)
    (hx : x ∈ Set.Icc 0 (Module.finrank K V : ℝ)) :
    (x, V.hermitianHNPolygon x) ∈
      convexHull ℝ (Set.range (fun U : Submodule K V ↦
        ((Module.finrank K U : ℝ), (V.restrictOfMeasurableBase U).degree))) := by
  let A : Set (ℝ × ℝ) := Set.range (fun U : Submodule K V ↦
    ((Module.finrank K U : ℝ), (V.restrictOfMeasurableBase U).degree))
  by_cases hr : 0 < Module.finrank K V
  · obtain ⟨i, hi⟩ := V.exists_hermitianHNFactor_real_rank_interval hr x hx
    let r : ℝ := Module.finrank K (V.hermitianHNTerm i.val)
    let s : ℝ := Module.finrank K (V.hermitianHNTerm (i.val + 1))
    let D := (V.restrictOfMeasurableBase (V.hermitianHNTerm i.val)).degree
    let D' := (V.restrictOfMeasurableBase
      (V.hermitianHNTerm (i.val + 1))).degree
    let β := (V.hermitianHNFactor i).slope
    have hrs : r < s := Nat.cast_lt.mpr
      (Submodule.finrank_lt_finrank_of_lt (V.hermitianHNTerm_lt i.val
        (i.val + 1) (Nat.lt_succ_self _) (Nat.succ_le_of_lt i.isLt)))
    have hd : 0 < s - r := sub_pos.mpr hrs
    let a := (s - x) / (s - r)
    let b := (x - r) / (s - r)
    have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hi.2) hd.le
    have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hi.1) hd.le
    have hab : a + b = 1 := by
      change (s - x) / (s - r) + (x - r) / (s - r) = 1
      rw [← add_div]
      have hn : (s - x) + (x - r) = s - r := by ring
      rw [hn, div_self hd.ne']
    have hc : a * r + b * s = x := by
      change (s - x) / (s - r) * r + (x - r) / (s - r) * s = x
      field_simp [hd.ne']
      ring
    have hD : D' = D + (s - r) * β :=
      (V.hermitianHNSupportLine_rank_factor_end i).symm.trans
        (V.hermitianHNSupportLine_factor_slope i s)
    have haf : a * D + b * D' = V.hermitianHNPolygon x := by
      rw [hD, V.hermitianHNPolygon_affine_factor i x hi]
      change a * D + b * (D + (s - r) * β) = D + (x - r) * β
      calc
        _ = (a + b) * D + (a * r + b * s - (a + b) * r) * β := by ring
        _ = _ := by rw [hab, hc, one_mul, one_mul]
    have hpr : (r, D) ∈ convexHull ℝ A :=
      subset_convexHull ℝ A ⟨V.hermitianHNTerm i.val, rfl⟩
    have hps : (s, D') ∈ convexHull ℝ A :=
      subset_convexHull ℝ A ⟨V.hermitianHNTerm (i.val + 1), rfl⟩
    have hcomb := convex_convexHull ℝ A hpr hps ha hb hab
    have heq : a • (r, D) + b • (s, D') =
        (x, V.hermitianHNPolygon x) := by
      apply Prod.ext
      · exact hc
      · exact haf
    exact heq ▸ hcomb
  · have hr0 : Module.finrank K V = 0 := Nat.eq_zero_of_not_pos hr
    have hx0 : x = 0 := le_antisymm (by simpa only [hr0, Nat.cast_zero] using hx.2) hx.1
    have hzRank : (Module.finrank K (V.hermitianHNTerm 0) : ℝ) = 0 := by
      have h := congrArg (fun U : Submodule K V ↦ (Module.finrank K U : ℝ))
        (V.hermitianHNTerm_zero)
      exact h.trans (by exact_mod_cast (finrank_bot K V))
    have hp := V.hermitianHNPolygon_rank_term 0 (Nat.zero_le _)
    have hv : (x, V.hermitianHNPolygon x) =
        ((Module.finrank K (V.hermitianHNTerm 0) : ℝ),
          (V.restrictOfMeasurableBase (V.hermitianHNTerm 0)).degree) := by
      apply Prod.ext
      · exact hx0.trans hzRank.symm
      · simpa only [hzRank, hx0] using hp
    exact hv ▸ subset_convexHull ℝ A ⟨V.hermitianHNTerm 0, rfl⟩

/-- The actual polygon is the greatest height of each convex-hull fibre
over its genuine rank interval. -/
theorem hermitianHNPolygon_isGreatest_degreePoints_hull_fibre (x : ℝ)
    (hx : x ∈ Set.Icc 0 (Module.finrank K V : ℝ)) :
    IsGreatest {y : ℝ | (x, y) ∈
      convexHull ℝ (Set.range (fun U : Submodule K V ↦
        ((Module.finrank K U : ℝ), (V.restrictOfMeasurableBase U).degree)))}
      (V.hermitianHNPolygon x) :=
  ⟨V.hermitianHNPolygon_graph_mem_convexHull_degreePoints x hx,
    fun _ hy ↦ (V.convexHull_degreePoints_subset_hermitianHNPolygon_hypograph
       hy).2⟩

/-- Away from actual internal HN ranks, the actual polygon agrees with
an affine function on an open neighbourhood inside its domain. -/
theorem hermitianHNPolygon_locally_affine_of_not_internal_rank (x : ℝ)
    (hx : x ∈ Set.Ioo 0 (Module.finrank K V : ℝ))
    (hnot : ∀ m : ℕ, 0 < m → m < V.hermitianHNLength →
      x ≠ (Module.finrank K (V.hermitianHNTerm m) : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ c b : ℝ, ∀ y ∈ Set.Ioo (x - ε) (x + ε),
      V.hermitianHNPolygon y = c + y * b := by
  have hr : 0 < Module.finrank K V := by exact_mod_cast (lt_trans hx.1 hx.2)
  obtain ⟨i, hi⟩ := V.exists_hermitianHNFactor_real_rank_interval hr x
    ⟨hx.1.le, hx.2.le⟩
  let r : ℝ := Module.finrank K (V.hermitianHNTerm i.val)
  let s : ℝ := Module.finrank K (V.hermitianHNTerm (i.val + 1))
  have hzRank : (Module.finrank K (V.hermitianHNTerm 0) : ℝ) = 0 := by
    have h := congrArg (fun U : Submodule K V ↦ (Module.finrank K U : ℝ))
      (V.hermitianHNTerm_zero)
    exact h.trans (by exact_mod_cast (finrank_bot K V))
  have hnRank :
      (Module.finrank K (V.hermitianHNTerm
        (V.hermitianHNLength)) : ℝ) = (Module.finrank K V : ℝ) := by
    have h := congrArg (fun U : Submodule K V ↦ (Module.finrank K U : ℝ))
      (V.hermitianHNTerm_length_eq_top)
    exact h.trans (by exact_mod_cast (finrank_top K V))
  have hl : r < x := by
    apply lt_of_le_of_ne hi.1
    intro he
    by_cases hiz : i.val = 0
    · have hri : r = 0 := (congrArg (fun m : ℕ ↦
          (Module.finrank K (V.hermitianHNTerm m) : ℝ)) hiz).trans hzRank
      have hx0 := he.symm.trans hri
      linarith [hx.1]
    · exact hnot i.val (Nat.pos_of_ne_zero hiz) i.isLt he.symm
  have hu : x < s := by
    apply lt_of_le_of_ne hi.2
    intro he
    by_cases hie : i.val + 1 = V.hermitianHNLength
    · have hsi : s = (Module.finrank K V : ℝ) :=
        (congrArg (fun m : ℕ ↦
          (Module.finrank K (V.hermitianHNTerm m) : ℝ)) hie).trans hnRank
      have hxe := he.trans hsi
      linarith [hx.2]
    · exact hnot (i.val + 1) (Nat.succ_pos _)
        (lt_of_le_of_ne (Nat.succ_le_of_lt i.isLt) hie) he
  let ε := min (x - r) (s - x)
  have he : 0 < ε := lt_min (sub_pos.mpr hl) (sub_pos.mpr hu)
  refine ⟨ε, he,
    (V.restrictOfMeasurableBase (V.hermitianHNTerm i.val)).degree -
      r * (V.hermitianHNFactor i).slope,
    (V.hermitianHNFactor i).slope, ?_⟩
  intro y hy
  have hyr : r ≤ y := by
    have h := min_le_left (x - r) (s - x)
    change ε ≤ x - r at h
    linarith [hy.1]
  have hys : y ≤ s := by
    have h := min_le_right (x - r) (s - x)
    change ε ≤ s - x at h
    linarith [hy.2]
  rw [V.hermitianHNPolygon_affine_factor i y ⟨hyr, hys⟩]
  change _ = _ - r * _ + y * _
  ring

/-- An actual internal HN flag rank is a genuine local slope break:
no affine function agrees with the polygon on an open neighbourhood. -/
theorem hermitianHNPolygon_not_locally_affine_at_internal_rank
    (m : ℕ) (hm : 0 < m) (hmn : m < V.hermitianHNLength) :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∃ c b : ℝ,
      ∀ y ∈ Set.Ioo
        ((Module.finrank K (V.hermitianHNTerm m) : ℝ) - ε)
        ((Module.finrank K (V.hermitianHNTerm m) : ℝ) + ε),
        V.hermitianHNPolygon y = c + y * b := by
  rintro ⟨ε, he, c, b, ha⟩
  let i : Fin (V.hermitianHNLength) := ⟨m - 1, by omega⟩
  let j : Fin (V.hermitianHNLength) := ⟨m, hmn⟩
  let l : ℝ := Module.finrank K (V.hermitianHNTerm (m - 1))
  let x : ℝ := Module.finrank K (V.hermitianHNTerm m)
  let r : ℝ := Module.finrank K (V.hermitianHNTerm (m + 1))
  have hli : l < x := Nat.cast_lt.mpr
    (Submodule.finrank_lt_finrank_of_lt (V.hermitianHNTerm_lt
      (m - 1) m (by omega) hmn.le))
  have hjr : x < r := Nat.cast_lt.mpr
    (Submodule.finrank_lt_finrank_of_lt (V.hermitianHNTerm_lt
      m (m + 1) (Nat.lt_succ_self _) (Nat.succ_le_of_lt hmn)))
  have hxend :
      (Module.finrank K (V.hermitianHNTerm (i.val + 1)) : ℝ) = x :=
    congrArg (fun k : ℕ ↦ (Module.finrank K (V.hermitianHNTerm k) : ℝ))
      (show i.val + 1 = m by dsimp [i]; omega)
  let δ := min ε (min (x - l) (r - x)) / 2
  have hd : 0 < δ := div_pos (lt_min he (lt_min (sub_pos.mpr hli) (sub_pos.mpr hjr)))
    (by norm_num)
  have hde : δ < ε := by
    have h := min_le_left ε (min (x - l) (r - x))
    dsimp [δ]
    linarith
  have hdl : δ ≤ x - l := by
    have h := (min_le_right ε (min (x - l) (r - x))).trans (min_le_left (x - l) (r - x))
    dsimp [δ]
    linarith
  have hdr : δ ≤ r - x := by
    have h := (min_le_right ε (min (x - l) (r - x))).trans (min_le_right (x - l) (r - x))
    dsimp [δ]
    linarith
  have hLx := V.hermitianHNPolygon_affine_factor i x
    ⟨hli.le, le_of_eq hxend.symm⟩
  have hLm := V.hermitianHNPolygon_affine_factor i (x - δ)
    ⟨by change l ≤ x - δ; linarith,
      by rw [hxend]; linarith⟩
  have hRx := V.hermitianHNPolygon_affine_factor j x
    ⟨le_rfl, hjr.le⟩
  have hRp := V.hermitianHNPolygon_affine_factor j (x + δ)
    ⟨by change x ≤ x + δ; linarith,
      by change x + δ ≤ r; linarith⟩
  have hdL : V.hermitianHNPolygon x -
      V.hermitianHNPolygon (x - δ) =
        δ * (V.hermitianHNFactor i).slope := by
    rw [hLx, hLm]
    ring
  have hdR : V.hermitianHNPolygon (x + δ) -
      V.hermitianHNPolygon x =
        δ * (V.hermitianHNFactor j).slope := by
    rw [hRp, hRx]
    ring
  have hax := ha x ⟨by change x - ε < x; linarith, by change x < x + ε; linarith⟩
  have ham := ha (x - δ)
    ⟨by change x - ε < x - δ; linarith, by change x - δ < x + ε; linarith⟩
  have hap := ha (x + δ)
    ⟨by change x - ε < x + δ; linarith, by change x + δ < x + ε; linarith⟩
  rw [hax, ham] at hdL
  rw [hap, hax] at hdR
  have hstrict := V.hermitianHNFactor_slope_strictAnti
    (show i < j by change m - 1 < m; omega)
  nlinarith

/-- The literal local-affinity criterion detects exactly the actual
internal HN flag ranks, within the genuine open rank domain. -/
theorem hermitianHNPolygon_not_locally_affine_iff_internal_rank (x : ℝ)
    (hx : x ∈ Set.Ioo 0 (Module.finrank K V : ℝ)) :
    (¬ ∃ ε : ℝ, 0 < ε ∧ ∃ c b : ℝ,
      ∀ y ∈ Set.Ioo (x - ε) (x + ε),
        V.hermitianHNPolygon y = c + y * b) ↔
      ∃ m : ℕ, 0 < m ∧ m < V.hermitianHNLength ∧
        x = (Module.finrank K (V.hermitianHNTerm m) : ℝ) := by
  constructor
  · intro h
    by_contra hn
    have hnot : ∀ m : ℕ, 0 < m → m < V.hermitianHNLength →
        x ≠ (Module.finrank K (V.hermitianHNTerm m) : ℝ) := by
      intro m hm hmn he
      exact hn ⟨m, hm, hmn, he⟩
    exact h (V.hermitianHNPolygon_locally_affine_of_not_internal_rank x hx hnot)
  · rintro ⟨m, hm, hmn, rfl⟩
    exact V.hermitianHNPolygon_not_locally_affine_at_internal_rank m hm hmn

end
end ArakelovGeometry.AdelicVectorBundle
