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
variable (V : AdelicVectorBundle S E)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hV : V.toNormFamily.IsHermitian hN)

/-- The convex hull of all actual rational subspace degree points lies
in the polygon's hypograph over the genuine rank interval. -/
theorem convexHull_degreePoints_subset_hermitianHNPolygon_hypograph :
    convexHull ℝ (Set.range (fun U : Submodule K E ↦
      ((Module.finrank K U : ℝ), (V.restrictOfMeasurableBase U hS).degree hS hN))) ⊆
        {p : ℝ × ℝ | p.1 ∈ Set.Icc 0 (Module.finrank K E : ℝ) ∧
          p.2 ≤ V.hermitianHNPolygon hS hN hV p.1} := by
  apply convexHull_min
  · rintro p ⟨U, rfl⟩
    exact ⟨⟨Nat.cast_nonneg _, Nat.cast_le.mpr U.finrank_le⟩,
      V.degree_restrict_le_hermitianHNPolygon hS hN hV U⟩
  · exact ((V.concaveOn_hermitianHNPolygon hS hN hV).subset
      (Set.subset_univ _) (convex_Icc 0 (Module.finrank K E : ℝ))).convex_hypograph

/-- On every actual unit rank interval, the polygon has the source's
actual ordered slope as its affine coefficient. -/
theorem hermitianHNPolygon_affine_unit (j : Fin (Module.finrank K E)) (x : ℝ)
    (hx : x ∈ Set.Icc (j.val : ℝ) ((j.val : ℝ) + 1)) :
    V.hermitianHNPolygon hS hN hV x =
      V.hermitianHNPolygon hS hN hV j.val +
        (x - (j.val : ℝ)) * V.hermitianHNOrderedSlope hS hN hV j := by
  let i := V.hermitianHNFactorIndex hS hN hV j
  have hi := V.hermitianHNFactorIndex_rank_interval hS hN hV j
  have hl : (Module.finrank K (V.hermitianHNTerm hS hN hV i.val) : ℝ) ≤ j.val :=
    Nat.cast_le.mpr hi.1
  have hu : (j.val : ℝ) + 1 ≤
      (Module.finrank K (V.hermitianHNTerm hS hN hV (i.val + 1)) : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hi.2
  have hPx := V.hermitianHNPolygon_affine_factor hS hN hV i x
    ⟨hl.trans hx.1, hx.2.trans hu⟩
  have hPj := V.hermitianHNPolygon_affine_factor hS hN hV i j.val
    ⟨hl, (by linarith : (j.val : ℝ) ≤ _).trans hu⟩
  change _ = _ + (x - (j.val : ℝ)) * (V.hermitianHNFactor hS hN hV i).slope hS hN
  rw [hPx, hPj]
  ring

/-- The difference of the actual polygon at consecutive integral ranks
is exactly the corresponding actual ordered slope. -/
theorem hermitianHNPolygon_unit_difference (j : Fin (Module.finrank K E)) :
    V.hermitianHNPolygon hS hN hV ((j.val : ℝ) + 1) -
      V.hermitianHNPolygon hS hN hV j.val = V.hermitianHNOrderedSlope hS hN hV j := by
  have h := V.hermitianHNPolygon_affine_unit hS hN hV j ((j.val : ℝ) + 1)
    ⟨by linarith, le_rfl⟩
  linarith

/-- Every real point of the positive-rank domain lies in an actual
HN factor's closed rank interval. -/
theorem exists_hermitianHNFactor_real_rank_interval
    (hr : 0 < Module.finrank K E) (x : ℝ)
    (hx : x ∈ Set.Icc 0 (Module.finrank K E : ℝ)) :
    ∃ i : Fin (V.hermitianHNLength hS hN hV),
      x ∈ Set.Icc (Module.finrank K (V.hermitianHNTerm hS hN hV i.val) : ℝ)
        (Module.finrank K (V.hermitianHNTerm hS hN hV (i.val + 1)) : ℝ) := by
  have hp := V.hermitianHNLength_pos_of_finrank_pos hS hN hV hr
  have hzRank : (Module.finrank K (V.hermitianHNTerm hS hN hV 0) : ℝ) = 0 := by
    have h := congrArg (fun U : Submodule K E ↦ (Module.finrank K U : ℝ))
      (V.hermitianHNTerm_zero hS hN hV)
    exact h.trans (by exact_mod_cast (finrank_bot K E))
  have hnRank :
      (Module.finrank K (V.hermitianHNTerm hS hN hV
        (V.hermitianHNLength hS hN hV)) : ℝ) = (Module.finrank K E : ℝ) := by
    have h := congrArg (fun U : Submodule K E ↦ (Module.finrank K U : ℝ))
      (V.hermitianHNTerm_length_eq_top hS hN hV)
    exact h.trans (by exact_mod_cast (finrank_top K E))
  by_cases hx0 : x = 0
  · subst x
    refine ⟨⟨0, hp⟩, ?_⟩
    change (Module.finrank K (V.hermitianHNTerm hS hN hV 0) : ℝ) ≤ 0 ∧
      0 ≤ (Module.finrank K (V.hermitianHNTerm hS hN hV 1) : ℝ)
    exact ⟨le_of_eq hzRank, Nat.cast_nonneg _⟩
  · let r : ℕ → ℝ := fun m ↦ Module.finrank K (V.hermitianHNTerm hS hN hV m)
    have h0 : r 0 = 0 := hzRank
    have hn : r (V.hermitianHNLength hS hN hV) = (Module.finrank K E : ℝ) := hnRank
    have hi : x ∈ Set.Ioc (r 0) (r (V.hermitianHNLength hS hN hV)) := by
      rw [h0, hn]
      exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), hx.2⟩
    have hu := Ioc_subset_biUnion_Ioc (V.hermitianHNLength hS hN hV) r hi
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hu
    obtain ⟨hmn, hxmem⟩ := Set.mem_iUnion.mp hm
    exact ⟨⟨m, Finset.mem_range.mp hmn⟩, hxmem.1.le, hxmem.2⟩

/-- Every actual graph point is in the convex hull of genuine
rational-subspace degree points. -/
theorem hermitianHNPolygon_graph_mem_convexHull_degreePoints (x : ℝ)
    (hx : x ∈ Set.Icc 0 (Module.finrank K E : ℝ)) :
    (x, V.hermitianHNPolygon hS hN hV x) ∈
      convexHull ℝ (Set.range (fun U : Submodule K E ↦
        ((Module.finrank K U : ℝ), (V.restrictOfMeasurableBase U hS).degree hS hN))) := by
  let A : Set (ℝ × ℝ) := Set.range (fun U : Submodule K E ↦
    ((Module.finrank K U : ℝ), (V.restrictOfMeasurableBase U hS).degree hS hN))
  by_cases hr : 0 < Module.finrank K E
  · obtain ⟨i, hi⟩ := V.exists_hermitianHNFactor_real_rank_interval hS hN hV hr x hx
    let r : ℝ := Module.finrank K (V.hermitianHNTerm hS hN hV i.val)
    let s : ℝ := Module.finrank K (V.hermitianHNTerm hS hN hV (i.val + 1))
    let D := (V.restrictOfMeasurableBase (V.hermitianHNTerm hS hN hV i.val) hS).degree hS hN
    let D' := (V.restrictOfMeasurableBase
      (V.hermitianHNTerm hS hN hV (i.val + 1)) hS).degree hS hN
    let β := (V.hermitianHNFactor hS hN hV i).slope hS hN
    have hrs : r < s := Nat.cast_lt.mpr
      (Submodule.finrank_lt_finrank_of_lt (V.hermitianHNTerm_lt hS hN hV i.val
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
      (V.hermitianHNSupportLine_rank_factor_end hS hN hV i).symm.trans
        (V.hermitianHNSupportLine_factor_slope hS hN hV i s)
    have haf : a * D + b * D' = V.hermitianHNPolygon hS hN hV x := by
      rw [hD, V.hermitianHNPolygon_affine_factor hS hN hV i x hi]
      change a * D + b * (D + (s - r) * β) = D + (x - r) * β
      calc
        _ = (a + b) * D + (a * r + b * s - (a + b) * r) * β := by ring
        _ = _ := by rw [hab, hc, one_mul, one_mul]
    have hpr : (r, D) ∈ convexHull ℝ A :=
      subset_convexHull ℝ A ⟨V.hermitianHNTerm hS hN hV i.val, rfl⟩
    have hps : (s, D') ∈ convexHull ℝ A :=
      subset_convexHull ℝ A ⟨V.hermitianHNTerm hS hN hV (i.val + 1), rfl⟩
    have hcomb := convex_convexHull ℝ A hpr hps ha hb hab
    have heq : a • (r, D) + b • (s, D') =
        (x, V.hermitianHNPolygon hS hN hV x) := by
      apply Prod.ext
      · exact hc
      · exact haf
    exact heq ▸ hcomb
  · have hr0 : Module.finrank K E = 0 := Nat.eq_zero_of_not_pos hr
    have hx0 : x = 0 := le_antisymm (by simpa only [hr0, Nat.cast_zero] using hx.2) hx.1
    have hzRank : (Module.finrank K (V.hermitianHNTerm hS hN hV 0) : ℝ) = 0 := by
      have h := congrArg (fun U : Submodule K E ↦ (Module.finrank K U : ℝ))
        (V.hermitianHNTerm_zero hS hN hV)
      exact h.trans (by exact_mod_cast (finrank_bot K E))
    have hp := V.hermitianHNPolygon_rank_term hS hN hV 0 (Nat.zero_le _)
    have hv : (x, V.hermitianHNPolygon hS hN hV x) =
        ((Module.finrank K (V.hermitianHNTerm hS hN hV 0) : ℝ),
          (V.restrictOfMeasurableBase (V.hermitianHNTerm hS hN hV 0) hS).degree hS hN) := by
      apply Prod.ext
      · exact hx0.trans hzRank.symm
      · simpa only [hzRank, hx0] using hp
    exact hv ▸ subset_convexHull ℝ A ⟨V.hermitianHNTerm hS hN hV 0, rfl⟩

/-- The actual polygon is the greatest height of each convex-hull fibre
over its genuine rank interval. -/
theorem hermitianHNPolygon_isGreatest_degreePoints_hull_fibre (x : ℝ)
    (hx : x ∈ Set.Icc 0 (Module.finrank K E : ℝ)) :
    IsGreatest {y : ℝ | (x, y) ∈
      convexHull ℝ (Set.range (fun U : Submodule K E ↦
        ((Module.finrank K U : ℝ), (V.restrictOfMeasurableBase U hS).degree hS hN)))}
      (V.hermitianHNPolygon hS hN hV x) :=
  ⟨V.hermitianHNPolygon_graph_mem_convexHull_degreePoints hS hN hV x hx,
    fun _ hy ↦ (V.convexHull_degreePoints_subset_hermitianHNPolygon_hypograph
      hS hN hV hy).2⟩

/-- Away from actual internal HN ranks, the actual polygon agrees with
an affine function on an open neighbourhood inside its domain. -/
theorem hermitianHNPolygon_locally_affine_of_not_internal_rank (x : ℝ)
    (hx : x ∈ Set.Ioo 0 (Module.finrank K E : ℝ))
    (hnot : ∀ m : ℕ, 0 < m → m < V.hermitianHNLength hS hN hV →
      x ≠ (Module.finrank K (V.hermitianHNTerm hS hN hV m) : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ c b : ℝ, ∀ y ∈ Set.Ioo (x - ε) (x + ε),
      V.hermitianHNPolygon hS hN hV y = c + y * b := by
  have hr : 0 < Module.finrank K E := by exact_mod_cast (lt_trans hx.1 hx.2)
  obtain ⟨i, hi⟩ := V.exists_hermitianHNFactor_real_rank_interval hS hN hV hr x
    ⟨hx.1.le, hx.2.le⟩
  let r : ℝ := Module.finrank K (V.hermitianHNTerm hS hN hV i.val)
  let s : ℝ := Module.finrank K (V.hermitianHNTerm hS hN hV (i.val + 1))
  have hzRank : (Module.finrank K (V.hermitianHNTerm hS hN hV 0) : ℝ) = 0 := by
    have h := congrArg (fun U : Submodule K E ↦ (Module.finrank K U : ℝ))
      (V.hermitianHNTerm_zero hS hN hV)
    exact h.trans (by exact_mod_cast (finrank_bot K E))
  have hnRank :
      (Module.finrank K (V.hermitianHNTerm hS hN hV
        (V.hermitianHNLength hS hN hV)) : ℝ) = (Module.finrank K E : ℝ) := by
    have h := congrArg (fun U : Submodule K E ↦ (Module.finrank K U : ℝ))
      (V.hermitianHNTerm_length_eq_top hS hN hV)
    exact h.trans (by exact_mod_cast (finrank_top K E))
  have hl : r < x := by
    apply lt_of_le_of_ne hi.1
    intro he
    by_cases hiz : i.val = 0
    · have hri : r = 0 := (congrArg (fun m : ℕ ↦
          (Module.finrank K (V.hermitianHNTerm hS hN hV m) : ℝ)) hiz).trans hzRank
      have hx0 := he.symm.trans hri
      linarith [hx.1]
    · exact hnot i.val (Nat.pos_of_ne_zero hiz) i.isLt he.symm
  have hu : x < s := by
    apply lt_of_le_of_ne hi.2
    intro he
    by_cases hie : i.val + 1 = V.hermitianHNLength hS hN hV
    · have hsi : s = (Module.finrank K E : ℝ) :=
        (congrArg (fun m : ℕ ↦
          (Module.finrank K (V.hermitianHNTerm hS hN hV m) : ℝ)) hie).trans hnRank
      have hxe := he.trans hsi
      linarith [hx.2]
    · exact hnot (i.val + 1) (Nat.succ_pos _)
        (lt_of_le_of_ne (Nat.succ_le_of_lt i.isLt) hie) he
  let ε := min (x - r) (s - x)
  have he : 0 < ε := lt_min (sub_pos.mpr hl) (sub_pos.mpr hu)
  refine ⟨ε, he,
    (V.restrictOfMeasurableBase (V.hermitianHNTerm hS hN hV i.val) hS).degree hS hN -
      r * (V.hermitianHNFactor hS hN hV i).slope hS hN,
    (V.hermitianHNFactor hS hN hV i).slope hS hN, ?_⟩
  intro y hy
  have hyr : r ≤ y := by
    have h := min_le_left (x - r) (s - x)
    change ε ≤ x - r at h
    linarith [hy.1]
  have hys : y ≤ s := by
    have h := min_le_right (x - r) (s - x)
    change ε ≤ s - x at h
    linarith [hy.2]
  rw [V.hermitianHNPolygon_affine_factor hS hN hV i y ⟨hyr, hys⟩]
  change _ = _ - r * _ + y * _
  ring

/-- An actual internal HN flag rank is a genuine local slope break:
no affine function agrees with the polygon on an open neighbourhood. -/
theorem hermitianHNPolygon_not_locally_affine_at_internal_rank
    (m : ℕ) (hm : 0 < m) (hmn : m < V.hermitianHNLength hS hN hV) :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∃ c b : ℝ,
      ∀ y ∈ Set.Ioo
        ((Module.finrank K (V.hermitianHNTerm hS hN hV m) : ℝ) - ε)
        ((Module.finrank K (V.hermitianHNTerm hS hN hV m) : ℝ) + ε),
        V.hermitianHNPolygon hS hN hV y = c + y * b := by
  rintro ⟨ε, he, c, b, ha⟩
  let i : Fin (V.hermitianHNLength hS hN hV) := ⟨m - 1, by omega⟩
  let j : Fin (V.hermitianHNLength hS hN hV) := ⟨m, hmn⟩
  let l : ℝ := Module.finrank K (V.hermitianHNTerm hS hN hV (m - 1))
  let x : ℝ := Module.finrank K (V.hermitianHNTerm hS hN hV m)
  let r : ℝ := Module.finrank K (V.hermitianHNTerm hS hN hV (m + 1))
  have hli : l < x := Nat.cast_lt.mpr
    (Submodule.finrank_lt_finrank_of_lt (V.hermitianHNTerm_lt hS hN hV
      (m - 1) m (by omega) hmn.le))
  have hjr : x < r := Nat.cast_lt.mpr
    (Submodule.finrank_lt_finrank_of_lt (V.hermitianHNTerm_lt hS hN hV
      m (m + 1) (Nat.lt_succ_self _) (Nat.succ_le_of_lt hmn)))
  have hxend :
      (Module.finrank K (V.hermitianHNTerm hS hN hV (i.val + 1)) : ℝ) = x :=
    congrArg (fun k : ℕ ↦ (Module.finrank K (V.hermitianHNTerm hS hN hV k) : ℝ))
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
  have hLx := V.hermitianHNPolygon_affine_factor hS hN hV i x
    ⟨hli.le, le_of_eq hxend.symm⟩
  have hLm := V.hermitianHNPolygon_affine_factor hS hN hV i (x - δ)
    ⟨by change l ≤ x - δ; linarith,
      by rw [hxend]; linarith⟩
  have hRx := V.hermitianHNPolygon_affine_factor hS hN hV j x
    ⟨le_rfl, hjr.le⟩
  have hRp := V.hermitianHNPolygon_affine_factor hS hN hV j (x + δ)
    ⟨by change x ≤ x + δ; linarith,
      by change x + δ ≤ r; linarith⟩
  have hdL : V.hermitianHNPolygon hS hN hV x -
      V.hermitianHNPolygon hS hN hV (x - δ) =
        δ * (V.hermitianHNFactor hS hN hV i).slope hS hN := by
    rw [hLx, hLm]
    ring
  have hdR : V.hermitianHNPolygon hS hN hV (x + δ) -
      V.hermitianHNPolygon hS hN hV x =
        δ * (V.hermitianHNFactor hS hN hV j).slope hS hN := by
    rw [hRp, hRx]
    ring
  have hax := ha x ⟨by change x - ε < x; linarith, by change x < x + ε; linarith⟩
  have ham := ha (x - δ)
    ⟨by change x - ε < x - δ; linarith, by change x - δ < x + ε; linarith⟩
  have hap := ha (x + δ)
    ⟨by change x - ε < x + δ; linarith, by change x + δ < x + ε; linarith⟩
  rw [hax, ham] at hdL
  rw [hap, hax] at hdR
  have hstrict := V.hermitianHNFactor_slope_strictAnti hS hN hV
    (show i < j by change m - 1 < m; omega)
  nlinarith

/-- The literal local-affinity criterion detects exactly the actual
internal HN flag ranks, within the genuine open rank domain. -/
theorem hermitianHNPolygon_not_locally_affine_iff_internal_rank (x : ℝ)
    (hx : x ∈ Set.Ioo 0 (Module.finrank K E : ℝ)) :
    (¬ ∃ ε : ℝ, 0 < ε ∧ ∃ c b : ℝ,
      ∀ y ∈ Set.Ioo (x - ε) (x + ε),
        V.hermitianHNPolygon hS hN hV y = c + y * b) ↔
      ∃ m : ℕ, 0 < m ∧ m < V.hermitianHNLength hS hN hV ∧
        x = (Module.finrank K (V.hermitianHNTerm hS hN hV m) : ℝ) := by
  constructor
  · intro h
    by_contra hn
    have hnot : ∀ m : ℕ, 0 < m → m < V.hermitianHNLength hS hN hV →
        x ≠ (Module.finrank K (V.hermitianHNTerm hS hN hV m) : ℝ) := by
      intro m hm hmn he
      exact hn ⟨m, hm, hmn, he⟩
    exact h (V.hermitianHNPolygon_locally_affine_of_not_internal_rank hS hN hV x hx hnot)
  · rintro ⟨m, hm, hmn, rfl⟩
    exact V.hermitianHNPolygon_not_locally_affine_at_internal_rank hS hN hV m hm hmn

end
end ArakelovGeometry.AdelicVectorBundle
