/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.Basic
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Basic

import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.OrderedDegree
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.PositiveDegree
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.SemistableFlagDegree
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# The polygon from actual Hermitian HN factors

Actual semistable-factor rank increments bound every actual subspace
degree by every supporting affine line. Their finite lower envelope
is the concave HN polygon; its later vertex and convex-hull consumers
use the actual constructed flag.
-/

@[expose] public section

open scoped BigOperators

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Every actual subspace degree lies below every affine line supplied by
the actual ranks and means of a complete semistable flag. -/
theorem degree_restrict_le_supportLine_of_semistableFlag
    (V : AdelicVectorBundle S) {n : ℕ} (F : Fin (n + 1) → Submodule K V)
    (hF : Monotone F) (hzero : F 0 = ⊥) (htop : F (Fin.last n) = ⊤)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian]
    [hsemi : ∀ i, (V.flagQuotientOfNormMeasurability F i).IsMeanSlopeSemistable]
    (U : Submodule K V) (t : ℝ) :
    (V.restrictOfNormMeasurability U).degree ≤
      (Module.finrank K U : ℝ) * t + ∑ i : Fin n,
        (Module.finrank K ((F i.succ) ⧸ ((F i.castSucc).comap (F i.succ).subtype)) : ℝ) *
          max ((V.flagQuotientOfNormMeasurability F i).slope - t) 0 := by
  let k : Fin n → ℝ := fun i ↦
    (Module.finrank K (U ⊓ F i.succ : Submodule K V) -
      Module.finrank K (U ⊓ F i.castSucc : Submodule K V) : ℕ)
  have hk : (∑ i, k i) = (Module.finrank K U : ℝ) := by
    dsimp only [k]
    exact_mod_cast sum_intersection_rank_increment_eq F hF hzero htop U
  apply (V.degree_restrict_le_sum_intersection_rank_mul_slope_of_semistableFlag
    F hF hzero htop U).trans
  calc
    _ = (Module.finrank K U : ℝ) * t + ∑ i : Fin n,
        k i * ((V.flagQuotientOfNormMeasurability F i).slope - t) := by
      rw [← hk, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change k i * _ = _
      ring
    _ ≤ _ := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro i _
      have hk0 : 0 ≤ k i := Nat.cast_nonneg _
      have hkd : k i ≤ (Module.finrank K
          ((F i.succ) ⧸ ((F i.castSucc).comap (F i.succ).subtype)) : ℝ) := by
        dsimp only [k]
        exact_mod_cast intersection_rank_increment_le F hF U i
      exact (mul_le_mul_of_nonneg_left (le_max_left _ _) hk0).trans
        (mul_le_mul_of_nonneg_right hkd (le_max_right _ _))

variable (V : AdelicVectorBundle S)
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]
  [hV : V.toNormFamily.IsHermitian]

/-- The supporting affine line at a real threshold, formed from the actual
constructed Hermitian HN factor ranks and means. -/
def hermitianHNSupportLine (t x : ℝ) : ℝ :=
  x * t + ∑ i : Fin (V.hermitianHNLength),
    (Module.finrank K ((V.hermitianHNTerm (i.val + 1)).map
      (V.hermitianHNTerm i.val).mkQ) : ℝ) *
        max ((V.hermitianHNFactor i).slope - t) 0

/-- Every actual rational subspace lies below each actual HN supporting line. -/
theorem degree_restrict_le_hermitianHNSupportLine (U : Submodule K V) (t : ℝ) :
    (V.restrictOfNormMeasurability U).degree ≤
      V.hermitianHNSupportLine t (Module.finrank K U) := by
  simpa only [hermitianHNSupportLine, V.finrank_hermitianHNFlagQuotient_eq,
    V.slope_hermitianHNFlagQuotient_eq] using
      V.degree_restrict_le_supportLine_of_semistableFlag
        (V.hermitianHNFlag) (V.hermitianHNFlag_strictMono).monotone
        (V.hermitianHNFlag_zero) (V.hermitianHNFlag_last)
        (hsemi := (V.isMeanSlopeSemistable_hermitianHNFlagQuotient)) U t

/-- The finite lower envelope of the actual HN supporting lines. In rank zero
the actual flag is empty and this function is zero. -/
def hermitianHNPolygon (x : ℝ) : ℝ :=
  if h : 0 < V.hermitianHNLength then
    (Finset.univ : Finset (Fin (V.hermitianHNLength))).inf'
      ⟨⟨0, h⟩, Finset.mem_univ _⟩
      (fun i ↦ V.hermitianHNSupportLine
        ((V.hermitianHNFactor i).slope) x)
  else 0

/-- The actual envelope is below each actual supporting line at a factor mean. -/
theorem hermitianHNPolygon_le_supportLine
    (i : Fin (V.hermitianHNLength)) (x : ℝ) :
    V.hermitianHNPolygon x ≤ V.hermitianHNSupportLine
      ((V.hermitianHNFactor i).slope) x := by
  have hp : 0 < V.hermitianHNLength :=
    (Nat.zero_le i.val).trans_lt i.isLt
  simp only [hermitianHNPolygon, dite_eq_left hp]
  exact Finset.inf'_le _ (Finset.mem_univ i)

/-- Every actual subspace degree is bounded by the actual finite envelope. -/
theorem degree_restrict_le_hermitianHNPolygon (U : Submodule K V) :
    (V.restrictOfNormMeasurability U).degree ≤
      V.hermitianHNPolygon (Module.finrank K U) := by
  classical
  by_cases hp : 0 < V.hermitianHNLength
  · simp only [hermitianHNPolygon, dite_eq_left hp]
    apply Finset.le_inf'
    intro i _
    exact V.degree_restrict_le_hermitianHNSupportLine U _
  · simp only [hermitianHNPolygon, dite_eq_right hp]
    have hb := V.degree_restrict_le_hermitianHNSupportLine U 0
    have hs : (∑ i : Fin (V.hermitianHNLength),
        (Module.finrank K ((V.hermitianHNTerm (i.val + 1)).map
          (V.hermitianHNTerm i.val).mkQ) : ℝ) *
            max ((V.hermitianHNFactor i).slope - 0) 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact False.elim (hp ((Nat.zero_le i.val).trans_lt i.isLt))
    simpa only [hermitianHNSupportLine, mul_zero, hs, zero_add] using hb

/-- The actual supporting-line envelope is concave, with its empty case explicit. -/
theorem concaveOn_hermitianHNPolygon :
    ConcaveOn ℝ Set.univ (V.hermitianHNPolygon) := by
  classical
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  by_cases hp : 0 < V.hermitianHNLength
  · simp only [hermitianHNPolygon, dite_eq_left hp]
    apply Finset.le_inf'
    intro i _
    have hx := V.hermitianHNPolygon_le_supportLine i x
    have hy := V.hermitianHNPolygon_le_supportLine i y
    simp only [hermitianHNPolygon, dite_eq_left hp] at hx hy
    apply (add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb)).trans_eq
    let β := (V.hermitianHNFactor i).slope
    let c := ∑ j : Fin (V.hermitianHNLength),
      (Module.finrank K ((V.hermitianHNTerm (j.val + 1)).map
        (V.hermitianHNTerm j.val).mkQ) : ℝ) *
          max ((V.hermitianHNFactor j).slope - β) 0
    change a * (x * β + c) + b * (y * β + c) = (a * x + b * y) * β + c
    calc
      _ = (a * x + b * y) * β + (a + b) * c := by ring
      _ = _ := by rw [hab, one_mul]
  · simp only [hermitianHNPolygon, dite_eq_right hp, mul_zero, zero_add, le_refl]

private theorem sum_fin_prefix_eq_sum_filter {n m : ℕ} (hm : m ≤ n) (f : Fin n → ℝ) :
    (∑ j : Fin m, f ⟨j.val, Nat.lt_of_lt_of_le j.isLt hm⟩) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < m), f j := by
  classical
  apply Finset.sum_bij (fun j _ ↦ (⟨j.val, Nat.lt_of_lt_of_le j.isLt hm⟩ : Fin n))
  · intro j _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩
  · intro j _ k _ hjk
    exact Fin.ext (congrArg (fun i : Fin n ↦ i.val) hjk)
  · intro j hj
    refine ⟨⟨j.val, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, rfl⟩
  · intro j _
    rfl

/-- Actual factor ranks telescope to each actual HN prefix rank. -/
theorem sum_hermitianHNFactor_finrank_prefix (m : ℕ)
    (hm : m ≤ V.hermitianHNLength) :
    (∑ i : Fin m,
      Module.finrank K ((V.hermitianHNTerm (i.val + 1)).map
        (V.hermitianHNTerm i.val).mkQ)) =
      Module.finrank K (V.hermitianHNTerm m) := by
  induction m with
  | zero =>
      rw [Fin.sum_univ_zero, V.hermitianHNTerm_zero, finrank_bot]
  | succ m ih =>
      have hm' : m ≤ V.hermitianHNLength := by omega
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih hm']
      have hq := V.finrank_hermitianHNFactor_eq_sub ⟨m, by omega⟩
      have hr := Submodule.finrank_mono
        (V.hermitianHNTerm_monotone (Nat.le_succ m))
      change Module.finrank K (V.hermitianHNTerm m) +
        Module.finrank K ((V.hermitianHNTerm (m + 1)).map
          (V.hermitianHNTerm m).mkQ) =
            Module.finrank K (V.hermitianHNTerm (m + 1))
      change Module.finrank K ((V.hermitianHNTerm (m + 1)).map
        (V.hermitianHNTerm m).mkQ) =
          Module.finrank K (V.hermitianHNTerm (m + 1)) -
            Module.finrank K (V.hermitianHNTerm m) at hq
      change Module.finrank K (V.hermitianHNTerm m) ≤
        Module.finrank K (V.hermitianHNTerm (m + 1)) at hr
      omega

/-- At an actual factor mean, the supporting line has the actual preceding
flag degree as its value at the preceding flag rank. -/
theorem hermitianHNSupportLine_factor_slope
    (i : Fin (V.hermitianHNLength)) (x : ℝ) :
    V.hermitianHNSupportLine
      ((V.hermitianHNFactor i).slope) x =
        (V.restrictOfNormMeasurability (V.hermitianHNTerm i.val)).degree +
          (x - (Module.finrank K (V.hermitianHNTerm i.val) : ℝ)) *
            (V.hermitianHNFactor i).slope := by
  classical
  let d : Fin (V.hermitianHNLength) → ℝ := fun j ↦
    Module.finrank K ((V.hermitianHNTerm (j.val + 1)).map
      (V.hermitianHNTerm j.val).mkQ)
  let β := fun j : Fin (V.hermitianHNLength) ↦
    (V.hermitianHNFactor j).slope
  have hi : i.val ≤ V.hermitianHNLength := i.isLt.le
  have hd : (∑ j : Fin i.val, d ⟨j.val, Nat.lt_of_lt_of_le j.isLt hi⟩) =
      (Module.finrank K (V.hermitianHNTerm i.val) : ℝ) := by
    dsimp only [d]
    exact_mod_cast V.sum_hermitianHNFactor_finrank_prefix i.val hi
  have hD : (∑ j : Fin i.val, d ⟨j.val, Nat.lt_of_lt_of_le j.isLt hi⟩ *
      β ⟨j.val, Nat.lt_of_lt_of_le j.isLt hi⟩) =
        (V.restrictOfNormMeasurability (V.hermitianHNTerm i.val)).degree := by
    simpa only [d, β, degree_eq_rank_mul_slope] using
      V.sum_hermitianHNFactor_degree_prefix i.val hi
  have hs : (∑ j : Fin (V.hermitianHNLength), d j * max (β j - β i) 0) =
      ∑ j : Fin i.val, d ⟨j.val, Nat.lt_of_lt_of_le j.isLt hi⟩ *
        (β ⟨j.val, Nat.lt_of_lt_of_le j.isLt hi⟩ - β i) := by
    rw [sum_fin_prefix_eq_sum_filter hi (fun j ↦ d j * (β j - β i))]
    calc
      _ = ∑ j ∈ Finset.univ.filter (fun j : Fin (V.hermitianHNLength) ↦
          j.val < i.val), d j * max (β j - β i) 0 := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j hj hnj
        have hij : i ≤ j := by
          change i.val ≤ j.val
          exact Nat.le_of_not_lt (fun h ↦ hnj (Finset.mem_filter.mpr ⟨hj, h⟩))
        have hb : β j ≤ β i := (V.hermitianHNFactor_slope_strictAnti).antitone hij
        rw [max_eq_right (sub_nonpos.mpr hb), mul_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        have hji : j < i := (Finset.mem_filter.mp hj).2
        have hb : β i ≤ β j := (V.hermitianHNFactor_slope_strictAnti hji).le
        rw [max_eq_left (sub_nonneg.mpr hb)]
  change x * β i + ∑ j, d j * max (β j - β i) 0 = _
  rw [hs]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hD, hd]
  ring

/-- The actual polygon takes the preceding actual flag degree at each factor's
preceding rank, rather than at a supplied numerical vertex. -/
theorem hermitianHNPolygon_rank_factor_start
    (i : Fin (V.hermitianHNLength)) :
    V.hermitianHNPolygon (Module.finrank K (V.hermitianHNTerm i.val)) =
      (V.restrictOfNormMeasurability (V.hermitianHNTerm i.val)).degree := by
  apply le_antisymm
  · apply (V.hermitianHNPolygon_le_supportLine i _).trans_eq
    rw [V.hermitianHNSupportLine_factor_slope]
    simp only [sub_self, zero_mul, add_zero]
  · exact V.degree_restrict_le_hermitianHNPolygon _

/-- The same actual supporting line supplies the other endpoint's actual
degree, using the checked Hermitian degree step and actual rank-nullity. -/
theorem hermitianHNPolygon_rank_factor_end
    (i : Fin (V.hermitianHNLength)) :
    V.hermitianHNPolygon
        (Module.finrank K (V.hermitianHNTerm (i.val + 1))) =
      (V.restrictOfNormMeasurability (V.hermitianHNTerm (i.val + 1))).degree
        := by
  apply le_antisymm
  · apply (V.hermitianHNPolygon_le_supportLine i _).trans_eq
    rw [V.hermitianHNSupportLine_factor_slope]
    have hm := Submodule.finrank_mono
      (V.hermitianHNTerm_monotone (Nat.le_succ i.val))
    have hr : (Module.finrank K (V.hermitianHNTerm (i.val + 1)) : ℝ) -
        (Module.finrank K (V.hermitianHNTerm i.val) : ℝ) =
          (Module.finrank K ((V.hermitianHNTerm (i.val + 1)).map
            (V.hermitianHNTerm i.val).mkQ) : ℝ) := by
      rw [V.finrank_hermitianHNFactor_eq_sub i]
      exact (Nat.cast_sub hm).symm
    rw [hr]
    have hd := V.degree_restrict_hermitianHNTerm_succ i
    rw [(V.hermitianHNFactor i).degree_eq_rank_mul_slope] at hd
    exact hd
  · exact V.degree_restrict_le_hermitianHNPolygon _

/-- Every actual HN flag vertex has its actual degree, including both
endpoints and the sole vertex of the empty zero-dimensional flag. -/
theorem hermitianHNPolygon_rank_term (m : ℕ)
    (hm : m ≤ V.hermitianHNLength) :
    V.hermitianHNPolygon (Module.finrank K (V.hermitianHNTerm m)) =
      (V.restrictOfNormMeasurability (V.hermitianHNTerm m)).degree := by
  by_cases hp : 0 < V.hermitianHNLength
  · by_cases hlt : m < V.hermitianHNLength
    · exact V.hermitianHNPolygon_rank_factor_start ⟨m, hlt⟩
    · have hm0 : 0 < m := by omega
      let i : Fin (V.hermitianHNLength) := ⟨m - 1, by omega⟩
      have hi : i.val + 1 = m := by dsimp only [i]; omega
      have hv := V.hermitianHNPolygon_rank_factor_end i
      have ht := congrArg (fun k : ℕ ↦
        V.hermitianHNPolygon (Module.finrank K (V.hermitianHNTerm k)) =
          (V.restrictOfNormMeasurability (V.hermitianHNTerm k)).degree) hi
      exact Eq.mp ht hv
  · have hm0 : m = 0 := by omega
    subst m
    rw [V.hermitianHNTerm_zero, finrank_bot]
    simp only [hermitianHNPolygon, dite_eq_right hp]
    exact (degree_eq_zero_of_finrank_eq_zero _ (finrank_bot K V)).symm

/-- The actual factor supporting line has the following actual flag degree
at the following actual flag rank. -/
theorem hermitianHNSupportLine_rank_factor_end
    (i : Fin (V.hermitianHNLength)) :
    V.hermitianHNSupportLine
        ((V.hermitianHNFactor i).slope)
        (Module.finrank K (V.hermitianHNTerm (i.val + 1))) =
      (V.restrictOfNormMeasurability (V.hermitianHNTerm (i.val + 1))).degree
        := by
  rw [V.hermitianHNSupportLine_factor_slope]
  have hm := Submodule.finrank_mono
    (V.hermitianHNTerm_monotone (Nat.le_succ i.val))
  have hr : (Module.finrank K (V.hermitianHNTerm (i.val + 1)) : ℝ) -
      (Module.finrank K (V.hermitianHNTerm i.val) : ℝ) =
        (Module.finrank K ((V.hermitianHNTerm (i.val + 1)).map
          (V.hermitianHNTerm i.val).mkQ) : ℝ) := by
    rw [V.finrank_hermitianHNFactor_eq_sub i]
    exact (Nat.cast_sub hm).symm
  rw [hr]
  have hd := V.degree_restrict_hermitianHNTerm_succ i
  rw [(V.hermitianHNFactor i).degree_eq_rank_mul_slope] at hd
  exact hd

/-- On every complete actual factor rank interval, the polygon is affine
with that actual factor's mean slope. -/
theorem hermitianHNPolygon_affine_factor
    (i : Fin (V.hermitianHNLength)) (x : ℝ)
    (hx : x ∈ Set.Icc
      (Module.finrank K (V.hermitianHNTerm i.val) : ℝ)
      (Module.finrank K (V.hermitianHNTerm (i.val + 1)) : ℝ)) :
    V.hermitianHNPolygon x =
      (V.restrictOfNormMeasurability (V.hermitianHNTerm i.val)).degree +
        (x - (Module.finrank K (V.hermitianHNTerm i.val) : ℝ)) *
          (V.hermitianHNFactor i).slope := by
  let r : ℝ := Module.finrank K (V.hermitianHNTerm i.val)
  let s : ℝ := Module.finrank K (V.hermitianHNTerm (i.val + 1))
  let D := (V.restrictOfNormMeasurability (V.hermitianHNTerm i.val)).degree
  let D' := (V.restrictOfNormMeasurability (V.hermitianHNTerm (i.val + 1))).degree
  let β := (V.hermitianHNFactor i).slope
  have hr : r < s := Nat.cast_lt.mpr
    (Submodule.finrank_lt_finrank_of_lt (V.hermitianHNTerm_lt i.val (i.val + 1)
      (Nat.lt_succ_self _) (Nat.succ_le_of_lt i.isLt)))
  have hd : 0 < s - r := sub_pos.mpr hr
  let a := (s - x) / (s - r)
  let b := (x - r) / (s - r)
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hx.2) hd.le
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hx.1) hd.le
  have hab : a + b = 1 := by
    change (s - x) / (s - r) + (x - r) / (s - r) = 1
    rw [← add_div]
    have hn : (s - x) + (x - r) = s - r := by ring
    rw [hn, div_self hd.ne']
  have hc : a * r + b * s = x := by
    change (s - x) / (s - r) * r + (x - r) / (s - r) * s = x
    field_simp [hd.ne']
    ring
  have hD : D' = D + (s - r) * β := by
    exact (V.hermitianHNSupportLine_rank_factor_end i).symm.trans
      (V.hermitianHNSupportLine_factor_slope i s)
  have hpr : V.hermitianHNPolygon r = D :=
    V.hermitianHNPolygon_rank_factor_start i
  have hps : V.hermitianHNPolygon s = D' :=
    V.hermitianHNPolygon_rank_factor_end i
  have hlow := (V.concaveOn_hermitianHNPolygon).2
    (Set.mem_univ r) (Set.mem_univ s) ha hb hab
  simp only [smul_eq_mul, hpr, hps, hc] at hlow
  have haf : a * D + b * D' = D + (x - r) * β := by
    rw [hD]
    calc
      _ = (a + b) * D + (a * r + b * s - (a + b) * r) * β := by ring
      _ = _ := by rw [hab, hc, one_mul, one_mul]
  change V.hermitianHNPolygon x = D + (x - r) * β
  apply le_antisymm
  · exact (V.hermitianHNPolygon_le_supportLine i x).trans_eq
      (V.hermitianHNSupportLine_factor_slope i x)
  · rwa [haf] at hlow

end

end ArakelovGeometry.AdelicVectorBundle
