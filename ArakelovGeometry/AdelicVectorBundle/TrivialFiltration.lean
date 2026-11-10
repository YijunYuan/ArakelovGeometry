/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.TrivialPlace
public import ArakelovGeometry.LinearAlgebra.FiniteFiltration
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Literal ball filtrations of actual trivial-place norms

The input is the actual norm family, with its ultrametric hypothesis.
Finite image and left local constancy are derived from dimension, not
assumed as filtration certificates.
-/

@[expose] public section

namespace ArakelovGeometry.NormFamily

noncomputable section

open AdelicStructure

universe u w

variable {K : Type u} [Field K] {E : Type w} [AddCommGroup E] [Module K E]
  (ξ : NormFamily (singleTrivialPlace K) E) (hξ : ξ.IsUltrametric)

open Classical in
/-- The literal closed ball of the extracted actual norm, as a rational
submodule. Every completed norm remains the canonical original family. -/
def trivialFiltration (t : ℝ) : Submodule K E where
  carrier := {x | ξ.trivialSeminorm x ≤ Real.exp (-t)}
  zero_mem' := by
    change ξ.trivialSeminorm 0 ≤ Real.exp (-t)
    rw [map_zero]
    exact (Real.exp_pos _).le
  add_mem' := by
    intro x y hx hy
    have hu : (ofTrivialNorm ξ.trivialSeminorm ξ.trivialSeminorm_eq_zero_iff).IsUltrametric := by
      rw [ξ.ofTrivialNorm_trivialSeminorm]
      exact hξ
    exact ((ofTrivialNorm_isUltrametric_iff _ _).mp hu x y).trans (max_le hx hy)
  smul_mem' := by
    intro a x hx
    change ξ.trivialSeminorm
      (WithAbs.toAbs (AbsoluteValue.trivial : AbsoluteValue K ℝ) a • x) ≤ _
    rw [map_smul_eq_mul, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_toAbs]
    by_cases ha : a = 0
    · rw [ha, map_zero, zero_mul]
      exact (Real.exp_pos _).le
    · rw [AbsoluteValue.trivial_apply ha, one_mul]
      exact hx

open Classical in
@[simp]
theorem mem_trivialFiltration (t : ℝ) (x : E) :
    x ∈ ξ.trivialFiltration hξ t ↔ ξ.trivialSeminorm x ≤ Real.exp (-t) := Iff.rfl

open Classical in
/-- Each nonzero vector has the literal included logarithmic cut. -/
theorem mem_trivialFiltration_iff_le_neg_log (t : ℝ) (x : E) (hx : x ≠ 0) :
    x ∈ ξ.trivialFiltration hξ t ↔ t ≤ -Real.log (ξ.trivialSeminorm x) := by
  have hp : 0 < ξ.trivialSeminorm x := by
    rw [trivialSeminorm_apply]
    exact ξ.norm_rational_pos PUnit.unit hx
  rw [mem_trivialFiltration]
  conv_lhs => rw [← Real.exp_log hp]
  rw [Real.exp_le_exp]
  constructor <;> intro he <;> linarith

/-- Actual balls decrease with their real threshold. -/
theorem antitone_trivialFiltration : Antitone (ξ.trivialFiltration hξ) := by
  intro s t hst x hx
  exact hx.trans (Real.exp_le_exp.mpr (neg_le_neg hst))

variable [FiniteDimensional K E]

/-- The actual ball filtration has finite image by the finite-dimensional
subspace chain theorem. -/
theorem finite_range_trivialFiltration : (Set.range (ξ.trivialFiltration hξ)).Finite := by
  have h := (ξ.antitone_trivialFiltration hξ).isChain_range.lt_of_le
  exact h.finite_of_wellFoundedLT_of_wellFoundedGT

include hξ

open Classical in
/-- Actual norm values are finite: attained positive radii inject into
the finite chain of literal balls. -/
theorem finite_range_trivialSeminorm : (Set.range ξ.trivialSeminorm).Finite := by
  let A : Set ℝ := {r | ∃ x, ξ.trivialSeminorm x = r ∧ r ≠ 0}
  let g : ℝ → Submodule K E := fun r ↦ ξ.trivialFiltration hξ (-Real.log r)
  have hp : ∀ r ∈ A, 0 < r := by
    rintro r ⟨x, hx, hr⟩
    exact lt_of_le_of_ne (hx ▸ apply_nonneg ξ.trivialSeminorm x) (Ne.symm hr)
  have hg : Set.InjOn g A := by
    intro r hr s hs he
    have hrp := hp r hr
    have hsp := hp s hs
    obtain ⟨x, hxr, _⟩ := hr
    obtain ⟨y, hys, _⟩ := hs
    have hx : x ∈ g r := by
      change ξ.trivialSeminorm x ≤ Real.exp (-(-Real.log r))
      rw [neg_neg, Real.exp_log hrp, hxr]
    have hy : y ∈ g s := by
      change ξ.trivialSeminorm y ≤ Real.exp (-(-Real.log s))
      rw [neg_neg, Real.exp_log hsp, hys]
    have hxs : x ∈ g s := he ▸ hx
    have hyr : y ∈ g r := he.symm ▸ hy
    change ξ.trivialSeminorm x ≤ Real.exp (-(-Real.log s)) at hxs
    change ξ.trivialSeminorm y ≤ Real.exp (-(-Real.log r)) at hyr
    rw [neg_neg, Real.exp_log hsp, hxr] at hxs
    rw [neg_neg, Real.exp_log hrp, hys] at hyr
    exact le_antisymm hxs hyr
  have hA : A.Finite := Set.Finite.of_finite_image
    ((ξ.finite_range_trivialFiltration hξ).subset (by
      rintro _ ⟨r, _, rfl⟩
      exact ⟨-Real.log r, rfl⟩)) hg
  apply (hA.insert 0).subset
  rintro r ⟨x, rfl⟩
  by_cases hx : ξ.trivialSeminorm x = 0
  · exact Set.mem_insert_iff.mpr (Or.inl hx)
  · exact Set.mem_insert_iff.mpr (Or.inr ⟨x, rfl, hx⟩)

open Classical in
/-- Separation and exhaustion are actual attained zero and whole-space
balls, including the zero space. -/
theorem trivialFiltration_attains_bot_top :
    (∃ t, ξ.trivialFiltration hξ t = ⊥) ∧
      (∃ t, ξ.trivialFiltration hξ t = ⊤) := by
  let J : Set ℝ := (fun r ↦ -Real.log r) '' Set.range ξ.trivialSeminorm
  have hJ : J.Finite := (ξ.finite_range_trivialSeminorm hξ).image _
  obtain ⟨a, ha⟩ := hJ.bddAbove
  obtain ⟨b, hb⟩ := hJ.bddBelow
  constructor
  · refine ⟨a + 1, le_antisymm ?_ bot_le⟩
    intro x hx
    by_contra hn
    have ht := (ξ.mem_trivialFiltration_iff_le_neg_log hξ _ x hn).mp hx
    have hle := ha (show -Real.log (ξ.trivialSeminorm x) ∈ J from
      ⟨_, ⟨x, rfl⟩, rfl⟩)
    linarith
  · refine ⟨b - 1, top_unique ?_⟩
    intro x _
    by_cases hx : x = 0
    · exact hx ▸ (ξ.trivialFiltration hξ _).zero_mem
    apply (ξ.mem_trivialFiltration_iff_le_neg_log hξ _ x hx).mpr
    have hle := hb (show -Real.log (ξ.trivialSeminorm x) ∈ J from
      ⟨_, ⟨x, rfl⟩, rfl⟩)
    linarith

open Classical in
/-- Each threshold includes its endpoint and has a genuinely constant
left interval, produced from the finite set of attained norm values. -/
theorem trivialFiltration_locallyConstant_left (t : ℝ) :
    ∃ ε > 0, ∀ s, t - ε < s → s ≤ t →
      ξ.trivialFiltration hξ s = ξ.trivialFiltration hξ t := by
  let J : Set ℝ := (fun r ↦ -Real.log r) '' Set.range ξ.trivialSeminorm
  let A : Set ℝ := J ∩ Set.Iio t
  have hA : A.Finite := ((ξ.finite_range_trivialSeminorm hξ).image _).subset
    Set.inter_subset_left
  have hgap : ∃ ε > 0, ∀ r ∈ J, r < t → r ≤ t - ε := by
    by_cases hn : A.Nonempty
    · have hm : sSup A ∈ A := hn.csSup_mem hA
      refine ⟨t - sSup A, sub_pos.mpr hm.2, ?_⟩
      intro r hr hrt
      have hl := le_csSup hA.bddAbove (show r ∈ A from ⟨hr, hrt⟩)
      linarith
    · refine ⟨1, zero_lt_one, ?_⟩
      intro r hr hrt
      exact (hn ⟨r, hr, hrt⟩).elim
  obtain ⟨ε, hε, hgap⟩ := hgap
  refine ⟨ε, hε, fun s hs hst ↦ le_antisymm ?_ (ξ.antitone_trivialFiltration hξ hst)⟩
  intro x hx
  by_cases hn : x = 0
  · exact hn ▸ (ξ.trivialFiltration hξ t).zero_mem
  apply (ξ.mem_trivialFiltration_iff_le_neg_log hξ t x hn).mpr
  have hcut := (ξ.mem_trivialFiltration_iff_le_neg_log hξ s x hn).mp hx
  by_contra hc
  have hlt : -Real.log (ξ.trivialSeminorm x) < t := lt_of_not_ge hc
  have hl := hgap _ ⟨_, ⟨x, rfl⟩, rfl⟩ hlt
  linarith

/-- The actual literal balls produce their strict full flag, real jumps,
included endpoints and true right-limit union. No finite flag is input. -/
theorem exists_strictMono_flag_and_jumps_trivialFiltration :
    ∃ (n : ℕ) (U : Fin (n + 1) → Submodule K E) (b : Fin n → ℝ),
      StrictMono U ∧ U 0 = ⊥ ∧ U (Fin.last n) = ⊤ ∧
      Set.range U = Set.range (ξ.trivialFiltration hξ) ∧ StrictAnti b ∧
      (∀ i t, U i.succ ≤ ξ.trivialFiltration hξ t ↔ t ≤ b i) ∧
      (∀ i, ξ.trivialFiltration hξ (b i) = U i.succ) ∧
      (∀ i, (⨆ s : {s : ℝ // b i < s}, ξ.trivialFiltration hξ s.val) = U i.castSucc) ∧
      (∀ t, ξ.trivialFiltration hξ t = ⨆ (i : Fin n) (_ : t ≤ b i), U i.succ) :=
  Submodule.exists_strictMono_flag_and_jumps_of_antitone
    (ξ.antitone_trivialFiltration hξ) (ξ.trivialFiltration_attains_bot_top hξ).1
    (ξ.trivialFiltration_attains_bot_top hξ).2
    (ξ.trivialFiltration_locallyConstant_left hξ)

end

end ArakelovGeometry.NormFamily
