/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.GeometryOfNumbers.LatticePrimitiveVector
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-! # Actual spanning lattice bodies and the geometric induction hypotheses -/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.GeometryOfNumbers.LatticeSpanningBody

open Set LatticeSubspaceBasis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonempty symmetric convex body contains its actual center. -/
theorem zero_mem_of_nonempty {C : Set E} (hC : Convex ℝ C)
    (hsC : ∀ x ∈ C, -x ∈ C) (hne : C.Nonempty) : (0 : E) ∈ C := by
  obtain ⟨x, hx⟩ := hne
  simpa only [midpoint_self_neg] using hC.midpoint_mem hx (hsC x hx)

/-- Full real span and symmetry put the center in the actual interior. -/
theorem zero_mem_interior_of_span [FiniteDimensional ℝ E] {C : Set E}
    (hC : Convex ℝ C) (hsC : ∀ x ∈ C, -x ∈ C) (h0 : (0 : E) ∈ C)
    (hspan : Submodule.span ℝ C = ⊤) : (0 : E) ∈ interior C := by
  have ha : affineSpan ℝ C = ⊤ := by
    have he := affineSpan_insert_zero (k := ℝ) C
    rw [insert_eq_of_mem h0, hspan] at he
    exact he.trans (by ext; simp)
  obtain ⟨x, hx⟩ := hC.interior_nonempty_iff_affineSpan_eq_top.mpr ha
  have hm := hC.combo_interior_self_mem_interior hx (hsC x (interior_subset hx))
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  simpa only [smul_neg, add_neg_cancel] using hm

/-- Actual lattice-point spanning implies the genuine interior hypothesis. -/
theorem zero_mem_interior_of_lattice_span [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) {C : Set E} (hC : Convex ℝ C)
    (hsC : ∀ x ∈ C, -x ∈ C) (h0 : (0 : E) ∈ C)
    (hspan : Submodule.span ℝ (C ∩ (L : Set E)) = ⊤) : (0 : E) ∈ interior C := by
  apply zero_mem_interior_of_span hC hsC h0
  apply top_unique
  rw [← hspan]
  exact Submodule.span_mono inter_subset_left

/-- In positive dimension an actual spanning lattice body contains a nonzero lattice point. -/
theorem exists_nonzero_latticePoint_of_span [Nontrivial E] (L : Submodule ℤ E)
    {C : Set E} (hspan : Submodule.span ℝ (C ∩ (L : Set E)) = ⊤) :
    ∃ x : E, x ∈ C ∧ x ∈ L ∧ x ≠ 0 := by
  by_contra h
  have hb : Submodule.span ℝ (C ∩ (L : Set E)) = ⊥ := by
    apply Submodule.span_eq_bot.mpr
    intro x hx
    by_contra hne
    exact h ⟨x, hx.1, hx.2, hne⟩
  exact top_ne_bot (hspan.symm.trans hb)

/-- Projection preserves spanning by the actual body points of the actual quotient lattice. -/
theorem quotient_latticePoints_span (L : Submodule ℤ E) (U : Submodule ℝ E)
    {C : Set E} (hspan : Submodule.span ℝ (C ∩ (L : Set E)) = ⊤) :
    Submodule.span ℝ ((U.mkQ '' C) ∩ (quotientImage L U : Set (E ⧸ U))) = ⊤ := by
  apply top_unique
  rw [← U.range_mkQ, ← Submodule.map_top, ← hspan, Submodule.map_span]
  apply Submodule.span_mono
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
  exact Submodule.mem_map.mpr ⟨x, hx.2, rfl⟩

/-- Quotienting by an actual nonzero vector lowers the induction dimension by one. -/
theorem finrank_quotient_line_add_one [FiniteDimensional ℝ E] {v : E} (hv : v ≠ 0) :
    Module.finrank ℝ (E ⧸ (ℝ ∙ v)) + 1 = Module.finrank ℝ E := by
  simpa only [finrank_span_singleton hv] using
    (ℝ ∙ v).finrank_quotient_add_finrank

end ArakelovGeometry.GeometryOfNumbers.LatticeSpanningBody
