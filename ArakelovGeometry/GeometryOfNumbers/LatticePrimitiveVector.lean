/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.GeometryOfNumbers.LatticeSubspaceBasis
import Mathlib.Analysis.Convex.Basic

/-! # Primitive vectors in actual symmetric convex lattice bodies -/

noncomputable section

namespace ArakelovGeometry.GeometryOfNumbers.LatticePrimitiveVector

open Module Set
open LatticeSubspaceBasis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

omit [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L] in
/-- The actual line through an actual lattice point is rational. -/
theorem span_singleton_rational {x : E} (hxL : x ∈ L) :
    Submodule.span ℝ ((L : Set E) ∩ ((ℝ ∙ x : Submodule ℝ E) : Set E)) =
      ℝ ∙ x := by
  apply le_antisymm (Submodule.span_le.mpr fun _ hx => hx.2)
  apply Submodule.span_le.mpr
  rintro _ (rfl : _ = x)
  exact Submodule.subset_span ⟨hxL, Submodule.subset_span (by simp)⟩

/-- The literal integer lattice intersection with a nonzero lattice line has rank one. -/
theorem intersection_line_finrank {x : E} (hxL : x ∈ L) (hx : x ≠ 0) :
    Module.finrank ℤ (intersection L (ℝ ∙ x)) = 1 := by
  have hcard := Module.finrank_eq_card_basis
    (intersectionRealBasis L (ℝ ∙ x) (span_singleton_rational L hxL))
  rw [Fintype.card_fin, finrank_span_singleton hx] at hcard
  exact hcard.symm

omit [FiniteDimensional ℝ E] in
/-- A symmetric convex set contains the primitive contraction of any nonzero
integer multiple it contains. -/
theorem mem_of_int_smul_mem {C : Set E} (hconvex : Convex ℝ C)
    (hsymm : ∀ y ∈ C, -y ∈ C) {v : E} {n : ℤ} (hn : n ≠ 0)
    (hnv : n • v ∈ C) : v ∈ C := by
  have hzero : (0 : E) ∈ C := by
    simpa only [midpoint_neg_self] using
      hconvex.midpoint_mem (hsymm (n • v) hnv) hnv
  have hpos (m : ℤ) (hm : 0 < m) (hmv : m • v ∈ C) : v ∈ C := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
    have ht : (m : ℝ)⁻¹ ∈ Icc (0 : ℝ) 1 :=
      ⟨inv_nonneg.mpr hm0.le, (inv_le_one₀ hm0).mpr hm1⟩
    have h := hconvex.smul_mem_of_zero_mem hzero hmv ht
    rw [← Int.cast_smul_eq_zsmul ℝ m v, smul_smul,
      inv_mul_cancel₀ (ne_of_gt hm0), one_smul] at h
    exact h
  rcases lt_or_gt_of_ne hn with hnneg | hnpos
  · apply hpos (-n) (by omega)
    simpa only [neg_smul] using hsymm (n • v) hnv
  · exact hpos n hnpos hnv

/-- Every point of the actual rank-one intersection is an integer multiple
of one of its constructed basis vectors. -/
theorem exists_intersection_generator {x : E} (hxL : x ∈ L) (hx : x ≠ 0) :
    ∃ i : Fin (Module.finrank ℤ (intersection L (ℝ ∙ x))),
      ∀ y : intersection L (ℝ ∙ x),
        ∃ n : ℤ, n • intersectionBasis L (ℝ ∙ x) i = y := by
  let b := (intersectionBasis L (ℝ ∙ x)).reindex
    (finCongr (intersection_line_finrank L hxL hx))
  refine ⟨(finCongr (intersection_line_finrank L hxL hx)).symm 0, ?_⟩
  intro y
  refine ⟨b.repr y 0, ?_⟩
  have h := b.sum_repr y
  simpa only [Fin.sum_univ_one, b, Basis.reindex_apply] using h

/-- The exact generator of the actual lattice line extends to an actual integer
basis of L, and generates the whole literal intersection. -/
theorem exists_basis_generator_on_line {x : E} (hxL : x ∈ L) (hx : x ≠ 0) :
    ∃ (b : Basis (Fin (Module.finrank ℤ L)) ℤ L) (i : Fin (Module.finrank ℤ L)),
      (ℝ ∙ (b i : E) : Submodule ℝ E) = ℝ ∙ x ∧
      L ⊓ (ℝ ∙ x : Submodule ℝ E).restrictScalars ℤ = ℤ ∙ (b i : E) := by
  classical
  let U : Submodule ℝ E := ℝ ∙ x
  obtain ⟨j, hj⟩ := exists_intersection_generator L hxL hx
  let g : intersection L U := intersectionBasis L U j
  let v : L := g
  have hvU : (v : E) ∈ U := g.property
  have hgen (y : E) (hyL : y ∈ L) (hyU : y ∈ U) : ∃ n : ℤ, n • (v : E) = y := by
    obtain ⟨n, hn⟩ := hj ⟨⟨y, hyL⟩, hyU⟩
    exact ⟨n, congrArg (fun z : intersection L U => ((z : L) : E)) hn⟩
  have hspan : (ℝ ∙ (v : E) : Submodule ℝ E) = U := by
    apply le_antisymm (Submodule.span_le.mpr (by simpa using hvU))
    apply Submodule.span_le.mpr
    intro y hy
    have hyx : y = x := by simpa using hy
    rw [hyx]
    obtain ⟨n, hn⟩ := hgen x hxL (Submodule.mem_span_singleton_self x)
    rw [← hn, ← Int.cast_smul_eq_zsmul ℝ n (v : E)]
    exact (ℝ ∙ (v : E) : Submodule ℝ E).smul_mem _
      (Submodule.mem_span_singleton_self _)
  have hint : L ⊓ U.restrictScalars ℤ = ℤ ∙ (v : E) := by
    ext y
    constructor
    · rintro ⟨hyL, hyU⟩
      exact Submodule.mem_span_singleton.mpr (hgen y hyL hyU)
    · intro hy
      obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hy
      exact ⟨L.smul_mem _ v.property, (U.restrictScalars ℤ).smul_mem _ hvU⟩
  let B := adaptedBasis L U
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis B).symm
  refine ⟨B.reindex e, e (Sum.inl j), ?_⟩
  have hBi : (B.reindex e) (e (Sum.inl j)) = v := by
    simp only [Basis.reindex_apply, Equiv.symm_apply_apply, B, adaptedBasis_inl]
    rfl
  rw [hBi]
  exact ⟨hspan, hint⟩

/-- A nonzero lattice point in a symmetric convex set produces a nonzero actual
lattice vector inside the set and an actual integer basis extending that vector. -/
theorem exists_primitive_mem_on_line {C : Set E} (hconvex : Convex ℝ C)
    (hsymm : ∀ y ∈ C, -y ∈ C) {x : E} (hxC : x ∈ C) (hxL : x ∈ L) (hx : x ≠ 0) :
    ∃ v : L, (v : E) ≠ 0 ∧ (v : E) ∈ C ∧
      (ℝ ∙ (v : E) : Submodule ℝ E) = ℝ ∙ x ∧
      L ⊓ (ℝ ∙ (v : E) : Submodule ℝ E).restrictScalars ℤ = ℤ ∙ (v : E) ∧
      ∃ (b : Basis (Fin (Module.finrank ℤ L)) ℤ L) (i : Fin (Module.finrank ℤ L)),
        b i = v := by
  obtain ⟨b, i, hspan, hgen⟩ := exists_basis_generator_on_line L hxL hx
  have hxb : x ∈ ℤ ∙ (b i : E) := by
    rw [← hgen]
    exact ⟨hxL, Submodule.mem_span_singleton_self _⟩
  obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp hxb
  have hn0 : n ≠ 0 := by
    intro h
    apply hx
    simpa only [h, zero_smul] using hn.symm
  have hvC : (b i : E) ∈ C := mem_of_int_smul_mem hconvex hsymm hn0 (hn.symm ▸ hxC)
  refine ⟨b i, ?_, hvC, hspan, ?_, b, i, rfl⟩
  · intro h
    exact b.ne_zero i (Subtype.ext h)
  · rw [hspan]
    exact hgen

/-- The source-facing primitive-vector choice, with the genuine extending lattice
basis and the exact integer intersection stated as conclusions. -/
theorem exists_primitive_mem {C : Set E} (hconvex : Convex ℝ C)
    (hsymm : ∀ y ∈ C, -y ∈ C) (hnonzero : ∃ x ∈ C ∩ (L : Set E), x ≠ 0) :
    ∃ v : L, (v : E) ≠ 0 ∧ (v : E) ∈ C ∧
      L ⊓ (ℝ ∙ (v : E) : Submodule ℝ E).restrictScalars ℤ = ℤ ∙ (v : E) ∧
      ∃ (b : Basis (Fin (Module.finrank ℤ L)) ℤ L) (i : Fin (Module.finrank ℤ L)),
        b i = v := by
  obtain ⟨x, ⟨hxC, hxL⟩, hx⟩ := hnonzero
  obtain ⟨v, hv, hvC, _, hgen, hb⟩ :=
    exists_primitive_mem_on_line L hconvex hsymm hxC hxL hx
  exact ⟨v, hv, hvC, hgen, hb⟩

end ArakelovGeometry.GeometryOfNumbers.LatticePrimitiveVector
