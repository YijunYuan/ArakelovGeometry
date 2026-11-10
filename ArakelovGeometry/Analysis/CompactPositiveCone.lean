/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Compact bases of closed positive cones

The contact-matrix cone in the real/complex ellipsoid theorem has a compact
trace-one base. Carathéodory's finite-dimensional bound gives compactness of
its actual convex hull, rather than replacing it by a closure.
-/

open Set
open scoped Pointwise

noncomputable section

namespace ArakelovGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A finite-dimensional convex hull is a finite union of simplex images of
tuples from the original set. No closure is introduced. -/
theorem convexHull_eq_bounded_simplex_images (s : Set E) :
    convexHull ℝ s = ⋃ n : Fin (Module.finrank ℝ E + 2),
      (fun p : (Fin n.val → ℝ) × (Fin n.val → E) => ∑ i, p.1 i • p.2 i) ''
        (stdSimplex ℝ (Fin n.val) ×ˢ {z : Fin n.val → E | ∀ i, z i ∈ s}) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    let t := Caratheodory.minCardFinsetOfMemConvexHull hx
    have ht : (t : Set E) ⊆ s := Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
    have ha : AffineIndependent ℝ ((↑) : t → E) :=
      Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
    have hn : Fintype.card t < Module.finrank ℝ E + 2 := by
      have hc := ha.card_le_finrank_succ
      have hd := (vectorSpan ℝ (Set.range ((↑) : t → E))).finrank_le
      omega
    have hm : x ∈ convexHull ℝ (t : Set E) := Caratheodory.mem_minCardFinsetOfMemConvexHull hx
    obtain ⟨w, hw, hw₁, hsum⟩ := Finset.mem_convexHull'.mp hm
    let e := Fintype.equivFin t
    apply Set.mem_iUnion.mpr
    refine ⟨⟨Fintype.card t, hn⟩, ?_⟩
    refine ⟨(fun i => w (e.symm i), fun i => (e.symm i : E)), ⟨?_, ?_⟩, ?_⟩
    · refine ⟨fun i => hw _ (e.symm i).property, ?_⟩
      rw [e.symm.sum_comp (fun i : t => w (i : E))]
      simpa only [Finset.univ_eq_attach, Finset.sum_attach] using hw₁
    · intro i
      exact ht (e.symm i).property
    · change (∑ i, w (e.symm i) • (e.symm i : E)) = x
      rw [e.symm.sum_comp (fun i : t => w (i : E) • (i : E))]
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach t (fun y => w y • y)).trans hsum
  · intro x hx
    obtain ⟨n, p, hp, rfl⟩ := Set.mem_iUnion.mp hx
    exact (convex_convexHull ℝ s).sum_mem (fun i _ => hp.1.1 i) hp.1.2
      (fun i _ => subset_convexHull ℝ s (hp.2 i))

/-- The convex hull of a compact set in a finite-dimensional real normed
space is compact, by the exact bounded simplex parametrization. -/
theorem isCompact_convexHull_of_finiteDimensional {s : Set E} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  rw [convexHull_eq_bounded_simplex_images]
  apply isCompact_iUnion
  intro n
  apply ((isCompact_stdSimplex ℝ (Fin n.val)).prod
    (isCompact_pi_infinite fun _ : Fin n.val => hs)).image
  exact continuous_finsetSum _ (fun i _ =>
    ((continuous_apply i).comp continuous_fst).smul ((continuous_apply i).comp continuous_snd))

omit [FiniteDimensional ℝ E] in
/-- The actual finite conical hull is the nonnegative scaling of the convex
hull. Nonemptiness supplies the base point for the zero element. -/
theorem mem_pointedCone_hull_iff_nonneg_smul_convexHull {s : Set E} (hs : s.Nonempty) (x : E) :
    x ∈ PointedCone.hull ℝ s ↔ ∃ r : ℝ, 0 ≤ r ∧
      ∃ y ∈ convexHull ℝ s, r • y = x := by
  classical
  obtain ⟨z, hz⟩ := hs
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, zero_le_one, x, subset_convexHull ℝ s hx, one_smul ℝ x⟩
    | zero => exact ⟨0, le_rfl, z, subset_convexHull ℝ s hz, zero_smul ℝ z⟩
    | add x y hx hy ihx ihy =>
        obtain ⟨r, hr, u, hu, rfl⟩ := ihx
        obtain ⟨t, ht, v, hv, rfl⟩ := ihy
        by_cases hrt : r + t = 0
        · have hr0 : r = 0 := by linarith
          have ht0 : t = 0 := by linarith
          exact ⟨0, le_rfl, z, subset_convexHull ℝ s hz, by simp [hr0, ht0]⟩
        · refine ⟨r + t, add_nonneg hr ht, (r / (r + t)) • u + (t / (r + t)) • v,
            (convex_convexHull ℝ s) hu hv
              (div_nonneg hr (add_nonneg hr ht)) (div_nonneg ht (add_nonneg hr ht))
                (by rw [← add_div, div_self hrt]), ?_⟩
          simp only [smul_add, smul_smul]
          congr 1 <;> congr 1 <;> field_simp
    | smul a x hx ih =>
        obtain ⟨r, hr, y, hy, rfl⟩ := ih
        exact ⟨(a : ℝ) * r, mul_nonneg a.property hr, y, hy, mul_smul (a : ℝ) r y⟩
  · rintro ⟨r, hr, y, hy, rfl⟩
    apply (PointedCone.hull ℝ s).smul_mem hr
    exact convexHull_min PointedCone.subset_hull (PointedCone.hull ℝ s).toConvexCone.convex hy

/-- A compact base lying in a continuous trace-one hyperplane generates a
closed actual finite conical hull. -/
theorem isClosed_pointedCone_hull_of_compact_base {s : Set E} (hs : IsCompact s)
    (hne : s.Nonempty) (f : E →L[ℝ] ℝ) (hf : ∀ x ∈ s, f x = 1) :
    IsClosed (PointedCone.hull ℝ s : Set E) := by
  let B := convexHull ℝ s
  have hB : IsCompact B := isCompact_convexHull_of_finiteDimensional hs
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB
  have hlevel : ∀ y ∈ B, f y = 1 :=
    convexHull_min hf ((convex_singleton (1 : ℝ)).linear_preimage f.toLinearMap)
  have he : (PointedCone.hull ℝ s : Set E) =
      {x | 0 ≤ f x} ∩ Prod.fst '' {p : E × B | f p.1 • (p.2 : E) = p.1} := by
    ext x
    rw [SetLike.mem_coe, mem_pointedCone_hull_iff_nonneg_smul_convexHull hne]
    constructor
    · rintro ⟨r, hr, y, hy, hxy⟩
      have ht : f x = r := by rw [← hxy, map_smul, hlevel y hy, smul_eq_mul, mul_one]
      refine ⟨?_, ⟨(x, ⟨y, hy⟩), ?_, rfl⟩⟩
      · change 0 ≤ f x
        simpa only [ht] using hr
      · change f x • y = x
        simpa only [ht] using hxy
    · rintro ⟨hx, p, hp, rfl⟩
      exact ⟨f p.1, hx, p.2, p.2.property, hp⟩
  rw [he]
  apply (isClosed_le continuous_const f.continuous).inter
  apply isClosedMap_fst_of_compactSpace
  exact isClosed_eq ((f.continuous.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)) continuous_fst

/-- A point outside the actual cone of a compact trace-one base admits a
strictly positive separating functional that is nonpositive on every generator. -/
theorem exists_separating_functional_of_not_mem_pointedCone_hull {s : Set E}
    (hs : IsCompact s) (hne : s.Nonempty) (f : E →L[ℝ] ℝ)
    (hf : ∀ x ∈ s, f x = 1) {x : E} (hx : x ∉ PointedCone.hull ℝ s) :
    ∃ g : E →L[ℝ] ℝ, 0 < g x ∧ ∀ y ∈ s, g y ≤ 0 := by
  let C : ProperCone ℝ E :=
    ⟨PointedCone.hull ℝ s, isClosed_pointedCone_hull_of_compact_base hs hne f hf⟩
  obtain ⟨g, hg, hgx⟩ := C.hyperplane_separation (convex_singleton x) isCompact_singleton
    (Set.disjoint_singleton_left.mpr hx)
  refine ⟨-g, ?_, fun y hy => ?_⟩
  · exact neg_pos.mpr (hgx x rfl)
  · exact neg_nonpos.mpr (hg y (PointedCone.subset_hull hy))

end ArakelovGeometry
