/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.LinearAlgebra.FiniteFiltration
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# Intrinsic tensor filtrations

The convolution is defined by the images of the tensor products of the actual
filtration steps. Adapted bases compute its steps and its strict right limits
using the original sums of weights, including repeated sums.
-/

@[expose] public section

open scoped TensorProduct
open Module

namespace Submodule

variable {K E V : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup V] [Module K V]

/-- The intrinsic convolution of two real families of subspaces. -/
noncomputable def tensorFiltration (F : ℝ → Submodule K E) (G : ℝ → Submodule K V)
    (γ : ℝ) : Submodule K (E ⊗[K] V) :=
  ⨆ (t : ℝ) (u : ℝ) (_ : γ ≤ t + u), LinearMap.range (TensorProduct.mapIncl (F t) (G u))

/-- Each tensor of filtered vectors lies in the step indexed by their total threshold. -/
theorem tmul_mem_tensorFiltration {F : ℝ → Submodule K E} {G : ℝ → Submodule K V}
    {t u γ : ℝ} (h : γ ≤ t + u) {x : E} {y : V} (hx : x ∈ F t) (hy : y ∈ G u) :
    x ⊗ₜ[K] y ∈ tensorFiltration F G γ := by
  have hle : LinearMap.range (TensorProduct.mapIncl (F t) (G u)) ≤
      tensorFiltration F G γ :=
    le_iSup_of_le t (le_iSup_of_le u (le_iSup_of_le h le_rfl))
  exact hle ⟨⟨x, hx⟩ ⊗ₜ[K] ⟨y, hy⟩, rfl⟩

/-- Increasing the threshold decreases the intrinsic tensor convolution. -/
theorem antitone_tensorFiltration (F : ℝ → Submodule K E) (G : ℝ → Submodule K V) :
    Antitone (tensorFiltration F G) := by
  intro a b hab
  exact iSup_le fun t ↦ iSup_le fun u ↦ iSup_le fun h ↦
    le_iSup_of_le t (le_iSup_of_le u (le_iSup_of_le (hab.trans h) le_rfl))

/-- The convolution of weighted spans is the span of tensors with the original summed weights. -/
theorem tensorFiltration_eq_span {ι κ : Type*} (b : ι → E) (c : κ → V)
    (w : ι → ℝ) (z : κ → ℝ) {F : ℝ → Submodule K E} {G : ℝ → Submodule K V}
    (hF : ∀ t, F t = span K (b '' {i | t ≤ w i}))
    (hG : ∀ u, G u = span K (c '' {j | u ≤ z j})) (γ : ℝ) :
    tensorFiltration F G γ =
      span K ((fun ij : ι × κ ↦ b ij.1 ⊗ₜ[K] c ij.2) '' {ij | γ ≤ w ij.1 + z ij.2}) := by
  apply le_antisymm
  · refine iSup_le fun t ↦ iSup_le fun u ↦ iSup_le fun h ↦ ?_
    rw [TensorProduct.range_mapIncl, hF, hG, map₂_span_span]
    apply span_mono
    rintro _ ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨(i, j), h.trans (add_le_add hi hj), rfl⟩
  · apply span_le.mpr
    rintro _ ⟨⟨i, j⟩, h, rfl⟩
    apply tmul_mem_tensorFiltration h
    · rw [hF]
      exact subset_span ⟨i, show w i ≤ w i from le_rfl, rfl⟩
    · rw [hG]
      exact subset_span ⟨j, show z j ≤ z j from le_rfl, rfl⟩

/-- The strict right limit consists exactly of tensors whose total weight is strictly larger. -/
theorem tensorFiltration_rightLimit_eq_span {ι κ : Type*} (b : ι → E) (c : κ → V)
    (w : ι → ℝ) (z : κ → ℝ) {F : ℝ → Submodule K E} {G : ℝ → Submodule K V}
    (hF : ∀ t, F t = span K (b '' {i | t ≤ w i}))
    (hG : ∀ u, G u = span K (c '' {j | u ≤ z j})) (γ : ℝ) :
    (⨆ s : {s : ℝ // γ < s}, tensorFiltration F G s.val) =
      span K ((fun ij : ι × κ ↦ b ij.1 ⊗ₜ[K] c ij.2) '' {ij | γ < w ij.1 + z ij.2}) := by
  apply le_antisymm
  · refine iSup_le fun s ↦ ?_
    rw [tensorFiltration_eq_span b c w z hF hG]
    apply span_mono
    rintro _ ⟨ij, hij, rfl⟩
    exact ⟨ij, s.property.trans_le hij, rfl⟩
  · apply span_le.mpr
    rintro _ ⟨ij, hij, rfl⟩
    apply mem_iSup_of_mem ⟨w ij.1 + z ij.2, hij⟩
    rw [tensorFiltration_eq_span b c w z hF hG]
    exact subset_span ⟨ij, show w ij.1 + z ij.2 ≤ w ij.1 + z ij.2 from le_rfl, rfl⟩

section FiniteBases

variable {ι κ : Type*} [Finite ι] [Finite κ] (b : Basis ι K E) (c : Basis κ K V)
  (w : ι → ℝ) (z : κ → ℝ) {F : ℝ → Submodule K E} {G : ℝ → Submodule K V}
  (hF : ∀ t, F t = span K (b '' {i | t ≤ w i}))
  (hG : ∀ u, G u = span K (c '' {j | u ≤ z j}))

include hF hG

omit [Finite ι] [Finite κ] in
/-- The tensor basis is adapted, with each weight the sum of its two original weights. -/
theorem tensorFiltration_eq_span_tensorProduct (γ : ℝ) :
    tensorFiltration F G γ =
      span K (b.tensorProduct c '' {ij | γ ≤ w ij.1 + z ij.2}) := by
  simpa only [Basis.tensorProduct_apply'] using tensorFiltration_eq_span b c w z hF hG γ

/-- Only finitely many subspaces occur in the weighted tensor convolution. -/
theorem finite_range_tensorFiltration : (Set.range (tensorFiltration F G)).Finite := by
  apply (Set.finite_range (fun s : Set (ι × κ) ↦ span K (b.tensorProduct c '' s))).subset
  rintro _ ⟨γ, rfl⟩
  exact ⟨{ij | γ ≤ w ij.1 + z ij.2}, (tensorFiltration_eq_span_tensorProduct b c w z hF hG γ).symm⟩

/-- Finite weighted tensor filtrations attain both extreme subspaces, even for an empty basis. -/
theorem tensorFiltration_attains_bot_top :
    (∃ γ, tensorFiltration F G γ = ⊥) ∧ (∃ γ, tensorFiltration F G γ = ⊤) := by
  have hw := Set.finite_range (fun ij : ι × κ ↦ w ij.1 + z ij.2)
  obtain ⟨U, hU⟩ := hw.bddAbove
  obtain ⟨L, hL⟩ := hw.bddBelow
  constructor
  · refine ⟨U + 1, ?_⟩
    rw [tensorFiltration_eq_span_tensorProduct b c w z hF hG]
    have he : {ij : ι × κ | U + 1 ≤ w ij.1 + z ij.2} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ij hij
      have := hU (Set.mem_range_self ij)
      change U + 1 ≤ w ij.1 + z ij.2 at hij
      linarith
    rw [he, Set.image_empty, span_empty]
  · refine ⟨L, ?_⟩
    rw [tensorFiltration_eq_span_tensorProduct b c w z hF hG]
    have he : {ij : ι × κ | L ≤ w ij.1 + z ij.2} = Set.univ := by
      exact Set.eq_univ_iff_forall.mpr fun ij ↦ hL (Set.mem_range_self ij)
    rw [he, Set.image_univ, (b.tensorProduct c).span_eq]

/-- The included threshold is constant on a genuine interval to its left. -/
theorem tensorFiltration_locallyConstant_left (γ : ℝ) :
    ∃ ε > 0, ∀ s, γ - ε < s → s ≤ γ → tensorFiltration F G s = tensorFiltration F G γ := by
  let W := Set.range (fun ij : ι × κ ↦ w ij.1 + z ij.2)
  let A := W ∩ Set.Iio γ
  have hA : A.Finite := (Set.finite_range _).subset Set.inter_subset_left
  have hgap : ∃ ε > 0, ∀ r ∈ W, r < γ → r ≤ γ - ε := by
    by_cases hn : A.Nonempty
    · have hm : sSup A ∈ A := hn.csSup_mem hA
      refine ⟨γ - sSup A, sub_pos.mpr hm.2, ?_⟩
      intro r hr hrg
      have := le_csSup hA.bddAbove (show r ∈ A from ⟨hr, hrg⟩)
      linarith
    · exact ⟨1, zero_lt_one, fun r hr hrg ↦ (hn ⟨r, hr, hrg⟩).elim⟩
  obtain ⟨ε, hε, hgap⟩ := hgap
  refine ⟨ε, hε, fun s hs hsg ↦ ?_⟩
  rw [tensorFiltration_eq_span_tensorProduct b c w z hF hG,
    tensorFiltration_eq_span_tensorProduct b c w z hF hG]
  congr 2
  ext ij
  constructor
  · intro hij
    by_contra h
    have := hgap _ (Set.mem_range_self ij) (lt_of_not_ge h)
    change s ≤ w ij.1 + z ij.2 at hij
    linarith
  · exact fun hij ↦ hsg.trans hij

end FiniteBases

section FiniteFamily

variable {J : Type*} [Fintype J] {M : J → Type*}
  [∀ j, AddCommGroup (M j)] [∀ j, Module K (M j)]

/-- Intrinsic convolution for a finite family, retaining every threshold tuple. -/
noncomputable def piTensorFiltration (F : ∀ j, ℝ → Submodule K (M j)) (γ : ℝ) :
    Submodule K (⨂[K] j, M j) :=
  ⨆ (t : J → ℝ) (_ : γ ≤ ∑ j, t j), LinearMap.range (PiTensorProduct.mapIncl (fun j ↦ F j (t j)))

/-- A finite tensor of filtered vectors belongs to the step at the sum of their thresholds. -/
theorem tprod_mem_piTensorFiltration {F : ∀ j, ℝ → Submodule K (M j)}
    {t : J → ℝ} {γ : ℝ} (h : γ ≤ ∑ j, t j) (x : ∀ j, M j)
    (hx : ∀ j, x j ∈ F j (t j)) :
    (⨂ₜ[K] j, x j) ∈ piTensorFiltration F γ := by
  apply (show LinearMap.range (PiTensorProduct.mapIncl (fun j ↦ F j (t j))) ≤
    piTensorFiltration F γ from le_iSup_of_le t (le_iSup_of_le h le_rfl))
  refine ⟨⨂ₜ[K] j, (⟨x j, hx j⟩ : F j (t j)), ?_⟩
  simp only [PiTensorProduct.mapIncl, PiTensorProduct.map_tprod, subtype_apply]

/-- The finite-family intrinsic convolution has the original sums of adapted basis weights. -/
theorem piTensorFiltration_eq_span {κ : J → Type*} (b : ∀ j, Basis (κ j) K (M j))
    (w : ∀ j, κ j → ℝ) {F : ∀ j, ℝ → Submodule K (M j)}
    (hF : ∀ j t, F j t = span K (b j '' {i | t ≤ w j i})) (γ : ℝ) :
    piTensorFiltration F γ = span K
      (Basis.piTensorProduct b '' {p | γ ≤ ∑ j, w j (p j)}) := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    rw [PiTensorProduct.mapIncl, PiTensorProduct.map_range_eq_span_tprod]
    apply span_le.mpr
    rintro _ ⟨x, rfl⟩
    apply (Basis.piTensorProduct b).mem_span_image.mpr
    intro p hp
    have hn := Finsupp.mem_support_iff.mp hp
    rw [Basis.piTensorProduct_repr_tprod_apply] at hn
    apply ht.trans
    apply Finset.sum_le_sum
    intro j _
    have hx := (hF j (t j)).le (x j).property
    exact (b j).mem_span_image.mp hx
      (Finsupp.mem_support_iff.mpr ((Finset.prod_ne_zero_iff.mp hn) j (Finset.mem_univ j)))
  · apply span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    rw [Basis.piTensorProduct_apply]
    apply tprod_mem_piTensorFiltration hp
    intro j
    rw [hF]
    exact subset_span ⟨p j, show w j (p j) ≤ w j (p j) from le_rfl, rfl⟩

/-- The finite-family strict cut retains exactly the strictly larger original total weights. -/
theorem piTensorFiltration_rightLimit_eq_span {κ : J → Type*}
    (b : ∀ j, Basis (κ j) K (M j)) (w : ∀ j, κ j → ℝ)
    {F : ∀ j, ℝ → Submodule K (M j)}
    (hF : ∀ j t, F j t = span K (b j '' {i | t ≤ w j i})) (γ : ℝ) :
    (⨆ s : {s : ℝ // γ < s}, piTensorFiltration F s.val) =
      span K (Basis.piTensorProduct b '' {p | γ < ∑ j, w j (p j)}) := by
  apply le_antisymm
  · apply iSup_le
    intro s
    rw [piTensorFiltration_eq_span b w hF]
    exact span_mono (Set.image_mono (fun _ hp ↦ s.property.trans_le hp))
  · apply span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    apply (le_iSup (fun s : {s : ℝ // γ < s} ↦ piTensorFiltration F s.val)
      ⟨∑ j, w j (p j), hp⟩)
    rw [piTensorFiltration_eq_span b w hF]
    exact subset_span ⟨p, show (∑ j, w j (p j)) ≤ ∑ j, w j (p j) from le_rfl, rfl⟩

end FiniteFamily

end Submodule
