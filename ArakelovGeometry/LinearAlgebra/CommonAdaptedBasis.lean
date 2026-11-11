/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.LinearAlgebra.FiniteFiltration
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Common bases for two finite flags

Independent-set extension along two flags constructs a single adapted basis.
-/

@[expose] public section

open Module

namespace Submodule

variable {K E : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]

private theorem span_inter_eq_of_extension {S T : Set E} {V W : Submodule K E}
    (hST : S ⊆ T) (hT : T ⊆ S ∪ (V : Set E)) (hVW : V ≤ W)
    (hS : span K (S ∩ (W : Set E)) = span K S ⊓ W) :
    span K (T ∩ (W : Set E)) = span K T ⊓ W := by
  have hdecomp : T = S ∪ (T ∩ (V : Set E)) := by
    ext x
    constructor
    · intro hx
      exact (hT hx).elim Or.inl (fun hv ↦ Or.inr ⟨hx, hv⟩)
    · rintro (hx | hx)
      · exact hST hx
      · exact hx.1
  have hle : span K (T ∩ (V : Set E)) ≤ W :=
    span_le.mpr fun _ hx ↦ hVW hx.2
  apply le_antisymm
  · exact le_inf (span_mono Set.inter_subset_left) (span_le.mpr fun _ hx ↦ hx.2)
  · calc
      span K T ⊓ W = (span K S ⊔ span K (T ∩ (V : Set E))) ⊓ W := by
        conv_lhs => rw [hdecomp, span_union]
      _ = span K (T ∩ (V : Set E)) ⊔ (span K S ⊓ W) := by
        rw [sup_comm, sup_inf_assoc_of_le _ hle]
      _ ≤ span K (T ∩ (W : Set E)) := by
        rw [← hS]
        exact sup_le (span_mono fun _ hx ↦ ⟨hx.1, hVW hx.2⟩)
          (span_mono fun _ hx ↦ ⟨hST hx.1, hx.2⟩)

/-- Extend an independent set compatible with a finite chain so that it spans every step. -/
theorem exists_extension_spanning_flag (n : ℕ)
    (V : Fin (n + 1) → Submodule K E) (hV : Monotone V)
    (S : Set E) (hS : LinearIndepOn K id S)
    (hadapt : ∀ j, span K (S ∩ (V j : Set E)) = span K S ⊓ V j) :
    ∃ T : Set E, LinearIndepOn K id T ∧ S ⊆ T ∧
      T ⊆ S ∪ (V (Fin.last n) : Set E) ∧
      span K T = span K S ⊔ V (Fin.last n) ∧
      ∀ j, span K (T ∩ (V j : Set E)) = V j := by
  classical
  induction n with
  | zero =>
      let hsub : S ⊆ S ∪ (V 0 : Set E) := Set.subset_union_left
      let T := hS.extend hsub
      have hST : S ⊆ T := hS.subset_extend hsub
      have hT : T ⊆ S ∪ (V 0 : Set E) := hS.extend_subset hsub
      have hspan : span K T = span K S ⊔ V 0 := by
        rw [hS.span_extend_eq_span hsub, span_union, span_eq]
      refine ⟨T, hS.linearIndepOn_extend hsub, hST, hT, hspan, ?_⟩
      intro j
      have hj : j = 0 := by apply Fin.ext; omega
      rw [hj, span_inter_eq_of_extension hST hT le_rfl (hadapt 0), hspan,
        inf_eq_right.mpr le_sup_right]
  | succ n ih =>
      obtain ⟨T, hT, hST, hTsub, hspan, hprev⟩ :=
        ih (fun j ↦ V j.castSucc) (fun _ _ h ↦ hV h) (fun j ↦ hadapt j.castSucc)
      let W := V (Fin.last (n + 1))
      have hVW : V (Fin.last n).castSucc ≤ W := hV (Fin.le_last _)
      have hcompat : span K (T ∩ (W : Set E)) = span K T ⊓ W :=
        span_inter_eq_of_extension hST hTsub hVW (hadapt _)
      let hsub : T ⊆ T ∪ (W : Set E) := Set.subset_union_left
      let R := hT.extend hsub
      have hTR : T ⊆ R := hT.subset_extend hsub
      have hRsub : R ⊆ T ∪ (W : Set E) := hT.extend_subset hsub
      have hRspan : span K R = span K T ⊔ W := by
        rw [hT.span_extend_eq_span hsub, span_union, span_eq]
      refine ⟨R, hT.linearIndepOn_extend hsub, hST.trans hTR, ?_, ?_, ?_⟩
      · intro x hx
        rcases hRsub hx with hx | hx
        · exact (hTsub hx).elim Or.inl (fun hv ↦ Or.inr (hVW hv))
        · exact Or.inr hx
      · rw [hRspan, hspan, sup_assoc, sup_eq_right.mpr hVW]
      · intro j
        rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
        · apply le_antisymm (span_le.mpr fun _ hx ↦ hx.2)
          exact (hprev i).symm.le.trans
            (span_mono fun _ hx ↦ ⟨hTR hx.1, hx.2⟩)
        · rw [span_inter_eq_of_extension hTR hRsub le_rfl hcompat, hRspan,
            inf_eq_right.mpr le_sup_right]

/-- Two increasing flags admit compatible independent generators of their final step. -/
theorem exists_independent_generators_two_flags (n m : ℕ)
    (U : Fin (n + 1) → Submodule K E) (V : Fin (m + 1) → Submodule K E)
    (hU : Monotone U) (hV : Monotone V) (hzero : U 0 = ⊥)
    (hVtop : V (Fin.last m) = ⊤) :
    ∃ S : Set E, LinearIndepOn K id S ∧ S ⊆ U (Fin.last n) ∧
      span K S = U (Fin.last n) ∧
      (∀ i, span K (S ∩ (U i : Set E)) = U i) ∧
      ∀ j, span K (S ∩ (V j : Set E)) = U (Fin.last n) ⊓ V j := by
  classical
  induction n with
  | zero =>
      refine ⟨∅, linearIndepOn_empty K id, Set.empty_subset _, ?_, ?_, ?_⟩
      · simpa only [span_empty, Fin.last_zero] using hzero.symm
      · intro i
        have hi : i = 0 := by apply Fin.ext; omega
        simp only [hi, Set.empty_inter, span_empty, hzero]
      · intro j
        simp only [Set.empty_inter, span_empty, Fin.last_zero, hzero, bot_inf_eq]
  | succ n ih =>
      obtain ⟨S, hS, hSsub, hspan, hSU, hSV⟩ :=
        ih (fun i ↦ U i.castSucc) (fun _ _ h ↦ hU h) hzero
      let P := U (Fin.last (n + 1))
      have hUP : U (Fin.last n).castSucc ≤ P := hU (Fin.le_last _)
      have hSP : S ⊆ (P : Set E) := hSsub.trans hUP
      have hcompat : ∀ j, span K (S ∩ ((P ⊓ V j : Submodule K E) : Set E)) =
          span K S ⊓ (P ⊓ V j) := by
        intro j
        have he : S ∩ ((P ⊓ V j : Submodule K E) : Set E) = S ∩ (V j : Set E) := by
          ext x
          exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hSP h.1, h.2⟩⟩
        rw [he, hSV, hspan, ← inf_assoc, inf_eq_left.mpr hUP]
      obtain ⟨T, hT, hST, hTsub, hTspan, hTV⟩ :=
        exists_extension_spanning_flag m (fun j ↦ P ⊓ V j)
          (fun _ _ h ↦ inf_le_inf_left P (hV h)) S hS hcompat
      have hTP : T ⊆ (P : Set E) := by
        intro x hx
        exact (hTsub hx).elim (fun hs ↦ hSP hs) (fun hp ↦ hp.1)
      have hspanT : span K T = P := by
        rw [hTspan, hspan, hVtop, inf_top_eq, sup_eq_right.mpr hUP]
      refine ⟨T, hT, hTP, hspanT, ?_, ?_⟩
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
        · apply le_antisymm (span_le.mpr fun _ hx ↦ hx.2)
          exact (hSU i).symm.le.trans
            (span_mono fun _ hx ↦ ⟨hST hx.1, hx.2⟩)
        · rwa [Set.inter_eq_left.mpr hTP]
      · intro j
        have he : T ∩ ((P ⊓ V j : Submodule K E) : Set E) = T ∩ (V j : Set E) := by
          ext x
          exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hTP h.1, h.2⟩⟩
        simpa only [he] using hTV j

/-- A single finite basis simultaneously spans the steps of two finite flags.
The index type is empty when the ambient space has dimension zero. -/
theorem exists_basis_two_flags [FiniteDimensional K E] (n m : ℕ)
    (U : Fin (n + 1) → Submodule K E) (V : Fin (m + 1) → Submodule K E)
    (hU : Monotone U) (hV : Monotone V) (hzero : U 0 = ⊥)
    (hUtop : U (Fin.last n) = ⊤) (hVtop : V (Fin.last m) = ⊤) :
    ∃ b : Basis (Fin (finrank K E)) K E,
      (∀ i, span K (Set.range b ∩ (U i : Set E)) = U i) ∧
      ∀ j, span K (Set.range b ∩ (V j : Set E)) = V j := by
  classical
  obtain ⟨S, hS, _, hspan, hSU, hSV⟩ :=
    exists_independent_generators_two_flags n m U V hU hV hzero hVtop
  have htop : ⊤ ≤ span K (Set.range (fun x : S ↦ (x : E))) := by
    simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hspan, hUtop] using
      (le_rfl : (⊤ : Submodule K E) ≤ ⊤)
  let b₀ := Basis.mk hS.linearIndependent_restrict htop
  have hr₀ : Set.range b₀ = S := by
    have he : (b₀ : S → E) = Subtype.val := by
      funext i
      exact Basis.mk_apply _ _ i
    rw [he, Subtype.range_coe_subtype, Set.ofPred_mem_eq]
  let b := b₀.reindex (b₀.indexEquiv (Module.finBasis K E))
  have hr : Set.range b = S := (Basis.range_reindex _ _).trans hr₀
  refine ⟨b, ?_, ?_⟩
  · simpa only [hr] using hSU
  · simpa only [hr, hUtop, top_inf_eq] using hSV

/-- Simultaneous adaptation to two decreasing real filtrations. Finite-dimensionality
extracts the finite flags; finite range and adapted bases are not assumptions. -/
theorem exists_basis_adapted_two_filtrations [FiniteDimensional K E]
    {F G : ℝ → Submodule K E}
    (hF : Antitone F) (hFbot : ∃ t, F t = ⊥) (hFtop : ∃ t, F t = ⊤)
    (hG : Antitone G) (hGbot : ∃ t, G t = ⊥) (hGtop : ∃ t, G t = ⊤) :
    ∃ b : Basis (Fin (finrank K E)) K E,
      (∀ t, span K (Set.range b ∩ (F t : Set E)) = F t) ∧
      ∀ t, span K (Set.range b ∩ (G t : Set E)) = G t := by
  obtain ⟨n, U, hU, hUzero, hUtop, hUF⟩ :=
    exists_strictMono_flag_of_antitone hF hFbot hFtop
  obtain ⟨m, V, hV, _, hVtop, hVG⟩ :=
    exists_strictMono_flag_of_antitone hG hGbot hGtop
  obtain ⟨b, hbU, hbV⟩ :=
    exists_basis_two_flags n m U V hU.monotone hV.monotone hUzero hUtop hVtop
  refine ⟨b, ?_, ?_⟩
  · intro t
    obtain ⟨i, hi⟩ : F t ∈ Set.range U := hUF.symm ▸ Set.mem_range_self t
    simpa only [hi] using hbU i
  · intro t
    obtain ⟨j, hj⟩ : G t ∈ Set.range V := hVG.symm ▸ Set.mem_range_self t
    simpa only [hj] using hbV j

end Submodule
