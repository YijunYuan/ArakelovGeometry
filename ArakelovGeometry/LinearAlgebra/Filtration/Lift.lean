/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.LinearAlgebra.FiniteFiltration
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Lifting prescribed bases along a finite flag

The adjacent quotients are the actual quotients of the flag subspaces.
The construction retains the index of each prescribed quotient basis vector.
All choices are choices of representatives; no canonical splitting is asserted.
-/

@[expose] public section

open Module
open scoped BigOperators

namespace Submodule

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- Representatives of a quotient basis, together with the kernel, span the source. -/
theorem sup_span_eq_top_of_quotient_basis {ι : Type*} (U : Submodule K E)
    (b : Basis ι K (E ⧸ U)) (v : ι → E) (hv : ∀ j, U.mkQ (v j) = b j) :
    U ⊔ span K (Set.range v) = ⊤ := by
  rw [← map_mkQ_eq_top, map_span, ← Set.range_comp]
  have he : U.mkQ ∘ v = b := funext hv
  rw [he, b.span_eq]

/-- Lifted representatives span exactly the next subspace after adjoining the preceding one. -/
theorem sup_span_eq_of_quotient_basis {ι : Type*} (U V : Submodule K E) (hUV : U ≤ V)
    (b : Basis ι K (V ⧸ U.comap V.subtype)) (v : ι → V)
    (hv : ∀ j, (U.comap V.subtype).mkQ (v j) = b j) :
    U ⊔ span K (Set.range (fun j ↦ (v j : E))) = V := by
  have h := congrArg (Submodule.map V.subtype)
    (sup_span_eq_top_of_quotient_basis (U.comap V.subtype) b v hv)
  simpa only [map_sup, map_comap_eq, range_subtype, inf_eq_right.mpr hUV,
    map_span, ← Set.range_comp, Function.comp_def, map_top, subtype_apply] using h

section Flag

variable {n : ℕ} (U : Fin (n + 1) → Submodule K E)
  {ι : Fin n → Type*}
  (b : ∀ i, Basis (ι i) K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype))
  (v : ∀ i, ι i → U i.succ)
  (hv : ∀ i j, ((U i.castSucc).comap (U i.succ).subtype).mkQ (v i j) = b i j)

include hv in
/-- At every step, the representatives of all earlier quotient bases span that step. -/
theorem span_flag_quotient_lifts (hU : Monotone U) (hzero : U 0 = ⊥)
    (k : Fin (n + 1)) :
    span K {x | ∃ i j, i.val < k.val ∧ (v i j : E) = x} = U k := by
  induction k using Fin.induction with
  | zero =>
      simp [hzero]
  | succ k ih =>
      have hs : {x | ∃ i j, i.val < k.succ.val ∧ (v i j : E) = x} =
          {x | ∃ i j, i.val < k.castSucc.val ∧ (v i j : E) = x} ∪
            Set.range (fun j ↦ (v k j : E)) := by
        ext x
        constructor
        · rintro ⟨i, j, hij, rfl⟩
          by_cases hi : i = k
          · subst i
            exact Or.inr ⟨j, rfl⟩
          · exact Or.inl ⟨i, j, by
              have hne : i.val ≠ k.val := fun h ↦ hi (Fin.ext h)
              simp only [Fin.val_succ, Fin.val_castSucc] at *
              omega, rfl⟩
        · rintro (⟨i, j, hij, rfl⟩ | ⟨j, rfl⟩)
          · exact ⟨i, j, Nat.lt_succ_of_lt hij, rfl⟩
          · exact ⟨k, j, Nat.lt_succ_self _, rfl⟩
      rw [hs, span_union, ih]
      exact sup_span_eq_of_quotient_basis _ _ (hU k.castSucc_le_succ) (b k) (v k) (hv k)

variable [FiniteDimensional K E] [∀ i, Fintype (ι i)]

include b in
/-- The number of prescribed quotient basis vectors is the rank of the final flag term. -/
theorem card_flag_quotient_basis (hU : Monotone U) (hzero : U 0 = ⊥) :
    Fintype.card (Σ i, ι i) = finrank K (U (Fin.last n)) := by
  classical
  rw [Fintype.card_sigma]
  induction n with
  | zero =>
      change 0 = finrank K (U 0)
      rw [hzero, finrank_bot]
  | succ n ih =>
      let G : Fin (n + 1) → Submodule K E := fun i ↦ U i.castSucc
      have hG : Monotone G := hU.comp Fin.strictMono_castSucc.monotone
      have hzG : G 0 = ⊥ := hzero
      have hp := ih G (fun i ↦ b i.castSucc) hG hzG
      have hs := ((U (Fin.last n).castSucc).comap
        (U (Fin.last (n + 1))).subtype).finrank_quotient_add_finrank
      rw [(comapSubtypeEquivOfLe (hU (Fin.le_last _))).finrank_eq] at hs
      rw [Fin.sum_univ_castSucc, hp, ← finrank_eq_card_basis (b (Fin.last n))]
      exact (add_comm _ _).trans hs

include hv in
/-- Any choices of representatives of the prescribed quotient bases form an ambient basis. -/
noncomputable def basisOfFlagQuotientLifts (hU : Monotone U) (hzero : U 0 = ⊥)
    (htop : U (Fin.last n) = ⊤) : Basis (Σ i, ι i) K E :=
  basisOfTopLeSpanOfCardEqFinrank (fun a ↦ (v a.1 a.2 : E)) (by
    have hs := span_flag_quotient_lifts U b v hv hU hzero (Fin.last n)
    have he : {x | ∃ i j, i.val < (Fin.last n).val ∧ (v i j : E) = x} =
        Set.range (fun a : Σ i, ι i ↦ (v a.1 a.2 : E)) := by
      ext x
      constructor
      · rintro ⟨i, j, _, rfl⟩
        exact ⟨⟨i, j⟩, rfl⟩
      · rintro ⟨⟨i, j⟩, rfl⟩
        exact ⟨i, j, i.isLt, rfl⟩
    rw [he, htop] at hs
    exact hs.ge) (by
    rw [card_flag_quotient_basis U b hU hzero, htop, finrank_top])

@[simp]
theorem basisOfFlagQuotientLifts_apply (hU : Monotone U) (hzero : U 0 = ⊥)
    (htop : U (Fin.last n) = ⊤) (i : Fin n) (j : ι i) :
    basisOfFlagQuotientLifts U b v hv hU hzero htop ⟨i, j⟩ = (v i j : E) := by
  simp [basisOfFlagQuotientLifts]

/-- The lifted basis is adapted to every term of the original flag. -/
theorem basisOfFlagQuotientLifts_span (hU : Monotone U) (hzero : U 0 = ⊥)
    (htop : U (Fin.last n) = ⊤) (k : Fin (n + 1)) :
    span K (basisOfFlagQuotientLifts U b v hv hU hzero htop ''
      {a : Σ i, ι i | a.1.val < k.val}) = U k := by
  rw [← span_flag_quotient_lifts U b v hv hU hzero k]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨i, j⟩, hij, rfl⟩
    exact ⟨i, j, hij, (basisOfFlagQuotientLifts_apply U b v hv hU hzero htop i j).symm⟩
  · rintro ⟨i, j, hij, rfl⟩
    exact ⟨⟨i, j⟩, hij, basisOfFlagQuotientLifts_apply U b v hv hU hzero htop i j⟩

omit [∀ i, Fintype (ι i)] in
/-- Chosen representatives lift all prescribed quotient bases simultaneously.
The resulting basis retains the original block indices and spans each flag step. -/
theorem exists_basis_lifting_flag_quotients (hU : Monotone U) (hzero : U 0 = ⊥)
    (htop : U (Fin.last n) = ⊤) :
    ∃ (B : Basis (Σ i, ι i) K E) (hB : ∀ i j, B ⟨i, j⟩ ∈ U i.succ),
      (∀ i j, ((U i.castSucc).comap (U i.succ).subtype).mkQ
        ⟨B ⟨i, j⟩, hB i j⟩ = b i j) ∧
      ∀ k, span K (B '' {a | a.1.val < k.val}) = U k := by
  classical
  let : ∀ i, Fintype (ι i) := fun i ↦ FiniteDimensional.fintypeBasisIndex (b i)
  let v : ∀ i, ι i → U i.succ := fun i j ↦
    Function.surjInv ((U i.castSucc).comap (U i.succ).subtype).mkQ_surjective (b i j)
  have hv : ∀ i j, ((U i.castSucc).comap (U i.succ).subtype).mkQ (v i j) = b i j :=
    fun i j ↦ Function.rightInverse_surjInv
      ((U i.castSucc).comap (U i.succ).subtype).mkQ_surjective (b i j)
  let B := basisOfFlagQuotientLifts U b v hv hU hzero htop
  have hB : ∀ i j, B ⟨i, j⟩ ∈ U i.succ := by
    intro i j
    rw [basisOfFlagQuotientLifts_apply]
    exact (v i j).property
  refine ⟨B, hB, ?_, basisOfFlagQuotientLifts_span U b v hv hU hzero htop⟩
  intro i j
  convert hv i j using 1
  congr 1
  apply Subtype.ext
  exact basisOfFlagQuotientLifts_apply U b v hv hU hzero htop i j

end Flag

section QuotientCuts

variable {n : ℕ} (U : Fin (n + 1) → Submodule K E) (hU : Monotone U)
  {ι : Fin n → Type*}
  (b : ∀ i, Basis (ι i) K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype))
  (B : Basis (Σ i, ι i) K E)
  (hmem : ∀ i j, B ⟨i, j⟩ ∈ U i.succ)
  (hquot : ∀ i j, ((U i.castSucc).comap (U i.succ).subtype).mkQ
    ⟨B ⟨i, j⟩, hmem i j⟩ = b i j)
  (hspan : ∀ k : Fin (n + 1), span K (B '' {a | a.1.val < k.val}) = U k)

include hspan in
/-- Intersecting a selected basis span with a flag step selects exactly the earlier blocks. -/
theorem span_lifted_basis_inf_flag (s : Set (Σ i, ι i)) (k : Fin (n + 1)) :
    span K (B '' s) ⊓ U k = span K (B '' (s ∩ {a | a.1.val < k.val})) := by
  rw [← hspan k]
  ext x
  simp only [mem_inf, B.mem_span_image, Set.subset_inter_iff]

include hU hquot hspan in
/-- On each actual adjacent quotient, an arbitrary selection of the lifted basis induces
exactly the same selection of its prescribed quotient basis. -/
theorem map_comap_span_lifted_basis (s : Set (Σ i, ι i)) (i : Fin n) :
    ((span K (B '' s)).comap (U i.succ).subtype).map
        ((U i.castSucc).comap (U i.succ).subtype).mkQ =
      span K (b i '' {j | (⟨i, j⟩ : Σ i, ι i) ∈ s}) := by
  let C : Set (Σ k, ι k) := s ∩ {a | a.1.val < i.succ.val}
  have hC : ∀ a : C, B a.val ∈ U i.succ := by
    intro ⟨⟨k, j⟩, ha⟩
    exact hU (by change k.val + 1 ≤ i.val + 1; exact ha.2) (hmem k j)
  let l : C → U i.succ := fun a ↦ ⟨B a.val, hC a⟩
  have he : (span K (Set.range l)).map (U i.succ).subtype =
      span K (B '' s) ⊓ U i.succ := by
    rw [span_lifted_basis_inf_flag U B hspan, map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨l ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
  have hc : (span K (B '' s)).comap (U i.succ).subtype = span K (Set.range l) := by
    have hh := congrArg (Submodule.comap (U i.succ).subtype) he
    simpa only [comap_map_eq, ker_subtype, sup_bot_eq, comap_inf,
      comap_subtype_self, inf_top_eq] using hh.symm
  rw [hc, map_span]
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    rcases a with ⟨⟨k, j⟩, ha⟩
    by_cases hki : k = i
    · subst k
      change ((U i.castSucc).comap (U i.succ).subtype).mkQ
        ⟨B ⟨i, j⟩, _⟩ ∈ _
      rw [hquot]
      exact subset_span ⟨j, ha.1, rfl⟩
    · have hki' : k.succ ≤ i.castSucc := by
        have hne : k.val ≠ i.val := fun h ↦ hki (Fin.ext h)
        have hle : k.val < i.val + 1 := ha.2
        change k.val + 1 ≤ i.val
        omega
      have hz : ((U i.castSucc).comap (U i.succ).subtype).mkQ
          (l ⟨⟨k, j⟩, ha⟩) = 0 := by
        apply (Quotient.mk_eq_zero _).mpr
        exact hU hki' (hmem k j)
      rw [hz]
      exact zero_mem _
  · apply span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    have ha : (⟨i, j⟩ : Σ k, ι k) ∈ C := ⟨hj, Nat.lt_succ_self _⟩
    apply subset_span
    refine ⟨l ⟨⟨i, j⟩, ha⟩, ⟨⟨⟨i, j⟩, ha⟩, rfl⟩, ?_⟩
    exact hquot i j

end QuotientCuts

section Weights

variable {ι : Type*} (B : Basis ι K E) (w : ι → ℝ)

/-- Weighted spans decrease with the threshold. -/
theorem antitone_span_weights : Antitone (fun t : ℝ ↦ span K (B '' {a | t ≤ w a})) := by
  intro s t hst
  exact span_mono (Set.image_mono (fun _ hi ↦ hst.trans hi))

variable [Finite ι]

/-- A finite weighted basis gives both extreme cuts, including an empty basis. -/
theorem span_weights_attains_bot_top :
    (∃ t : ℝ, span K (B '' {a | t ≤ w a}) = ⊥) ∧
    (∃ t : ℝ, span K (B '' {a | t ≤ w a}) = ⊤) := by
  obtain ⟨u, hu⟩ := (Set.finite_range w).bddAbove
  obtain ⟨l, hl⟩ := (Set.finite_range w).bddBelow
  constructor
  · refine ⟨u + 1, ?_⟩
    have he : {a | u + 1 ≤ w a} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have h := hu (Set.mem_range_self a)
      change u + 1 ≤ w a at ha
      linarith
    rw [he, Set.image_empty, span_empty]
  · refine ⟨l, ?_⟩
    have he : {a | l ≤ w a} = Set.univ :=
      Set.eq_univ_iff_forall.mpr fun a ↦ hl (Set.mem_range_self a)
    rw [he, Set.image_univ, B.span_eq]

/-- Included weighted cuts are constant on a genuine left interval at every threshold. -/
theorem span_weights_locallyConstant_left (t : ℝ) :
    ∃ ε > 0, ∀ s, t - ε < s → s ≤ t →
      span K (B '' {a | s ≤ w a}) = span K (B '' {a | t ≤ w a}) := by
  let A := Set.range w ∩ Set.Iio t
  have hA : A.Finite := (Set.finite_range w).subset Set.inter_subset_left
  have hgap : ∃ ε > 0, ∀ a, w a < t → w a ≤ t - ε := by
    by_cases hn : A.Nonempty
    · have hm : sSup A ∈ A := hn.csSup_mem hA
      refine ⟨t - sSup A, sub_pos.mpr hm.2, ?_⟩
      intro a ha
      have h := le_csSup hA.bddAbove (show w a ∈ A from ⟨Set.mem_range_self a, ha⟩)
      linarith
    · exact ⟨1, zero_lt_one, fun a ha ↦ (hn ⟨w a, Set.mem_range_self a, ha⟩).elim⟩
  obtain ⟨ε, hε, hgap⟩ := hgap
  refine ⟨ε, hε, fun s hs hst ↦ ?_⟩
  congr 2
  ext a
  constructor
  · intro ha
    by_contra ht
    have h := hgap a (lt_of_not_ge ht)
    change s ≤ w a at ha
    linarith
  · exact fun ha ↦ hst.trans ha

end Weights

section WeightedLift

variable [FiniteDimensional K E] {n : ℕ}
  (U : Fin (n + 1) → Submodule K E) (hU : Monotone U) (hzero : U 0 = ⊥)
  (htop : U (Fin.last n) = ⊤) {ι : Fin n → Type*}
  (b : ∀ i, Basis (ι i) K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype))
  (w : ∀ i, ι i → ℝ)

include hU hzero htop in
/-- Prescribed weighted quotient bases lift without changing a single weight.
Every threshold on the actual quotient agrees with its prescribed weighted span. -/
theorem exists_basis_lifting_weighted_quotients :
    ∃ (B : Basis (Σ i, ι i) K E) (hB : ∀ i j, B ⟨i, j⟩ ∈ U i.succ),
      (∀ i j, ((U i.castSucc).comap (U i.succ).subtype).mkQ
        ⟨B ⟨i, j⟩, hB i j⟩ = b i j) ∧
      (∀ k : Fin (n + 1), span K (B '' {a | a.1.val < k.val}) = U k) ∧
      ∀ i t, ((span K (B '' {a | t ≤ w a.1 a.2})).comap (U i.succ).subtype).map
        ((U i.castSucc).comap (U i.succ).subtype).mkQ =
          span K (b i '' {j | t ≤ w i j}) := by
  obtain ⟨B, hB, hquot, hspan⟩ := exists_basis_lifting_flag_quotients U b hU hzero htop
  exact ⟨B, hB, hquot, hspan, fun i t ↦
    map_comap_span_lifted_basis U hU b B hB hquot hspan {a | t ≤ w a.1 a.2} i⟩

end WeightedLift

/-- A basis adapted to a flag is also adapted to its decreasing block weights. -/
theorem iSup_flag_eq_span_weights {n : ℕ} {ι : Fin n → Type*}
    (U : Fin (n + 1) → Submodule K E) (B : Basis (Σ i, ι i) K E)
    (hspan : ∀ k : Fin (n + 1), span K (B '' {a | a.1.val < k.val}) = U k)
    (a : Fin n → ℝ) (ha : Antitone a) (t : ℝ) :
    (⨆ (i : Fin n) (_ : t ≤ a i), U i.succ) =
      span K (B '' {j | t ≤ a j.1}) := by
  apply le_antisymm
  · refine iSup_le fun i ↦ iSup_le fun hi ↦ ?_
    rw [← hspan i.succ]
    apply span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    apply subset_span
    refine ⟨j, hi.trans (ha ?_), rfl⟩
    exact Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ hj)
  · apply span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    apply le_iSup_of_le j.1
    apply le_iSup_of_le hj
    rw [← hspan j.1.succ]
    exact subset_span ⟨j, Nat.lt_succ_self _, rfl⟩

end Submodule
