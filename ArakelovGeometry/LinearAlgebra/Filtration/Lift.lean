/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

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

end Submodule
