/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.FieldTheory.AlgebraicClosure

import Mathlib.Algebra.AlgebraicCard
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Countable density in an algebraic closure

The canonical relative algebraic closure of a common countable dense subfield
is countable. Polynomial coefficient approximation and actual roots supply
its density in every extending completion, without a separability assumption.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry

universe u v

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

/-- The canonical relative algebraic closure of a countable subfield is countable. -/
theorem countable_algebraicClosure_subfield (K₀ : Subfield K) [Countable K₀] :
    Countable (algebraicClosure K₀ L).toSubfield := by
  have hc : ((algebraicClosure K₀ L).toSubfield : Set L).Countable := by
    apply (Algebraic.countable K₀ L).mono
    intro a ha
    exact mem_algebraicClosure_iff.mp ha
  exact hc.to_subtype

/-- Countability is canonical for the relative algebraic closure of a countable subfield.
The subfield occurs in the target, so instance search can recover every parameter. -/
instance (K₀ : Subfield K) [Countable K₀] :
    Countable (algebraicClosure K₀ L).toSubfield :=
  countable_algebraicClosure_subfield K₀

/-- A small monic evaluation produces an actual nearby root, counting multiplicities.
No positive-degree or nontrivial-valuation hypothesis is needed. -/
theorem exists_root_abv_sub_lt (w : AbsoluteValue L ℝ)
    (p : Polynomial L) (hp : p.Monic) (hs : p.Splits)
    (a : L) (ε : ℝ) (hε : 0 < ε) (ha : w (p.eval a) < ε ^ p.natDegree) :
    ∃ b ∈ p.roots, w (a - b) < ε := by
  classical
  by_contra! hn
  have hl : ∀ m : Multiset L, (∀ b ∈ m, ε ≤ w (a - b)) →
      ε ^ m.card ≤ (m.map (fun b => w (a - b))).prod := by
    intro m
    induction m using Multiset.induction_on with
    | empty => simp
    | cons b m ih =>
      intro hm
      have hb := hm b (Multiset.mem_cons_self _ _)
      have hrest := ih (fun c hc => hm c (Multiset.mem_cons_of_mem hc))
      simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, pow_succ]
      rw [mul_comm (ε ^ m.card) ε]
      exact mul_le_mul hb hrest (pow_nonneg hε.le _) (w.nonneg _)
  have hprod : w (p.eval a) = (p.roots.map (fun b => w (a - b))).prod := by
    rw [hs.eval_eq_prod_roots_of_monic hp a]
    change w.toMonoidWithZeroHom (p.roots.map (fun b => a - b)).prod =
      (p.roots.map (fun b => w (a - b))).prod
    rw [map_multiset_prod, Multiset.map_map]
    rfl
  have ht := hl p.roots hn
  rw [← hs.natDegree_eq_card_roots, ← hprod] at ht
  exact (not_lt_of_ge ht) ha

end ArakelovGeometry
