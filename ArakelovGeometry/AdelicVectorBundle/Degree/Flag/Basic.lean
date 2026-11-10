/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Countable
public import ArakelovGeometry.AdelicVectorBundle.Degree.Basic
import ArakelovGeometry.AdelicVectorBundle.Degree.ExactSequence.Basic
import ArakelovGeometry.AdelicVectorBundle.Subquotient.Restriction.Functor
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# The lower degree inequality for finite flags

Every successive quotient carries the actual restriction followed by the
actual quotient norm. Monotone flags may have repeated terms, and the empty
flag segment uses the scalar unit determinant of the zero space.
-/

@[expose] public section

open scoped BigOperators

namespace ArakelovGeometry

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace AdelicVectorBundle

/-- The actual successive quotient bundle of a finite rational flag. -/
noncomputable def flagQuotientOfMeasurableBase (V : AdelicVectorBundle S E)
    {n : ℕ} (F : Fin (n + 1) → Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) (i : Fin n) :
    AdelicVectorBundle S ((F i.succ) ⧸ ((F i.castSucc).comap (F i.succ).subtype)) :=
  (V.restrictOfMeasurableBase (F i.succ) hS).quotientOfMeasurableBase
    ((F i.castSucc).comap (F i.succ).subtype) hS

/-- Successive quotient degrees are bounded by the degree of the final
restricted bundle for every finite monotone flag starting at zero. -/
theorem sum_flagQuotient_degree_le_restrict [S.IsProper] (V : AdelicVectorBundle S E)
    {n : ℕ} (F : Fin (n + 1) → Submodule K E) (hF : Monotone F) (hzero : F 0 = ⊥)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (∑ i : Fin n, (V.flagQuotientOfMeasurableBase F hS i).degree hS hN) ≤
      (V.restrictOfMeasurableBase (F (Fin.last n)) hS).degree hS hN := by
  induction n with
  | zero =>
      have hz : F (Fin.last 0) = ⊥ := hzero
      have hr : Module.finrank K (F (Fin.last 0)) = 0 := by
        rw [hz]
        exact finrank_bot K E
      have hd := degree_eq_zero_of_finrank_eq_zero
        (V.restrictOfMeasurableBase (F (Fin.last 0)) hS) hS hN hr
      simp only [Fin.sum_univ_zero, hd, le_refl]
  | succ n ih =>
      let G : Fin (n + 1) → Submodule K E := fun i ↦ F i.castSucc
      let U : Submodule K E := F (Fin.last n).castSucc
      let W : Submodule K E := F (Fin.last (n + 1))
      have hG : Monotone G := hF.comp Fin.strictMono_castSucc.monotone
      have hzG : G 0 = ⊥ := hzero
      have hprefix := ih G hG hzG
      change (∑ i : Fin n,
        (V.flagQuotientOfMeasurableBase F hS i.castSucc).degree hS hN) ≤
          (V.restrictOfMeasurableBase U hS).degree hS hN at hprefix
      have hUW : U ≤ W := hF (Fin.le_last _)
      have hstep := degree_restrict_add_degree_quotient_le
        (V.restrictOfMeasurableBase W hS) (U.comap W.subtype) hS hN
      rw [V.degree_restrict_restrict U W hUW hS hN] at hstep
      change (V.restrictOfMeasurableBase U hS).degree hS hN +
        (V.flagQuotientOfMeasurableBase F hS (Fin.last n)).degree hS hN ≤
          (V.restrictOfMeasurableBase W hS).degree hS hN at hstep
      rw [Fin.sum_univ_castSucc]
      exact (add_le_add_left hprefix _).trans hstep

/-- The lower degree inequality for a complete finite flag, with no strictness
or positive-rank assumption on its successive quotients. -/
theorem sum_flagQuotient_degree_le [S.IsProper] (V : AdelicVectorBundle S E)
    {n : ℕ} (F : Fin (n + 1) → Submodule K E) (hF : Monotone F) (hzero : F 0 = ⊥)
    (htop : F (Fin.last n) = ⊤)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (∑ i : Fin n, (V.flagQuotientOfMeasurableBase F hS i).degree hS hN) ≤
      V.degree hS hN := by
  calc
    _ ≤ (V.restrictOfMeasurableBase (F (Fin.last n)) hS).degree hS hN :=
      V.sum_flagQuotient_degree_le_restrict F hF hzero hS hN
    _ = V.degree hS hN := by
      rw [htop, V.degree_restrict_top hS hN]

end AdelicVectorBundle

end ArakelovGeometry
