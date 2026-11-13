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

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace AdelicVectorBundle

/-- The actual successive quotient bundle of a finite rational flag. -/
noncomputable abbrev flagQuotientOfMeasurableBase (V : AdelicVectorBundle S)
    {n : ℕ} (F : Fin (n + 1) → Submodule K V)
    [hS : S.HasMeasurableBase] (i : Fin n) :
    AdelicVectorBundle S :=
  (V.restrictOfMeasurableBase (F i.succ)).quotientOfMeasurableBase
    ((F i.castSucc).comap (F i.succ).subtype)

/-- Successive quotient degrees are bounded by the degree of the final
restricted bundle for every finite monotone flag starting at zero. -/
theorem sum_flagQuotient_degree_le_restrict [S.IsProper] (V : AdelicVectorBundle S)
    {n : ℕ} (F : Fin (n + 1) → Submodule K V) (hF : Monotone F) (hzero : F 0 = ⊥)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (∑ i : Fin n, (V.flagQuotientOfMeasurableBase F i).degree) ≤
      (V.restrictOfMeasurableBase (F (Fin.last n))).degree := by
  induction n with
  | zero =>
      have hz : F (Fin.last 0) = ⊥ := hzero
      have hr : Module.finrank K (F (Fin.last 0)) = 0 := by
        rw [hz]
        exact finrank_bot K V
      have hd := degree_eq_zero_of_finrank_eq_zero
        (V.restrictOfMeasurableBase (F (Fin.last 0))) hr
      simp only [Fin.sum_univ_zero, hd, le_refl]
  | succ n ih =>
      let G : Fin (n + 1) → Submodule K V := fun i ↦ F i.castSucc
      let U : Submodule K V := F (Fin.last n).castSucc
      let W : Submodule K V := F (Fin.last (n + 1))
      have hG : Monotone G := hF.comp Fin.strictMono_castSucc.monotone
      have hzG : G 0 = ⊥ := hzero
      have hprefix := ih G hG hzG
      change (∑ i : Fin n,
        (V.flagQuotientOfMeasurableBase F i.castSucc).degree) ≤
          (V.restrictOfMeasurableBase U).degree at hprefix
      have hUW : U ≤ W := hF (Fin.le_last _)
      have hstep := degree_restrict_add_degree_quotient_le
        (V.restrictOfMeasurableBase W) (U.comap W.subtype)
      rw [V.degree_restrict_restrict U W hUW] at hstep
      change (V.restrictOfMeasurableBase U).degree +
        (V.flagQuotientOfMeasurableBase F (Fin.last n)).degree ≤
          (V.restrictOfMeasurableBase W).degree at hstep
      rw [Fin.sum_univ_castSucc]
      exact (add_le_add_left hprefix _).trans hstep

/-- The lower degree inequality for a complete finite flag, with no strictness
or positive-rank assumption on its successive quotients. -/
theorem sum_flagQuotient_degree_le [S.IsProper] (V : AdelicVectorBundle S)
    {n : ℕ} (F : Fin (n + 1) → Submodule K V) (hF : Monotone F) (hzero : F 0 = ⊥)
    (htop : F (Fin.last n) = ⊤)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (∑ i : Fin n, (V.flagQuotientOfMeasurableBase F i).degree) ≤
      V.degree := by
  calc
    _ ≤ (V.restrictOfMeasurableBase (F (Fin.last n))).degree :=
      V.sum_flagQuotient_degree_le_restrict F hF hzero
    _ = V.degree := by
      rw [htop, V.degree_restrict_top]

end AdelicVectorBundle

end ArakelovGeometry
