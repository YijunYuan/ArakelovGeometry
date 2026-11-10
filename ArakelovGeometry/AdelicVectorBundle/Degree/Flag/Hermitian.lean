/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.Basic
import ArakelovGeometry.AdelicVectorBundle.Degree.ExactSequence.Dual
import ArakelovGeometry.AdelicVectorBundle.Subquotient.Restriction.Functor
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Degree additivity for actual Hermitian finite flags

Every step uses Hermitianity of the actual restricted bundle, the genuine
two-step degree identity, and the canonical nested restriction isometry.
Empty flag segments and repeated subspaces are included.
-/

@[expose] public section

open scoped BigOperators

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The actual successive quotient degrees of a Hermitian flag sum to the
degree of its final restricted bundle, without strict-inclusion assumptions. -/
theorem sum_flagQuotient_degree_eq_restrict_of_isHermitian [S.IsProper]
    (V : AdelicVectorBundle S E) {n : ℕ} (F : Fin (n + 1) → Submodule K E)
    (hF : Monotone F) (hzero : F 0 = ⊥)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) :
    (∑ i : Fin n, (V.flagQuotientOfMeasurableBase F hS i).degree hS hN) =
      (V.restrictOfMeasurableBase (F (Fin.last n)) hS).degree hS hN := by
  induction n with
  | zero =>
      have hz : F (Fin.last 0) = ⊥ := hzero
      have hr : Module.finrank K (F (Fin.last 0)) = 0 := by
        rw [hz]
        exact finrank_bot K E
      have hd := degree_eq_zero_of_finrank_eq_zero
        (V.restrictOfMeasurableBase (F (Fin.last 0)) hS) hS hN hr
      simp only [Fin.sum_univ_zero, hd]
  | succ n ih =>
      let G : Fin (n + 1) → Submodule K E := fun i ↦ F i.castSucc
      let U : Submodule K E := F (Fin.last n).castSucc
      let W : Submodule K E := F (Fin.last (n + 1))
      have hG : Monotone G := hF.comp Fin.strictMono_castSucc.monotone
      have hzG : G 0 = ⊥ := hzero
      have hprefix := ih G hG hzG
      change (∑ i : Fin n,
        (V.flagQuotientOfMeasurableBase F hS i.castSucc).degree hS hN) =
          (V.restrictOfMeasurableBase U hS).degree hS hN at hprefix
      have hUW : U ≤ W := hF (Fin.le_last _)
      have hHW : (V.restrictOfMeasurableBase W hS).toNormFamily.IsHermitian hN := by
        simpa only [restrictOfMeasurableBase_toNormFamily] using hV.restrict W
      have hstep := degree_restrict_add_degree_quotient_eq_of_isHermitian
        (V.restrictOfMeasurableBase W hS) (U.comap W.subtype) hS hN hHW
      rw [V.degree_restrict_restrict U W hUW hS hN] at hstep
      change (V.restrictOfMeasurableBase U hS).degree hS hN +
        (V.flagQuotientOfMeasurableBase F hS (Fin.last n)).degree hS hN =
          (V.restrictOfMeasurableBase W hS).degree hS hN at hstep
      rw [Fin.sum_univ_castSucc, hprefix]
      exact hstep

/-- Exact degree additivity for a complete actual Hermitian finite flag. -/
theorem sum_flagQuotient_degree_eq_of_isHermitian [S.IsProper]
    (V : AdelicVectorBundle S E) {n : ℕ} (F : Fin (n + 1) → Submodule K E)
    (hF : Monotone F) (hzero : F 0 = ⊥) (htop : F (Fin.last n) = ⊤)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) :
    (∑ i : Fin n, (V.flagQuotientOfMeasurableBase F hS i).degree hS hN) =
      V.degree hS hN := by
  calc
    _ = (V.restrictOfMeasurableBase (F (Fin.last n)) hS).degree hS hN :=
      V.sum_flagQuotient_degree_eq_restrict_of_isHermitian F hF hzero hS hN hV
    _ = V.degree hS hN := by
      rw [htop, V.degree_restrict_top hS hN]

end ArakelovGeometry.AdelicVectorBundle
