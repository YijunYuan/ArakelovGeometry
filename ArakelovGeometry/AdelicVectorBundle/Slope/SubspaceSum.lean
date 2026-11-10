/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic
import ArakelovGeometry.AdelicVectorBundle.Degree.Supermodular
import ArakelovGeometry.AdelicVectorBundle.Slope.Extension
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Minimal slope of an actual subspace sum

Every nonzero quotient of the actual sum detects a genuine summand. Its rational
inclusion followed by the quotient contracts the actual completed norms. The
nonzero-map slope inequality and actual quotient infimum then preserve any
common real lower bound for the minimal slopes of the summands.
No Hermitian hypothesis or nonempty-family premise is required.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

universe u v w w' w''

variable {K : Type u} [Field K] {E : Type w} [AddCommGroup E] [Module K E]
  {F : Type w'} [AddCommGroup F] [Module K F]

namespace Submodule

/-- A nonzero map out of the actual sum of subspaces is nonzero on a
genuine summand, with its canonical rational inclusion. -/
theorem exists_ne_zero_comp_inclusion_iSup {ι : Type w''} (U : ι → Submodule K E)
    (f : ↥(⨆ i, U i) →ₗ[K] F) (hf : f ≠ 0) :
    ∃ i, f.comp (Submodule.inclusion (le_iSup U i)) ≠ 0 := by
  obtain ⟨W, ⟨i, rfl⟩, hi⟩ :=
    LinearMap.exists_ne_zero_of_sSup_eq hf (Set.range U) sSup_range
  exact ⟨i, hi⟩


end Submodule

namespace ArakelovGeometry

variable {S : AdelicStructure.{u, v} K}

namespace NormFamily

variable [FiniteDimensional K E]

/-- A canonical inclusion followed by a true quotient contracts the actual
completed restriction norms. -/
theorem quotient_after_inclusion_norm_le (ξ : NormFamily S E)
    (U W : Submodule K E) (hUW : U ≤ W) (T : Submodule K W) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] U) :
    ((ξ.restrict W).quotient T).norm ω
        ((T.mkQ.comp (Submodule.inclusion hUW)).baseChange (S.ϕ ω).Completion z) ≤
      (ξ.restrict U).norm ω z := by
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply]
  apply ((ξ.restrict W).quotient_norm_mk_le T ω _).trans_eq
  have hc : W.subtype.comp (Submodule.inclusion hUW) = U.subtype :=
    Submodule.subtype_comp_inclusion U W hUW
  have hz := DFunLike.congr_fun
    (congrArg (fun f ↦ f.baseChange (S.ϕ ω).Completion) hc) z
  simpa only [restrict_norm, LinearMap.baseChange_comp, LinearMap.comp_apply] using
    congrArg (ξ.norm ω) hz


end NormFamily

namespace AdelicVectorBundle

variable [S.IsProper] [FiniteDimensional K E]

/-- Arbitrary sums of actual restricted subspaces preserve a common lower
bound on their actual minimal slopes. Zero summands and an empty family are allowed. -/
theorem minimalSlope_restrict_iSup_ge (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    {ι : Type w''} (U : ι → Submodule K E) (a : ℝ)
    (hU : ∀ i, (a : EReal) ≤ (V.restrictOfMeasurableBase (U i) hS).minimalSlope hS hN) :
    (a : EReal) ≤ (V.restrictOfMeasurableBase (⨆ i, U i) hS).minimalSlope hS hN := by
  let W : Submodule K E := ⨆ i, U i
  let B := V.restrictOfMeasurableBase W hS
  apply B.le_minimalSlope hS hN
  intro T hT
  have hq : T.mkQ ≠ 0 := by
    intro hzero
    have hker : T = ⊤ := by
      apply top_unique
      intro x _
      exact (Submodule.Quotient.mk_eq_zero T).mp (DFunLike.congr_fun hzero x)
    have hd := T.finrank_quotient_add_finrank
    have hdimT : Module.finrank K T = Module.finrank K W := by
      rw [hker, finrank_top]
    rw [hdimT] at hd
    omega
  obtain ⟨i, hi⟩ := Submodule.exists_ne_zero_comp_inclusion_iSup U T.mkQ hq
  let f := T.mkQ.comp (Submodule.inclusion (le_iSup U i))
  let A := V.restrictOfMeasurableBase (U i) hS
  let Q := B.quotientOfMeasurableBase T hS
  have hh : A.mapHeight Q f ≤ 0 := by
    apply mapHeight_le_zero_of_completed_contraction
    intro ω z
    exact V.toNormFamily.quotient_after_inclusion_norm_le (U i) W (le_iSup U i) T ω z
  have hm := A.minimalSlope_sub_mapHeight_le_maximalSlope_of_ne_zero Q hS hN f hi
  calc
    (a : EReal) ≤ A.minimalSlope hS hN := hU i
    _ = A.minimalSlope hS hN - 0 := by simp
    _ ≤ A.minimalSlope hS hN - A.mapHeight Q f := EReal.sub_le_sub le_rfl hh
    _ ≤ Q.maximalSlope hS hN := hm


end AdelicVectorBundle

end ArakelovGeometry

end
