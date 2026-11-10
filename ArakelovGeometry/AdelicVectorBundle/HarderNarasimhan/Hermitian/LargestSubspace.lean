/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Basic
import ArakelovGeometry.AdelicVectorBundle.Degree.Supermodular
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Functoriality
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Truncations
import ArakelovGeometry.AdelicVectorBundle.Slope.Extension
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# The actual HN threshold as the largest subspace of prescribed minimal slope

Actual quotient contractivity and the HN truncation slope bounds show that a
bundle of minimal slope at least a threshold is retained in full. Actual HN
functoriality for the true restricted inclusion then gives the largest-subspace
and nonzero-subspace sum characterizations of source Corollary 4.3.43.
The zero subspace has minimal slope top and the empty sum is zero.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type (max u w)} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace AdelicVectorBundle

variable [S.IsProper] (V : AdelicVectorBundle S E)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hV : V.toNormFamily.IsHermitian hN)
include hS hN hV

/-- If the actual minimal slope is at least the threshold, the actual HN
threshold subspace is the whole space, including the zero-dimensional case. -/
theorem hermitianHNFiltration_eq_top_of_le_minimalSlope (t : ℝ)
    (ht : (t : EReal) ≤ V.minimalSlope hS hN) :
    V.hermitianHNFiltration hS hN hV t = ⊤ := by
  let T := V.hermitianHNFiltration hS hN hV t
  let Q := V.quotientOfMeasurableBase T hS
  have hm : T.mkQ = 0 := by
    by_contra hm
    have hmap := V.minimalSlope_sub_mapHeight_le_maximalSlope_of_ne_zero Q hS hN T.mkQ hm
    have hheight : V.mapHeight Q T.mkQ ≤ 0 := by
      apply mapHeight_le_zero_of_completed_contraction
      intro ω z
      exact V.toNormFamily.quotient_norm_mk_le T ω z
    have hlo : (t : EReal) ≤ V.minimalSlope hS hN - V.mapHeight Q T.mkQ := by
      calc
        (t : EReal) ≤ V.minimalSlope hS hN := ht
        _ = V.minimalSlope hS hN - 0 := by simp
        _ ≤ V.minimalSlope hS hN - V.mapHeight Q T.mkQ :=
          EReal.sub_le_sub le_rfl hheight
    exact (not_le_of_gt
      (V.maximalSlope_quotient_hermitianHNFiltration_lt hS hN hV t)) (hlo.trans hmap)
  apply top_unique
  intro x _
  exact (Submodule.Quotient.mk_eq_zero T).mp (DFunLike.congr_fun hm x)

/-- Every actual restricted subspace with minimal slope at least the
threshold lies in the actual HN threshold subspace. -/
theorem le_hermitianHNFiltration_of_le_minimalSlope_restrict (U : Submodule K E) (t : ℝ)
    (ht : (t : EReal) ≤ (V.restrictOfMeasurableBase U hS).minimalSlope hS hN) :
    U ≤ V.hermitianHNFiltration hS hN hV t := by
  by_cases hf : U.subtype = 0
  · intro x hx
    have he : x = 0 := DFunLike.congr_fun hf (⟨x, hx⟩ : U)
    exact he ▸ Submodule.zero_mem _
  · have htop := hermitianHNFiltration_eq_top_of_le_minimalSlope
      (V.restrictOfMeasurableBase U hS) hS hN (hV.restrict U) t ht
    have hh : (V.restrictOfMeasurableBase U hS).mapHeight V U.subtype ≤ 0 := by
      apply mapHeight_le_zero_of_completed_contraction
      intro ω z
      exact le_rfl
    have hfun := map_hermitianHNFiltration_le_of_mapHeight_le
      (V.restrictOfMeasurableBase U hS) V hS hN (hV.restrict U) hV U.subtype hf 0 hh t
    simpa only [sub_zero, htop, Submodule.map_top, Submodule.range_subtype] using hfun

/-- The actual HN threshold subspace is the greatest rational subspace
with actual restricted minimal slope at least the threshold. -/
theorem isGreatest_hermitianHNFiltration (t : ℝ) :
    IsGreatest {U : Submodule K E |
      (t : EReal) ≤ (V.restrictOfMeasurableBase U hS).minimalSlope hS hN}
      (V.hermitianHNFiltration hS hN hV t) := by
  refine ⟨V.le_minimalSlope_restrict_hermitianHNFiltration hS hN hV t, ?_⟩
  intro U hU
  exact V.le_hermitianHNFiltration_of_le_minimalSlope_restrict hS hN hV U t hU

/-- The actual HN threshold subspace is the sum of all rational subspaces
whose actual restricted minimal slope is at least the threshold. -/
theorem hermitianHNFiltration_eq_iSup_minimalSlope (t : ℝ) :
    V.hermitianHNFiltration hS hN hV t =
      ⨆ (U : Submodule K E)
        (_ : (t : EReal) ≤ (V.restrictOfMeasurableBase U hS).minimalSlope hS hN), U := by
  apply le_antisymm
  · exact le_iSup_of_le (V.hermitianHNFiltration hS hN hV t)
      (le_iSup_of_le (V.le_minimalSlope_restrict_hermitianHNFiltration hS hN hV t) le_rfl)
  · exact iSup_le fun U ↦ iSup_le fun hU ↦
      V.le_hermitianHNFiltration_of_le_minimalSlope_restrict hS hN hV U t hU

/-- The source's sum over nonzero eligible subspaces equals the actual HN
threshold subspace. An empty eligible family contributes the zero subspace. -/
theorem hermitianHNFiltration_eq_iSup_nonzero_minimalSlope (t : ℝ) :
    V.hermitianHNFiltration hS hN hV t =
      ⨆ (U : Submodule K E) (_ : U ≠ ⊥)
        (_ : (t : EReal) ≤ (V.restrictOfMeasurableBase U hS).minimalSlope hS hN), U := by
  apply le_antisymm
  · by_cases hzero : V.hermitianHNFiltration hS hN hV t = ⊥
    · rw [hzero]
      exact bot_le
    · exact le_iSup_of_le (V.hermitianHNFiltration hS hN hV t)
        (le_iSup_of_le hzero (le_iSup_of_le
          (V.le_minimalSlope_restrict_hermitianHNFiltration hS hN hV t) le_rfl))
  · exact iSup_le fun U ↦ iSup_le fun _ ↦ iSup_le fun hU ↦
      V.le_hermitianHNFiltration_of_le_minimalSlope_restrict hS hN hV U t hU


end AdelicVectorBundle

end

end ArakelovGeometry
