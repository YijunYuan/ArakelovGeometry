/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Basic
public import ArakelovGeometry.AdelicVectorBundle.Slope.Subquotient

import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.LargestSubspace
import ArakelovGeometry.AdelicVectorBundle.Slope.Finite
import ArakelovGeometry.AdelicVectorBundle.Slope.Quotient
import ArakelovGeometry.AdelicVectorBundle.Slope.SubspaceSum
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# The general Harder–Narasimhan filtration

For a real threshold, take the sum of nonzero subspaces whose restricted minimal
slope is at least that threshold. Stability of this condition under sums gives
the largest such subspace. The epsilon-intersection construction then defines the
real-indexed filtration of Chen–Moriwaki, Definition 4.3.45 and equation (4.65).

The construction uses minimal slopes of restricted norm families and requires the
stated properness, measurable-base and Archimedean normalization hypotheses.
It applies without a Hermitian assumption. The comparison with mean-slope
semistability is established in the Hermitian theory.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace AdelicVectorBundle

variable [S.IsProper] (V : AdelicVectorBundle S)
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]

/-- The actual sum in source Definition 4.3.45. Only nonzero rational
subspaces with the actual restricted minimum-slope bound occur. -/
def generalHNSlopeSum (t : ℝ) : Submodule K V :=
  ⨆ (U : Submodule K V) (_ : U ≠ ⊥)
    (_ : (t : EReal) ≤ (V.restrictOfMeasurableBase U).minimalSlope), U

/-- Source equation (4.65), with the actual epsilon-intersection. -/
def generalHNFiltration (t : ℝ) : Submodule K V :=
  ⨅ (ε : ℝ) (_ : 0 < ε), V.generalHNSlopeSum (t - ε)

/-- The source's two infinite endpoint conventions, keeping real levels
in the actual epsilon-intersection definition. -/
def generalHNFiltrationExtended : EReal → Submodule K V :=
  EReal.rec ⊤ (V.generalHNFiltration) ⊥

@[simp] theorem generalHNFiltrationExtended_bot :
    V.generalHNFiltrationExtended ⊥ = ⊤ := rfl

@[simp] theorem generalHNFiltrationExtended_top :
    V.generalHNFiltrationExtended ⊤ = ⊥ := rfl

@[simp] theorem generalHNFiltrationExtended_coe (t : ℝ) :
    V.generalHNFiltrationExtended (t : EReal) =
      V.generalHNFiltration t := rfl

/-- A higher threshold has fewer eligible summands. -/
theorem antitone_generalHNSlopeSum : Antitone (V.generalHNSlopeSum) := by
  intro s t hst
  apply iSup_le
  intro U
  apply iSup_le
  intro hU
  apply iSup_le
  intro ht
  exact le_iSup_of_le U (le_iSup_of_le hU (le_iSup_of_le
    ((EReal.coe_le_coe hst).trans ht) le_rfl))

/-- The source epsilon-intersection is decreasing in its real parameter. -/
theorem antitone_generalHNFiltration : Antitone (V.generalHNFiltration) := by
  intro s t hst
  exact iInf_mono fun ε ↦ iInf_mono fun _ ↦
    V.antitone_generalHNSlopeSum (sub_le_sub_right hst ε)

/-- The exact-threshold sum lies in every positive-epsilon term. -/
theorem generalHNSlopeSum_le_generalHNFiltration (t : ℝ) :
    V.generalHNSlopeSum t ≤ V.generalHNFiltration t := by
  apply le_iInf
  intro ε
  apply le_iInf
  intro hε
  exact V.antitone_generalHNSlopeSum (sub_le_self t hε.le)

/-- Finite dimension forces the actual positive-epsilon cone to stabilize
at its intersection. No finite image, flag, or slope attainment is supplied. -/
theorem exists_generalHNFiltration_stabilizes (t : ℝ) :
    ∃ δ > 0, ∀ ε, 0 < ε → ε ≤ δ →
      V.generalHNSlopeSum (t - ε) = V.generalHNFiltration t := by
  classical
  let P : ℕ → Prop := fun n ↦ ∃ δ > 0,
    Module.finrank K (V.generalHNSlopeSum (t - δ)) = n
  have hex : ∃ n, P n := ⟨_, 1, zero_lt_one, rfl⟩
  obtain ⟨δ, hδ, hdim⟩ := Nat.find_spec hex
  have hsmall : ∀ ε, 0 < ε → ε ≤ δ →
      V.generalHNSlopeSum (t - ε) = V.generalHNSlopeSum (t - δ) := by
    intro ε hε hεδ
    have hle := V.antitone_generalHNSlopeSum (sub_le_sub_left hεδ t)
    apply Submodule.eq_of_le_of_finrank_eq hle
    apply Nat.le_antisymm (Submodule.finrank_mono hle)
    rw [hdim]
    exact Nat.find_min' hex ⟨ε, hε, rfl⟩
  have hintersection : V.generalHNFiltration t =
      V.generalHNSlopeSum (t - δ) := by
    apply le_antisymm
    · exact iInf_le_of_le δ (iInf_le_of_le hδ le_rfl)
    · apply le_iInf
      intro ε
      apply le_iInf
      intro hε
      by_cases hεδ : ε ≤ δ
      · exact le_of_eq (hsmall ε hε hεδ).symm
      · exact V.antitone_generalHNSlopeSum
          (sub_le_sub_left (le_of_not_ge hεδ) t)
  exact ⟨δ, hδ, fun ε hε hεδ ↦ (hsmall ε hε hεδ).trans hintersection.symm⟩

/-- In rank zero the actual source sum has no eligible nonzero summands. -/
theorem generalHNSlopeSum_eq_bot_of_finrank_eq_zero
    (hr : Module.finrank K V = 0) (t : ℝ) : V.generalHNSlopeSum t = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro U
  apply iSup_le
  intro hU
  have hz : Module.finrank K U = 0 := Nat.eq_zero_of_le_zero (hr ▸ U.finrank_le)
  exact False.elim (hU (Submodule.finrank_eq_zero.mp hz))

/-- The actual epsilon intersection is zero at every real level in rank zero. -/
theorem generalHNFiltration_eq_bot_of_finrank_eq_zero
    (hr : Module.finrank K V = 0) (t : ℝ) : V.generalHNFiltration t = ⊥ := by
  apply bot_unique
  exact iInf_le_of_le 1 (iInf_le_of_le zero_lt_one
    (le_of_eq (V.generalHNSlopeSum_eq_bot_of_finrank_eq_zero hr (t - 1))))


/-- Above the actual ambient maximal slope there are no nonzero eligible
summands: each restricted minimum is at most its mean and the ambient maximum. -/
theorem generalHNSlopeSum_eq_bot_of_maximalSlope_lt (t : ℝ)
    (ht : V.maximalSlope < (t : EReal)) : V.generalHNSlopeSum t = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro U
  apply iSup_le
  intro hU
  apply iSup_le
  intro hmin
  have hrU : 0 < Module.finrank K U := Nat.pos_of_ne_zero
    (fun hz ↦ hU (Submodule.finrank_eq_zero.mp hz))
  have hbound := ((V.restrictOfMeasurableBase U).minimalSlope_le_slope hrU).trans
    (V.slope_restrict_le_maximalSlope U hrU)
  exact False.elim ((not_le_of_gt ht) (hmin.trans hbound))

/-- The ambient bundle itself supplies a top summand at every threshold
below its minimum. The zero-rank case retains the empty source sum. -/
theorem generalHNSlopeSum_eq_top_of_le_minimalSlope (t : ℝ)
    (ht : (t : EReal) ≤ V.minimalSlope) : V.generalHNSlopeSum t = ⊤ := by
  by_cases hr : Module.finrank K V = 0
  · have htop : (⊤ : Submodule K V) = ⊥ := Submodule.finrank_eq_zero.mp
      (by simpa only [finrank_top] using hr)
    exact (V.generalHNSlopeSum_eq_bot_of_finrank_eq_zero hr t).trans htop.symm
  · apply top_unique
    have htop : (⊤ : Submodule K V) ≠ ⊥ := fun hz ↦ hr
      (by simpa only [finrank_top] using (Submodule.finrank_eq_zero.mpr hz))
    exact le_iSup_of_le ⊤ (le_iSup_of_le htop (le_iSup_of_le
      (by simpa only [V.minimalSlope_restrict_top] using ht) le_rfl))

/-- The whole ambient bundle lies in the actual epsilon intersection at
every threshold below its actual minimum. -/
theorem generalHNFiltration_eq_top_of_le_minimalSlope (t : ℝ)
    (ht : (t : EReal) ≤ V.minimalSlope) : V.generalHNFiltration t = ⊤ := by
  apply top_unique
  rw [← V.generalHNSlopeSum_eq_top_of_le_minimalSlope t ht]
  exact V.generalHNSlopeSum_le_generalHNFiltration t

/-- Above the actual maximal slope, one positive-epsilon term of the
intersection is already zero. Infinite zero-rank extrema are kept explicit. -/
theorem generalHNFiltration_eq_bot_of_maximalSlope_lt (t : ℝ)
    (ht : V.maximalSlope < (t : EReal)) : V.generalHNFiltration t = ⊥ := by
  by_cases hr : Module.finrank K V = 0
  · exact V.generalHNFiltration_eq_bot_of_finrank_eq_zero hr t
  · obtain ⟨c, hc⟩ := V.exists_maximalSlope_eq_coe (Nat.pos_of_ne_zero hr)
    have hct : c < t := EReal.coe_lt_coe_iff.mp (hc ▸ ht)
    let ε := (t - c) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hsmall : V.maximalSlope < ((t - ε : ℝ) : EReal) := by
      rw [hc]
      apply EReal.coe_lt_coe
      dsimp [ε]
      linarith
    apply bot_unique
    exact iInf_le_of_le ε (iInf_le_of_le hε
      (le_of_eq (V.generalHNSlopeSum_eq_bot_of_maximalSlope_lt (t - ε) hsmall)))

/-- The actual general filtration is exhaustive, including the zero bundle. -/
theorem exists_generalHNFiltration_eq_top :
    ∃ t : ℝ, V.generalHNFiltration t = ⊤ := by
  by_cases hr : Module.finrank K V = 0
  · refine ⟨0, V.generalHNFiltration_eq_top_of_le_minimalSlope 0 ?_⟩
    rw [V.minimalSlope_eq_top_of_finrank_eq_zero hr]
    exact le_top
  · obtain ⟨c, hc⟩ := V.exists_minimalSlope_eq_coe (Nat.pos_of_ne_zero hr)
    exact ⟨c, V.generalHNFiltration_eq_top_of_le_minimalSlope c (le_of_eq hc.symm)⟩

/-- The actual general filtration is separated, including the zero bundle. -/
theorem exists_generalHNFiltration_eq_bot :
    ∃ t : ℝ, V.generalHNFiltration t = ⊥ := by
  by_cases hr : Module.finrank K V = 0
  · exact ⟨0, V.generalHNFiltration_eq_bot_of_finrank_eq_zero hr 0⟩
  · obtain ⟨c, hc⟩ := V.exists_maximalSlope_eq_coe (Nat.pos_of_ne_zero hr)
    refine ⟨c + 1, V.generalHNFiltration_eq_bot_of_maximalSlope_lt (c + 1) ?_⟩
    rw [hc]
    exact EReal.coe_lt_coe (by linarith)

/-- The actual source sum retains the minimum-slope bound, even when its
nonzero eligible index is empty. This consumes actual arbitrary-sum stability. -/
theorem le_minimalSlope_restrict_generalHNSlopeSum (t : ℝ) :
    (t : EReal) ≤ (V.restrictOfMeasurableBase
      (V.generalHNSlopeSum t)).minimalSlope := by
  let I := {U : Submodule K V // U ≠ ⊥ ∧
    (t : EReal) ≤ (V.restrictOfMeasurableBase U).minimalSlope}
  have he : (⨆ U : I, U.val) = V.generalHNSlopeSum t := by
    apply le_antisymm
    · exact iSup_le fun U ↦ le_iSup_of_le U.val (le_iSup_of_le U.property.1
        (le_iSup_of_le U.property.2 le_rfl))
    · exact iSup_le fun U ↦ iSup_le fun hU ↦ iSup_le fun ht ↦
        le_iSup_of_le (⟨U, hU, ht⟩ : I) le_rfl
  have hb := V.minimalSlope_restrict_iSup_ge (fun U : I ↦ U.val) t
    (fun U ↦ U.property.2)
  rwa [he] at hb

/-- Source Proposition 4.3.46: the actual epsilon intersection has actual
restricted minimum at least the exact real threshold. Rank-zero minima remain top. -/
theorem le_minimalSlope_restrict_generalHNFiltration (t : ℝ) :
    (t : EReal) ≤ (V.restrictOfMeasurableBase
      (V.generalHNFiltration t)).minimalSlope := by
  let R := V.restrictOfMeasurableBase (V.generalHNFiltration t)
  by_cases hr : Module.finrank K (V.generalHNFiltration t) = 0
  · rw [R.minimalSlope_eq_top_of_finrank_eq_zero hr]
    exact le_top
  · obtain ⟨c, hc⟩ := R.exists_minimalSlope_eq_coe (Nat.pos_of_ne_zero hr)
    rw [hc]
    apply EReal.coe_le_coe
    by_contra htc
    have hct : c < t := lt_of_not_ge htc
    obtain ⟨δ, hδ, hstable⟩ := V.exists_generalHNFiltration_stabilizes t
    let ε := min δ ((t - c) / 2)
    have hε : 0 < ε := lt_min hδ (by linarith)
    have hεδ : ε ≤ δ := min_le_left _ _
    have hεc : ε ≤ (t - c) / 2 := min_le_right _ _
    have he := congrArg (fun U : Submodule K V ↦
      (V.restrictOfMeasurableBase U).minimalSlope) (hstable ε hε hεδ)
    have hb : ((t - ε : ℝ) : EReal) ≤ R.minimalSlope :=
      (V.le_minimalSlope_restrict_generalHNSlopeSum (t - ε)).trans_eq he
    rw [hc] at hb
    have hbc := EReal.coe_le_coe_iff.mp hb
    linarith

/-- The literal source epsilon-intersection equals the nonzero actual
minimum-slope sum at the exact threshold, including an empty eligible family. -/
theorem generalHNFiltration_eq_generalHNSlopeSum (t : ℝ) :
    V.generalHNFiltration t = V.generalHNSlopeSum t := by
  apply le_antisymm _ (V.generalHNSlopeSum_le_generalHNFiltration t)
  by_cases hz : V.generalHNFiltration t = ⊥
  · rw [hz]
    exact bot_le
  · exact le_iSup_of_le (V.generalHNFiltration t)
      (le_iSup_of_le hz (le_iSup_of_le
        (V.le_minimalSlope_restrict_generalHNFiltration t) le_rfl))

/-- Every actual restricted subspace with minimum at least the threshold
lies in the general filtration term; the zero subspace is allowed. -/
theorem le_generalHNFiltration_of_le_minimalSlope_restrict (U : Submodule K V) (t : ℝ)
    (ht : (t : EReal) ≤ (V.restrictOfMeasurableBase U).minimalSlope) :
    U ≤ V.generalHNFiltration t := by
  by_cases hU : U = ⊥
  · rw [hU]
    exact bot_le
  · have hi : U ≤ V.generalHNSlopeSum t :=
      le_iSup_of_le U (le_iSup_of_le hU (le_iSup_of_le ht le_rfl))
    exact hi.trans (V.generalHNSlopeSum_le_generalHNFiltration t)

/-- The actual general term is the greatest subspace with its actual
restricted minimum at least the threshold, without any supplied attainment. -/
theorem isGreatest_generalHNFiltration (t : ℝ) :
    IsGreatest {U : Submodule K V |
      (t : EReal) ≤ (V.restrictOfMeasurableBase U).minimalSlope}
      (V.generalHNFiltration t) :=
  ⟨V.le_minimalSlope_restrict_generalHNFiltration t,
    fun U hU ↦ V.le_generalHNFiltration_of_le_minimalSlope_restrict U t hU⟩

/-- The exact real levels retaining the whole bundle are characterized by
the actual ambient minimum, with its infinite zero-bundle convention intact. -/
theorem generalHNFiltration_eq_top_iff (t : ℝ) :
    V.generalHNFiltration t = ⊤ ↔ (t : EReal) ≤ V.minimalSlope := by
  constructor
  · intro ht
    have hm := V.le_minimalSlope_restrict_generalHNFiltration t
    have he := congrArg (fun U : Submodule K V ↦
      (V.restrictOfMeasurableBase U).minimalSlope) ht
    exact hm.trans_eq (he.trans (V.minimalSlope_restrict_top))
  · exact V.generalHNFiltration_eq_top_of_le_minimalSlope t

/-- Left local constancy is produced by the actual finite-dimensional
epsilon stabilization and exact-threshold sum equality. -/
theorem generalHNFiltration_locallyConstant_left (t : ℝ) :
    ∃ δ > 0, ∀ ε, 0 ≤ ε → ε ≤ δ →
      V.generalHNFiltration (t - ε) = V.generalHNFiltration t := by
  obtain ⟨δ, hδ, hstable⟩ := V.exists_generalHNFiltration_stabilizes t
  refine ⟨δ, hδ, fun ε hε hεδ ↦ ?_⟩
  by_cases hz : ε = 0
  · simp only [hz, sub_zero]
  · exact (V.generalHNFiltration_eq_generalHNSlopeSum (t - ε)).trans
      (hstable ε (lt_of_le_of_ne hε (Ne.symm hz)) hεδ)

/-- Source maximum formula in positive rank, stated intrinsically as a
greatest real level rather than a real-part convention for infinite minima. -/
theorem exists_isGreatest_generalHNFiltration_eq_top
    (hr : 0 < Module.finrank K V) :
    ∃ c : ℝ, V.minimalSlope = (c : EReal) ∧
      IsGreatest {t : ℝ | V.generalHNFiltration t = ⊤} c := by
  obtain ⟨c, hc⟩ := V.exists_minimalSlope_eq_coe hr
  refine ⟨c, hc, ?_⟩
  have he : {t : ℝ | V.generalHNFiltration t = ⊤} = Set.Iic c := by
    ext t
    simp only [Set.mem_ofPred_eq, V.generalHNFiltration_eq_top_iff, hc,
      EReal.coe_le_coe_iff, Set.mem_Iic]
  rw [he]
  exact isGreatest_Iic

section HermitianComparison

variable {E' : Type (max u w)} [AddCommGroup E'] [Module K E']
  [FiniteDimensional K E'] (W : AdelicVectorBundle.{max u w} S)

/-- On actual Hermitian bundles the source epsilon-intersection construction
equals the previously produced Hermitian filtration, since both are the same
nonzero actual minimum-slope sum. -/
theorem generalHNFiltration_eq_hermitianHNFiltration
    [hW : W.toNormFamily.IsHermitian] (t : ℝ) :
    W.generalHNFiltration t = W.hermitianHNFiltration t :=
  (W.generalHNFiltration_eq_generalHNSlopeSum t).trans
    (W.hermitianHNFiltration_eq_iSup_nonzero_minimalSlope t).symm

end HermitianComparison

end AdelicVectorBundle

end

end ArakelovGeometry
