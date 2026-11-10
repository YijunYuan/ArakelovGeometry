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

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace AdelicVectorBundle

variable [S.IsProper] (V : AdelicVectorBundle S E)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)

/-- The actual sum in source Definition 4.3.45. Only nonzero rational
subspaces with the actual restricted minimum-slope bound occur. -/
def generalHNSlopeSum (t : ℝ) : Submodule K E :=
  ⨆ (U : Submodule K E) (_ : U ≠ ⊥)
    (_ : (t : EReal) ≤ (V.restrictOfMeasurableBase U hS).minimalSlope hS hN), U

/-- Source equation (4.65), with the actual epsilon-intersection. -/
def generalHNFiltration (t : ℝ) : Submodule K E :=
  ⨅ (ε : ℝ) (_ : 0 < ε), V.generalHNSlopeSum hS hN (t - ε)

/-- The source's two infinite endpoint conventions, keeping real levels
in the actual epsilon-intersection definition. -/
def generalHNFiltrationExtended : EReal → Submodule K E :=
  EReal.rec ⊤ (V.generalHNFiltration hS hN) ⊥

@[simp] theorem generalHNFiltrationExtended_bot :
    V.generalHNFiltrationExtended hS hN ⊥ = ⊤ := rfl

@[simp] theorem generalHNFiltrationExtended_top :
    V.generalHNFiltrationExtended hS hN ⊤ = ⊥ := rfl

@[simp] theorem generalHNFiltrationExtended_coe (t : ℝ) :
    V.generalHNFiltrationExtended hS hN (t : EReal) =
      V.generalHNFiltration hS hN t := rfl

/-- A higher threshold has fewer eligible summands. -/
theorem antitone_generalHNSlopeSum : Antitone (V.generalHNSlopeSum hS hN) := by
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
theorem antitone_generalHNFiltration : Antitone (V.generalHNFiltration hS hN) := by
  intro s t hst
  exact iInf_mono fun ε ↦ iInf_mono fun _ ↦
    V.antitone_generalHNSlopeSum hS hN (sub_le_sub_right hst ε)

/-- The exact-threshold sum lies in every positive-epsilon term. -/
theorem generalHNSlopeSum_le_generalHNFiltration (t : ℝ) :
    V.generalHNSlopeSum hS hN t ≤ V.generalHNFiltration hS hN t := by
  apply le_iInf
  intro ε
  apply le_iInf
  intro hε
  exact V.antitone_generalHNSlopeSum hS hN (sub_le_self t hε.le)

/-- Finite dimension forces the actual positive-epsilon cone to stabilize
at its intersection. No finite image, flag, or slope attainment is supplied. -/
theorem exists_generalHNFiltration_stabilizes (t : ℝ) :
    ∃ δ > 0, ∀ ε, 0 < ε → ε ≤ δ →
      V.generalHNSlopeSum hS hN (t - ε) = V.generalHNFiltration hS hN t := by
  classical
  let P : ℕ → Prop := fun n ↦ ∃ δ > 0,
    Module.finrank K (V.generalHNSlopeSum hS hN (t - δ)) = n
  have hex : ∃ n, P n := ⟨_, 1, zero_lt_one, rfl⟩
  obtain ⟨δ, hδ, hdim⟩ := Nat.find_spec hex
  have hsmall : ∀ ε, 0 < ε → ε ≤ δ →
      V.generalHNSlopeSum hS hN (t - ε) = V.generalHNSlopeSum hS hN (t - δ) := by
    intro ε hε hεδ
    have hle := V.antitone_generalHNSlopeSum hS hN (sub_le_sub_left hεδ t)
    apply Submodule.eq_of_le_of_finrank_eq hle
    apply Nat.le_antisymm (Submodule.finrank_mono hle)
    rw [hdim]
    exact Nat.find_min' hex ⟨ε, hε, rfl⟩
  have hintersection : V.generalHNFiltration hS hN t =
      V.generalHNSlopeSum hS hN (t - δ) := by
    apply le_antisymm
    · exact iInf_le_of_le δ (iInf_le_of_le hδ le_rfl)
    · apply le_iInf
      intro ε
      apply le_iInf
      intro hε
      by_cases hεδ : ε ≤ δ
      · exact le_of_eq (hsmall ε hε hεδ).symm
      · exact V.antitone_generalHNSlopeSum hS hN
          (sub_le_sub_left (le_of_not_ge hεδ) t)
  exact ⟨δ, hδ, fun ε hε hεδ ↦ (hsmall ε hε hεδ).trans hintersection.symm⟩

/-- In rank zero the actual source sum has no eligible nonzero summands. -/
theorem generalHNSlopeSum_eq_bot_of_finrank_eq_zero
    (hr : Module.finrank K E = 0) (t : ℝ) : V.generalHNSlopeSum hS hN t = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro U
  apply iSup_le
  intro hU
  have hz : Module.finrank K U = 0 := Nat.eq_zero_of_le_zero (hr ▸ U.finrank_le)
  exact False.elim (hU (Submodule.finrank_eq_zero.mp hz))

/-- The actual epsilon intersection is zero at every real level in rank zero. -/
theorem generalHNFiltration_eq_bot_of_finrank_eq_zero
    (hr : Module.finrank K E = 0) (t : ℝ) : V.generalHNFiltration hS hN t = ⊥ := by
  apply bot_unique
  exact iInf_le_of_le 1 (iInf_le_of_le zero_lt_one
    (le_of_eq (V.generalHNSlopeSum_eq_bot_of_finrank_eq_zero hS hN hr (t - 1))))


/-- Above the actual ambient maximal slope there are no nonzero eligible
summands: each restricted minimum is at most its mean and the ambient maximum. -/
theorem generalHNSlopeSum_eq_bot_of_maximalSlope_lt (t : ℝ)
    (ht : V.maximalSlope hS hN < (t : EReal)) : V.generalHNSlopeSum hS hN t = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro U
  apply iSup_le
  intro hU
  apply iSup_le
  intro hmin
  have hrU : 0 < Module.finrank K U := Nat.pos_of_ne_zero
    (fun hz ↦ hU (Submodule.finrank_eq_zero.mp hz))
  have hbound := ((V.restrictOfMeasurableBase U hS).minimalSlope_le_slope hS hN hrU).trans
    (V.slope_restrict_le_maximalSlope U hrU hS hN)
  exact False.elim ((not_le_of_gt ht) (hmin.trans hbound))

/-- The ambient bundle itself supplies a top summand at every threshold
below its minimum. The zero-rank case retains the empty source sum. -/
theorem generalHNSlopeSum_eq_top_of_le_minimalSlope (t : ℝ)
    (ht : (t : EReal) ≤ V.minimalSlope hS hN) : V.generalHNSlopeSum hS hN t = ⊤ := by
  by_cases hr : Module.finrank K E = 0
  · have htop : (⊤ : Submodule K E) = ⊥ := Submodule.finrank_eq_zero.mp
      (by simpa only [finrank_top] using hr)
    exact (V.generalHNSlopeSum_eq_bot_of_finrank_eq_zero hS hN hr t).trans htop.symm
  · apply top_unique
    have htop : (⊤ : Submodule K E) ≠ ⊥ := fun hz ↦ hr
      (by simpa only [finrank_top] using (Submodule.finrank_eq_zero.mpr hz))
    exact le_iSup_of_le ⊤ (le_iSup_of_le htop (le_iSup_of_le
      (by simpa only [V.minimalSlope_restrict_top hS hN] using ht) le_rfl))

/-- The whole ambient bundle lies in the actual epsilon intersection at
every threshold below its actual minimum. -/
theorem generalHNFiltration_eq_top_of_le_minimalSlope (t : ℝ)
    (ht : (t : EReal) ≤ V.minimalSlope hS hN) : V.generalHNFiltration hS hN t = ⊤ := by
  apply top_unique
  rw [← V.generalHNSlopeSum_eq_top_of_le_minimalSlope hS hN t ht]
  exact V.generalHNSlopeSum_le_generalHNFiltration hS hN t

/-- Above the actual maximal slope, one positive-epsilon term of the
intersection is already zero. Infinite zero-rank extrema are kept explicit. -/
theorem generalHNFiltration_eq_bot_of_maximalSlope_lt (t : ℝ)
    (ht : V.maximalSlope hS hN < (t : EReal)) : V.generalHNFiltration hS hN t = ⊥ := by
  by_cases hr : Module.finrank K E = 0
  · exact V.generalHNFiltration_eq_bot_of_finrank_eq_zero hS hN hr t
  · obtain ⟨c, hc⟩ := V.exists_maximalSlope_eq_coe hS hN (Nat.pos_of_ne_zero hr)
    have hct : c < t := EReal.coe_lt_coe_iff.mp (hc ▸ ht)
    let ε := (t - c) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hsmall : V.maximalSlope hS hN < ((t - ε : ℝ) : EReal) := by
      rw [hc]
      apply EReal.coe_lt_coe
      dsimp [ε]
      linarith
    apply bot_unique
    exact iInf_le_of_le ε (iInf_le_of_le hε
      (le_of_eq (V.generalHNSlopeSum_eq_bot_of_maximalSlope_lt hS hN (t - ε) hsmall)))

/-- The actual general filtration is exhaustive, including the zero bundle. -/
theorem exists_generalHNFiltration_eq_top :
    ∃ t : ℝ, V.generalHNFiltration hS hN t = ⊤ := by
  by_cases hr : Module.finrank K E = 0
  · refine ⟨0, V.generalHNFiltration_eq_top_of_le_minimalSlope hS hN 0 ?_⟩
    rw [V.minimalSlope_eq_top_of_finrank_eq_zero hS hN hr]
    exact le_top
  · obtain ⟨c, hc⟩ := V.exists_minimalSlope_eq_coe hS hN (Nat.pos_of_ne_zero hr)
    exact ⟨c, V.generalHNFiltration_eq_top_of_le_minimalSlope hS hN c (le_of_eq hc.symm)⟩

/-- The actual general filtration is separated, including the zero bundle. -/
theorem exists_generalHNFiltration_eq_bot :
    ∃ t : ℝ, V.generalHNFiltration hS hN t = ⊥ := by
  by_cases hr : Module.finrank K E = 0
  · exact ⟨0, V.generalHNFiltration_eq_bot_of_finrank_eq_zero hS hN hr 0⟩
  · obtain ⟨c, hc⟩ := V.exists_maximalSlope_eq_coe hS hN (Nat.pos_of_ne_zero hr)
    refine ⟨c + 1, V.generalHNFiltration_eq_bot_of_maximalSlope_lt hS hN (c + 1) ?_⟩
    rw [hc]
    exact EReal.coe_lt_coe (by linarith)

/-- The actual source sum retains the minimum-slope bound, even when its
nonzero eligible index is empty. This consumes actual arbitrary-sum stability. -/
theorem le_minimalSlope_restrict_generalHNSlopeSum (t : ℝ) :
    (t : EReal) ≤ (V.restrictOfMeasurableBase
      (V.generalHNSlopeSum hS hN t) hS).minimalSlope hS hN := by
  let I := {U : Submodule K E // U ≠ ⊥ ∧
    (t : EReal) ≤ (V.restrictOfMeasurableBase U hS).minimalSlope hS hN}
  have he : (⨆ U : I, U.val) = V.generalHNSlopeSum hS hN t := by
    apply le_antisymm
    · exact iSup_le fun U ↦ le_iSup_of_le U.val (le_iSup_of_le U.property.1
        (le_iSup_of_le U.property.2 le_rfl))
    · exact iSup_le fun U ↦ iSup_le fun hU ↦ iSup_le fun ht ↦
        le_iSup_of_le (⟨U, hU, ht⟩ : I) le_rfl
  have hb := V.minimalSlope_restrict_iSup_ge hS hN (fun U : I ↦ U.val) t
    (fun U ↦ U.property.2)
  rwa [he] at hb

/-- Source Proposition 4.3.46: the actual epsilon intersection has actual
restricted minimum at least the exact real threshold. Rank-zero minima remain top. -/
theorem le_minimalSlope_restrict_generalHNFiltration (t : ℝ) :
    (t : EReal) ≤ (V.restrictOfMeasurableBase
      (V.generalHNFiltration hS hN t) hS).minimalSlope hS hN := by
  let R := V.restrictOfMeasurableBase (V.generalHNFiltration hS hN t) hS
  by_cases hr : Module.finrank K (V.generalHNFiltration hS hN t) = 0
  · rw [R.minimalSlope_eq_top_of_finrank_eq_zero hS hN hr]
    exact le_top
  · obtain ⟨c, hc⟩ := R.exists_minimalSlope_eq_coe hS hN (Nat.pos_of_ne_zero hr)
    rw [hc]
    apply EReal.coe_le_coe
    by_contra htc
    have hct : c < t := lt_of_not_ge htc
    obtain ⟨δ, hδ, hstable⟩ := V.exists_generalHNFiltration_stabilizes hS hN t
    let ε := min δ ((t - c) / 2)
    have hε : 0 < ε := lt_min hδ (by linarith)
    have hεδ : ε ≤ δ := min_le_left _ _
    have hεc : ε ≤ (t - c) / 2 := min_le_right _ _
    have he := congrArg (fun U : Submodule K E ↦
      (V.restrictOfMeasurableBase U hS).minimalSlope hS hN) (hstable ε hε hεδ)
    have hb : ((t - ε : ℝ) : EReal) ≤ R.minimalSlope hS hN :=
      (V.le_minimalSlope_restrict_generalHNSlopeSum hS hN (t - ε)).trans_eq he
    rw [hc] at hb
    have hbc := EReal.coe_le_coe_iff.mp hb
    linarith

/-- The literal source epsilon-intersection equals the nonzero actual
minimum-slope sum at the exact threshold, including an empty eligible family. -/
theorem generalHNFiltration_eq_generalHNSlopeSum (t : ℝ) :
    V.generalHNFiltration hS hN t = V.generalHNSlopeSum hS hN t := by
  apply le_antisymm _ (V.generalHNSlopeSum_le_generalHNFiltration hS hN t)
  by_cases hz : V.generalHNFiltration hS hN t = ⊥
  · rw [hz]
    exact bot_le
  · exact le_iSup_of_le (V.generalHNFiltration hS hN t)
      (le_iSup_of_le hz (le_iSup_of_le
        (V.le_minimalSlope_restrict_generalHNFiltration hS hN t) le_rfl))

/-- Every actual restricted subspace with minimum at least the threshold
lies in the general filtration term; the zero subspace is allowed. -/
theorem le_generalHNFiltration_of_le_minimalSlope_restrict (U : Submodule K E) (t : ℝ)
    (ht : (t : EReal) ≤ (V.restrictOfMeasurableBase U hS).minimalSlope hS hN) :
    U ≤ V.generalHNFiltration hS hN t := by
  by_cases hU : U = ⊥
  · rw [hU]
    exact bot_le
  · have hi : U ≤ V.generalHNSlopeSum hS hN t :=
      le_iSup_of_le U (le_iSup_of_le hU (le_iSup_of_le ht le_rfl))
    exact hi.trans (V.generalHNSlopeSum_le_generalHNFiltration hS hN t)

/-- The actual general term is the greatest subspace with its actual
restricted minimum at least the threshold, without any supplied attainment. -/
theorem isGreatest_generalHNFiltration (t : ℝ) :
    IsGreatest {U : Submodule K E |
      (t : EReal) ≤ (V.restrictOfMeasurableBase U hS).minimalSlope hS hN}
      (V.generalHNFiltration hS hN t) :=
  ⟨V.le_minimalSlope_restrict_generalHNFiltration hS hN t,
    fun U hU ↦ V.le_generalHNFiltration_of_le_minimalSlope_restrict hS hN U t hU⟩

/-- The exact real levels retaining the whole bundle are characterized by
the actual ambient minimum, with its infinite zero-bundle convention intact. -/
theorem generalHNFiltration_eq_top_iff (t : ℝ) :
    V.generalHNFiltration hS hN t = ⊤ ↔ (t : EReal) ≤ V.minimalSlope hS hN := by
  constructor
  · intro ht
    have hm := V.le_minimalSlope_restrict_generalHNFiltration hS hN t
    have he := congrArg (fun U : Submodule K E ↦
      (V.restrictOfMeasurableBase U hS).minimalSlope hS hN) ht
    exact hm.trans_eq (he.trans (V.minimalSlope_restrict_top hS hN))
  · exact V.generalHNFiltration_eq_top_of_le_minimalSlope hS hN t

/-- Left local constancy is produced by the actual finite-dimensional
epsilon stabilization and exact-threshold sum equality. -/
theorem generalHNFiltration_locallyConstant_left (t : ℝ) :
    ∃ δ > 0, ∀ ε, 0 ≤ ε → ε ≤ δ →
      V.generalHNFiltration hS hN (t - ε) = V.generalHNFiltration hS hN t := by
  obtain ⟨δ, hδ, hstable⟩ := V.exists_generalHNFiltration_stabilizes hS hN t
  refine ⟨δ, hδ, fun ε hε hεδ ↦ ?_⟩
  by_cases hz : ε = 0
  · simp only [hz, sub_zero]
  · exact (V.generalHNFiltration_eq_generalHNSlopeSum hS hN (t - ε)).trans
      (hstable ε (lt_of_le_of_ne hε (Ne.symm hz)) hεδ)

/-- Source maximum formula in positive rank, stated intrinsically as a
greatest real level rather than a real-part convention for infinite minima. -/
theorem exists_isGreatest_generalHNFiltration_eq_top
    (hr : 0 < Module.finrank K E) :
    ∃ c : ℝ, V.minimalSlope hS hN = (c : EReal) ∧
      IsGreatest {t : ℝ | V.generalHNFiltration hS hN t = ⊤} c := by
  obtain ⟨c, hc⟩ := V.exists_minimalSlope_eq_coe hS hN hr
  refine ⟨c, hc, ?_⟩
  have he : {t : ℝ | V.generalHNFiltration hS hN t = ⊤} = Set.Iic c := by
    ext t
    simp only [Set.mem_ofPred_eq, V.generalHNFiltration_eq_top_iff hS hN, hc,
      EReal.coe_le_coe_iff, Set.mem_Iic]
  rw [he]
  exact isGreatest_Iic

section HermitianComparison

variable {E' : Type (max u w)} [AddCommGroup E'] [Module K E']
  [FiniteDimensional K E'] (W : AdelicVectorBundle S E')

/-- On actual Hermitian bundles the source epsilon-intersection construction
equals the previously produced Hermitian filtration, since both are the same
nonzero actual minimum-slope sum. -/
theorem generalHNFiltration_eq_hermitianHNFiltration
    (hW : W.toNormFamily.IsHermitian hN) (t : ℝ) :
    W.generalHNFiltration hS hN t = W.hermitianHNFiltration hS hN hW t :=
  (W.generalHNFiltration_eq_generalHNSlopeSum hS hN t).trans
    (W.hermitianHNFiltration_eq_iSup_nonzero_minimalSlope hS hN hW t).symm

end HermitianComparison

end AdelicVectorBundle

end

end ArakelovGeometry
