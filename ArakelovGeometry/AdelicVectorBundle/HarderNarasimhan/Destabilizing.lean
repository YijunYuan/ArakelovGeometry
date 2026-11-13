/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic

import ArakelovGeometry.AdelicVectorBundle.Degree.Supermodular
import ArakelovGeometry.AdelicVectorBundle.Subquotient.Restriction.Functor
import ArakelovGeometry.LinearAlgebra.Submodule.SupermodularSlope
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Largest destabilizing subspaces of actual Hermitian bundles

Supermodularity of the actual restricted degree feeds the finite-dimensional
lattice maximum theorem. The resulting largest subspace attains the actual
extended-real maximal slope. Semistability includes the nonzero qualification
of source Definition 4.3.29, and the produced subspace is itself semistable
with its actual restriction norms.
-/

@[expose] public section

namespace ArakelovGeometry

noncomputable section

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace AdelicVectorBundle

/-- A nonzero Hermitian bundle has a unique largest actual maximizing
subspace. No boundedness or attainment premise is supplied by the caller. -/
theorem exists_unique_largest_maximalSlope_subspace (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] (hr : 0 < Module.finrank K V) :
    ∃! D : Submodule K V, 0 < Module.finrank K D ∧
      ((V.restrictOfNormMeasurability D).slope : EReal) = V.maximalSlope ∧
      ∀ F : Submodule K V, 0 < Module.finrank K F →
        ((V.restrictOfNormMeasurability F).slope : EReal) = V.maximalSlope →
        F ≤ D := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos hr
  let d := fun U : Submodule K V ↦ (V.restrictOfNormMeasurability U).degree
  have hd0 : d ⊥ ≤ 0 := by
    dsimp only [d]
    rw [(V.restrictOfNormMeasurability ⊥).degree_eq_zero_of_finrank_eq_zero
      (by simp)]
  have hdsuper : ∀ U W, d U + d W ≤ d (U ⊓ W) + d (U ⊔ W) :=
    fun U W ↦ V.degree_restrict_inf_add_sup_ge_of_isHermitian U W
  obtain ⟨D, ⟨hD, hmax⟩, _⟩ :=
    exists_unique_largest_finrank_slope_maximizer d hd0 hdsuper
  have hp : 0 < Module.finrank K D :=
    Nat.pos_of_ne_zero (fun hz ↦ hD (Submodule.finrank_eq_zero.mp hz))
  have he : ((V.restrictOfNormMeasurability D).slope : EReal) =
      V.maximalSlope := by
    apply le_antisymm (V.slope_restrict_le_maximalSlope D hp)
    apply V.maximalSlope_le
    intro F hF
    apply EReal.coe_le_coe_iff.mpr
    exact (hmax F (fun hz ↦ (ne_of_gt hF) (Submodule.finrank_eq_zero.mpr hz))).1
  have hcontains (F : Submodule K V) (hF : 0 < Module.finrank K F)
      (heF : ((V.restrictOfNormMeasurability F).slope : EReal) =
        V.maximalSlope) : F ≤ D := by
    apply (hmax F (fun hz ↦ (ne_of_gt hF) (Submodule.finrank_eq_zero.mpr hz))).2
    exact EReal.coe_eq_coe_iff.mp (heF.trans he.symm)
  refine ⟨D, ⟨hp, he, hcontains⟩, ?_⟩
  rintro D' ⟨hp', he', hcontains'⟩
  exact le_antisymm (hcontains D' hp' he') (hcontains' D hp he)

/-- The maximal destabilizing subspace produced from actual Hermitian degree. -/
def destabilizingSubspace (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] (hr : 0 < Module.finrank K V) : Submodule K V :=
  Classical.choose (V.exists_unique_largest_maximalSlope_subspace hr)

/-- The produced destabilizing subspace is nonzero. -/
theorem destabilizingSubspace_finrank_pos (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] (hr : 0 < Module.finrank K V) :
    0 < Module.finrank K (V.destabilizingSubspace hr) :=
  (Classical.choose_spec (V.exists_unique_largest_maximalSlope_subspace hr)).1.1

/-- The produced subspace's real mean is the actual extended-real maximum. -/
theorem slope_destabilizingSubspace_eq_maximalSlope (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] (hr : 0 < Module.finrank K V) :
    ((V.restrictOfNormMeasurability (V.destabilizingSubspace hr)).slope
      : EReal) = V.maximalSlope :=
  (Classical.choose_spec (V.exists_unique_largest_maximalSlope_subspace hr)).1.2.1

/-- Every actual maximizing subspace is contained in the produced one. -/
theorem le_destabilizingSubspace_of_slope_eq_maximalSlope (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] (hr : 0 < Module.finrank K V)
    (F : Submodule K V) (hF : 0 < Module.finrank K F)
    (heF : ((V.restrictOfNormMeasurability F).slope : EReal) = V.maximalSlope) :
    F ≤ V.destabilizingSubspace hr :=
  (Classical.choose_spec (V.exists_unique_largest_maximalSlope_subspace hr)).1.2.2
    F hF heF

/-- Semistability uses actual restrictions and includes the source's nonzero
qualification. Hermitian attainment identifies it with the whole-space
destabilizing subspace below. -/
class IsMeanSlopeSemistable (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] : Prop where
  /-- Semistability excludes the zero bundle. -/
  rank_pos : 0 < Module.finrank K V
  /-- Every nonzero subspace has slope at most the ambient mean slope. -/
  slope_le : ∀ F : Submodule K V, 0 < Module.finrank K F →
    (V.restrictOfNormMeasurability F).slope ≤ V.slope

/-- For any positive-rank bundle, semistability is equality of maximal and
mean slopes. The equality retains the actual `EReal` maximal slope. -/
theorem isMeanSlopeSemistable_iff_maximalSlope_eq_slope (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (hr : 0 < Module.finrank K V) :
    V.IsMeanSlopeSemistable ↔ V.maximalSlope = (V.slope : EReal) := by
  constructor
  · intro h
    exact le_antisymm
      (V.maximalSlope_le (fun F hF ↦ EReal.coe_le_coe_iff.mpr (h.2 F hF)))
      (V.slope_le_maximalSlope hr)
  · intro he
    refine ⟨hr, fun F hF ↦ ?_⟩
    exact EReal.coe_le_coe_iff.mp
      ((V.slope_restrict_le_maximalSlope F hF).trans_eq he)

/-- Source Definition 4.3.29: the produced destabilizing subspace is the
whole space exactly when the actual bundle is semistable. -/
theorem destabilizingSubspace_eq_top_iff_isMeanSlopeSemistable (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] (hr : 0 < Module.finrank K V) :
    V.destabilizingSubspace hr = ⊤ ↔ V.IsMeanSlopeSemistable := by
  rw [V.isMeanSlopeSemistable_iff_maximalSlope_eq_slope hr]
  constructor
  · intro hD
    have h := V.slope_destabilizingSubspace_eq_maximalSlope hr
    rwa [hD, V.slope_restrict_top, eq_comm] at h
  · intro he
    apply top_le_iff.mp
    apply V.le_destabilizingSubspace_of_slope_eq_maximalSlope hr ⊤
    · simpa only [finrank_top] using hr
    · rw [V.slope_restrict_top, he]

/-- Canonical nested restrictions preserve actual mean slopes, as well as
the degrees and dimensions that define them. -/
theorem slope_restrict_restrict (V : AdelicVectorBundle S)
    (U W : Submodule K V) (h : U ≤ W)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    ((V.restrictOfNormMeasurability W).restrictOfNormMeasurability
      (U.comap W.subtype)).slope =
      (V.restrictOfNormMeasurability U).slope := by
  rw [slope, slope, V.degree_restrict_restrict U W h,
    (Submodule.comapSubtypeEquivOfLe h).finrank_eq]

/-- The actual restriction to the produced largest destabilizing subspace
is semistable, by viewing every one of its subspaces inside the original
bundle through the canonical nested restriction isometry. -/
theorem isMeanSlopeSemistable_restrict_destabilizingSubspace (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] (hr : 0 < Module.finrank K V) :
    (V.restrictOfNormMeasurability (V.destabilizingSubspace hr)).IsMeanSlopeSemistable
      := by
  let D := V.destabilizingSubspace hr
  refine ⟨V.destabilizingSubspace_finrank_pos hr, fun F hF ↦ ?_⟩
  let U := F.map D.subtype
  have hUD : U ≤ D := D.map_subtype_le F
  have hc : U.comap D.subtype = F := by
    simp only [U, Submodule.comap_map_eq, Submodule.ker_subtype, sup_bot_eq]
  have hs := V.slope_restrict_restrict U D hUD
  rw [hc] at hs
  rw [hs]
  apply EReal.coe_le_coe_iff.mp
  have hpU : 0 < Module.finrank K U := by
    rw [Submodule.finrank_map_subtype_eq]
    exact hF
  exact (V.slope_restrict_le_maximalSlope U hpU).trans_eq
    (V.slope_destabilizingSubspace_eq_maximalSlope hr).symm

/-- The source nonzero qualification excludes the zero-rank bundle from
semistability. -/
theorem not_isMeanSlopeSemistable_of_finrank_eq_zero (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (hr : Module.finrank K V = 0) : ¬ V.IsMeanSlopeSemistable := by
  intro h
  exact (ne_of_gt h.1) hr

/-- Every actual line bundle is semistable: its only nonzero rational
subspace is the total space. -/
theorem isMeanSlopeSemistable_of_finrank_eq_one (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (hr : Module.finrank K V = 1) : V.IsMeanSlopeSemistable := by
  refine ⟨by omega, fun F hF ↦ ?_⟩
  have ht : F = ⊤ := Submodule.eq_top_of_finrank_eq (by
    have hle := F.finrank_le
    omega)
  rw [ht, V.slope_restrict_top]

instance isMeanSlopeSemistable_of_isLine (V : AdelicVectorBundle S)
    [S.NormMeasurabilityHypotheses] [S.IsArchimedeanNormalized] [hV : V.IsLine] :
    V.IsMeanSlopeSemistable :=
  V.isMeanSlopeSemistable_of_finrank_eq_one hV.rank_eq_one

end AdelicVectorBundle

end

end ArakelovGeometry
