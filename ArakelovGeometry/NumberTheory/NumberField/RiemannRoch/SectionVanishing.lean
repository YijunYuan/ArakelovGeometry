/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic
public import ArakelovGeometry.NumberTheory.NumberField.Model.Sections

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.AdelicVectorBundle.Degree.LineVector
import Mathlib.Topology.Sheaves.Init

/-! # Actual classical section vanishing under negative maximal slope -/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped TensorProduct

namespace ArakelovGeometry

namespace AdelicVectorBundle

variable {K E : Type*} [Field K] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- An actual effective rational section would have nonnegative vector degree,
contradicting negative actual maximal slope. -/
theorem effectiveSections_eq_singleton_of_maximalSlope_neg
    (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (hneg : V.maximalSlope < 0) : V.toNormFamily.effectiveSections = {0} := by
  ext s
  constructor
  · intro hs
    apply mem_singleton_iff.mpr
    by_contra hszero
    have hd : 0 ≤ V.vectorDegree ⟨s, hszero⟩ := by
      rw [vectorDegree, NormFamily.vectorDegree_eq_neg_integral]
      apply neg_nonneg.mpr
      apply integral_nonpos_of_ae
      exact Filter.Eventually.of_forall fun ω =>
        Real.log_nonpos (V.toNormFamily.norm_nonneg _ _) (hs ω)
    have hm := V.vectorDegree_le_maximalSlope ⟨s, hszero⟩
    have hz : (0 : EReal) ≤ (V.vectorDegree ⟨s, hszero⟩ : EReal) := by exact_mod_cast hd
    exact (not_le_of_gt hneg) (hz.trans hm)
  · intro hs
    rw [mem_singleton_iff] at hs
    subst s
    intro ω
    simp

/-- A quotient with negative actual maximal slope has no nonzero effective image,
so all actual effective sections come from the literal restricted subspace. -/
theorem effectiveSections_eq_image_restrict_of_quotient_maximalSlope_neg
    (V : AdelicVectorBundle S) (U : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (hneg : (V.quotientOfNormMeasurability U).maximalSlope < 0) :
    V.toNormFamily.effectiveSections =
      U.subtype '' (V.restrictOfNormMeasurability U).toNormFamily.effectiveSections := by
  have hQ := (V.quotientOfNormMeasurability U).effectiveSections_eq_singleton_of_maximalSlope_neg
    hneg
  ext x
  constructor
  · intro hx
    have hxQ : U.mkQ x ∈ (V.quotientOfNormMeasurability U).toNormFamily.effectiveSections := by
      intro ω
      change (V.toNormFamily.quotient U).norm ω (1 ⊗ₜ[K] U.mkQ x) ≤ 1
      have h := (V.toNormFamily.quotient_norm_mk_le U ω (1 ⊗ₜ[K] x)).trans (hx ω)
      simpa only [LinearMap.baseChange_tmul, smul_eq_mul, one_mul] using h
    have hxzero : U.mkQ x = 0 := by simpa only [hQ, mem_singleton_iff] using hxQ
    have hxU : x ∈ U := by
      have hk : x ∈ LinearMap.ker U.mkQ := hxzero
      simpa only [Submodule.ker_mkQ] using hk
    refine ⟨⟨x, hxU⟩, ?_, rfl⟩
    intro ω
    exact hx ω
  · rintro ⟨u, hu, rfl⟩
    intro ω
    exact hu ω

end AdelicVectorBundle

namespace NumberFieldClassicalSectionVanishing

open NumberField AdelicStructure NumberFieldProjectiveGeneric NumberFieldFullLattice
open NumberFieldInvertibleGeneric (genericImage genericImage_fullSpan genericInclusion)

variable {K : Type*} [Field K] [NumberField K]
  (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Negative maximal slope of the actual full-lattice adelic bundle forces the
original finite projective module's actual effective sections to be exactly zero. -/
theorem effectiveSections_eq_singleton_of_maximalSlope_neg
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hneg :
      (fullLatticeAdelicBundle (genericImage (K := K) M)
      (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M) η).maximalSlope
        < 0) :
    effectiveSections M η = {0} := by
  let V := fullLatticeAdelicBundle (genericImage (K := K) M)
    (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M) η
  have hV := V.effectiveSections_eq_singleton_of_maximalSlope_neg
    hneg
  ext m
  constructor
  · intro hm
    apply mem_singleton_iff.mpr
    apply genericInclusion_injective (K := K) M
    have hx := (genericInclusion_mem_effectiveSections_iff M η m).mpr hm
    rw [hV, mem_singleton_iff] at hx
    simpa only [map_zero] using hx
  · intro hm
    rw [mem_singleton_iff] at hm
    subst m
    exact zero_mem_effectiveSections M η

/-- The source h0 of the original arithmetic module vanishes under negative
actual maximal slope, including the zero-rank case. -/
theorem logSectionCount_eq_zero_of_maximalSlope_neg
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hneg :
      (fullLatticeAdelicBundle (genericImage (K := K) M)
      (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M) η).maximalSlope
        < 0) :
    logSectionCount M η = 0 := by
  simp [logSectionCount, effectiveSections_eq_singleton_of_maximalSlope_neg M η hneg]

end NumberFieldClassicalSectionVanishing

end ArakelovGeometry
