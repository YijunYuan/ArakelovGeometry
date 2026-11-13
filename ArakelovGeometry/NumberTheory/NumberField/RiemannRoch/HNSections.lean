/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.Basic
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Basic
public import ArakelovGeometry.NumberTheory.NumberField.RiemannRoch.SectionVanishing

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.PositiveDegree
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Truncations
import Mathlib.Topology.Sheaves.Init

/-! # Effective sections and the actual nonnegative Hermitian HN subspace -/

@[expose] public section

noncomputable section
open MeasureTheory Set

namespace ArakelovGeometry.AdelicVectorBundle

variable {K E : Type*} [Field K] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S)
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]
  [hV : V.toNormFamily.IsHermitian]

/-- Inclusion of the actual zero HN truncation gives an actual bijection of the
original all-place effective-section sets, without an arithmetic model premise. -/
def effectiveSectionsEquivHNZero :
    (V.restrictOfNormMeasurability
      (V.hermitianHNFiltration 0)).toNormFamily.effectiveSections ≃
      V.toNormFamily.effectiveSections :=
  let U := V.hermitianHNFiltration 0
  (Equiv.Set.imageOfInjOn U.subtype
    (V.restrictOfNormMeasurability U).toNormFamily.effectiveSections
      (by exact U.subtype_injective.injOn)).trans (Set.equivOfEq (by
        have hneg : (V.quotientOfNormMeasurability U).maximalSlope < 0 := by
          simpa only [EReal.coe_zero] using
            V.maximalSlope_quotient_hermitianHNFiltration_lt 0
        exact (V.effectiveSections_eq_image_restrict_of_quotient_maximalSlope_neg
          U hneg).symm))

/-- The actual all-place effective-section count is unchanged at the nonnegative
HN truncation. The count equality comes from the produced literal bijection. -/
theorem card_effectiveSections_eq_HNZero :
    Nat.card V.toNormFamily.effectiveSections =
      Nat.card
        (V.restrictOfNormMeasurability
          (V.hermitianHNFiltration 0)).toNormFamily.effectiveSections :=
  (Nat.card_congr (V.effectiveSectionsEquivHNZero)).symm

/-- Actual HN truncation simultaneously preserves effective-section cardinality,
realizes positive degree and has nonnegative actual minimal slope. -/
theorem hnZero_sections_degree_minimalSlope :
    (Nat.card V.toNormFamily.effectiveSections =
      Nat.card (V.restrictOfNormMeasurability
        (V.hermitianHNFiltration 0)).toNormFamily.effectiveSections) ∧
    V.positiveDegree =
      ((V.restrictOfNormMeasurability (V.hermitianHNFiltration 0)).degree : EReal) ∧
    0 ≤ (V.restrictOfNormMeasurability
      (V.hermitianHNFiltration 0)).minimalSlope := by
  refine ⟨V.card_effectiveSections_eq_HNZero,
    V.positiveDegree_eq_degree_restrict_hermitianHNFiltration_zero, ?_⟩
  · simpa only [EReal.coe_zero] using V.le_minimalSlope_restrict_hermitianHNFiltration 0

end ArakelovGeometry.AdelicVectorBundle

namespace ArakelovGeometry.NumberFieldClassicalHNSections

open NumberField AdelicStructure NumberFieldProjectiveGeneric NumberFieldFullLattice
open NumberFieldInvertibleGeneric (genericImage genericImage_fullSpan)
open scoped TensorProduct

variable {K : Type*} [Field K] [NumberField K]
  (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- The actual original-module h0 reduces to the genuine nonnegative HN subspace,
whose actual degree is positive degree and whose actual minimal slope is nonnegative. -/
theorem original_hnZero_sections_degree_minimalSlope
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    [hη : η.IsHermitian] :
    let L := genericImage (K := K) M
    let hfg := genericImage_fg (K := K) M
    let hspan := genericImage_fullSpan (K := K) M
    let V := fullLatticeAdelicBundle L hfg hspan η
    let hV : V.toNormFamily.IsHermitian :=
      fullLatticeGaugeFamily_isHermitian L hfg hspan η
    let F := V.hermitianHNFiltration
      (hV := hV) 0
    let W := V.restrictOfNormMeasurability F
    (logSectionCount M η = Real.log (Nat.card W.toNormFamily.effectiveSections : ℝ)) ∧
    V.positiveDegree =
      (W.degree : EReal) ∧
    0 ≤ W.minimalSlope := by
  let L := genericImage (K := K) M
  let hfg := genericImage_fg (K := K) M
  let hspan := genericImage_fullSpan (K := K) M
  let V := fullLatticeAdelicBundle L hfg hspan η
  have hV : V.toNormFamily.IsHermitian :=
    fullLatticeGaugeFamily_isHermitian L hfg hspan η
  have h := V.hnZero_sections_degree_minimalSlope
    (hV := hV)
  refine ⟨?_, h.2⟩
  rw [logSectionCount_eq_adelic M η, h.1]

end ArakelovGeometry.NumberFieldClassicalHNSections
