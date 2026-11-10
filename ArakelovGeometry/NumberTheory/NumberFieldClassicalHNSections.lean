/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HermitianHNPositiveDegree
public import ArakelovGeometry.AdelicVectorBundle.HermitianHNTruncations
public import ArakelovGeometry.NumberTheory.NumberFieldClassicalSectionVanishing

/-! # Effective sections and the actual nonnegative Hermitian HN subspace -/

@[expose] public section

noncomputable section
open MeasureTheory Set

namespace ArakelovGeometry.AdelicVectorBundle

variable {K E : Type*} [Field K] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S E)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hV : V.toNormFamily.IsHermitian hN)

/-- Inclusion of the actual zero HN truncation gives an actual bijection of the
original all-place effective-section sets, without an arithmetic model premise. -/
def effectiveSectionsEquivHNZero :
    (V.restrictOfMeasurableBase
      (V.hermitianHNFiltration hS hN hV 0) hS).toNormFamily.effectiveSections ≃
      V.toNormFamily.effectiveSections := by
  let U := V.hermitianHNFiltration hS hN hV 0
  have hneg : (V.quotientOfMeasurableBase U hS).maximalSlope hS hN < 0 := by
    simpa only [EReal.coe_zero] using
      V.maximalSlope_quotient_hermitianHNFiltration_lt hS hN hV 0
  have h := V.effectiveSections_eq_image_restrict_of_quotient_maximalSlope_neg
    U hS hN hneg
  exact (Equiv.Set.imageOfInjOn U.subtype
    (V.restrictOfMeasurableBase U hS).toNormFamily.effectiveSections
      U.subtype_injective.injOn).trans
      (Set.equivOfEq h.symm)

/-- The actual all-place effective-section count is unchanged at the nonnegative
HN truncation. The count equality comes from the produced literal bijection. -/
theorem card_effectiveSections_eq_HNZero :
    Nat.card V.toNormFamily.effectiveSections =
      Nat.card
        (V.restrictOfMeasurableBase
          (V.hermitianHNFiltration hS hN hV 0) hS).toNormFamily.effectiveSections :=
  (Nat.card_congr (V.effectiveSectionsEquivHNZero hS hN hV)).symm

/-- Actual HN truncation simultaneously preserves effective-section cardinality,
realizes positive degree and has nonnegative actual minimal slope. -/
theorem hnZero_sections_degree_minimalSlope :
    (Nat.card V.toNormFamily.effectiveSections =
      Nat.card (V.restrictOfMeasurableBase
        (V.hermitianHNFiltration hS hN hV 0) hS).toNormFamily.effectiveSections) ∧
    V.positiveDegree hS hN =
      ((V.restrictOfMeasurableBase (V.hermitianHNFiltration hS hN hV 0) hS).degree hS hN : EReal) ∧
    0 ≤ (V.restrictOfMeasurableBase
      (V.hermitianHNFiltration hS hN hV 0) hS).minimalSlope hS hN := by
  refine ⟨V.card_effectiveSections_eq_HNZero hS hN hV,
    V.positiveDegree_eq_degree_restrict_hermitianHNFiltration_zero hS hN hV, ?_⟩
  · simpa only [EReal.coe_zero] using V.le_minimalSlope_restrict_hermitianHNFiltration hS hN hV 0

end ArakelovGeometry.AdelicVectorBundle

namespace ArakelovGeometry.NumberFieldClassicalHNSections

open NumberField AdelicStructure NumberFieldProjectiveGeneric NumberFieldFullLattice
open NumberFieldInvertibleGeneric (genericImage genericImage_fullSpan)
open scoped TensorProduct

variable {K : Type*} [Field K] [NumberField K]
  (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

attribute [local instance] genericFiniteDimensional normalizedNumberFieldAdelicStructure_isProper

/-- The actual original-module h0 reduces to the genuine nonnegative HN subspace,
whose actual degree is positive degree and whose actual minimal slope is nonnegative. -/
theorem original_hnZero_sections_degree_minimalSlope
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    let L := genericImage (K := K) M
    let hfg := genericImage_fg (K := K) M
    let hspan := genericImage_fullSpan (K := K) M
    let V := fullLatticeAdelicBundle L hfg hspan η
    let hV : V.toNormFamily.IsHermitian normalizedNumberFieldArchimedeanCompletions :=
      fullLatticeGaugeFamily_isHermitian L hfg hspan η hη
    let F := V.hermitianHNFiltration (Or.inl inferInstance)
      normalizedNumberFieldArchimedeanCompletions hV 0
    let W := V.restrictOfMeasurableBase F (Or.inl inferInstance)
    (logSectionCount M η = Real.log (Nat.card W.toNormFamily.effectiveSections : ℝ)) ∧
    V.positiveDegree (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions =
      (W.degree (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions : EReal) ∧
    0 ≤ W.minimalSlope (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions := by
  let L := genericImage (K := K) M
  let hfg := genericImage_fg (K := K) M
  let hspan := genericImage_fullSpan (K := K) M
  let V := fullLatticeAdelicBundle L hfg hspan η
  have hV : V.toNormFamily.IsHermitian normalizedNumberFieldArchimedeanCompletions :=
    fullLatticeGaugeFamily_isHermitian L hfg hspan η hη
  have h := V.hnZero_sections_degree_minimalSlope (Or.inl inferInstance)
    normalizedNumberFieldArchimedeanCompletions hV
  refine ⟨?_, h.2⟩
  rw [logSectionCount_eq_adelic M η, h.1]

end ArakelovGeometry.NumberFieldClassicalHNSections
