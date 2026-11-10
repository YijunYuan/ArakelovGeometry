/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Isomorphism.Subspace
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Tower.OrdinaryNativeRestriction
import ArakelovGeometry.AdelicVectorBundle.AbsoluteInvariants.PositiveAtoms.Closure
import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Determinant.Basic
import Mathlib.CategoryTheory.Category.Init

/-!
# Ordinary native determinant degrees and closure choice

Actual native restriction bundles are produced from regularity of the original
base. The prescribed rational determinant map and genuine place measure
transport identify their canonical degrees and all native suprema.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K M]
  [IsAlgClosed L] [IsAlgClosed M] {S : AdelicStructure K} [S.IsProper]
  {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Canonical measurable-determinant degree of the actual ordinary direct
native restriction, with all analytic hypotheses produced. -/
def nativeRestrictionDegreeOfOrdinaryBase (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule L (L ⊗[K] E)) : ℝ :=
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  (V.scalarExtensionRestrictionOfOrdinaryBase hreg hN A).degreeOfMeasurableDeterminant
    (V.scalarExtensionRestrictionOfOrdinaryBase_determinant_isMeasurable hreg hN A)
    (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN)

/-- On common density this is the usual degree of the same actual native
restriction. -/
theorem nativeRestrictionDegreeOfOrdinaryBase_eq_common_degree
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule L (L ⊗[K] E)) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    V.nativeRestrictionDegreeOfOrdinaryBase (Or.inl hcount) hN A =
      ((V.scalarExtension (L := L) hcount hN).restrictOfMeasurableBase A
        (Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))).degree
        (Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))
        (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) := rfl

/-- On a countable discrete original base this is the existing actual native
determinant degree. -/
theorem nativeRestrictionDegreeOfOrdinaryBase_eq_countable_discrete_degree
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule L (L ⊗[K] E)) :
    V.nativeRestrictionDegreeOfOrdinaryBase (Or.inr ⟨inferInstance, inferInstance⟩) hN A =
      V.nativeRestrictionDegreeOfCountableDiscreteBase hN A := rfl

/-- Every nonzero rational determinant section computes the actual degree,
including the nonzero empty determinant in rank zero. -/
theorem nativeRestrictionDegreeOfOrdinaryBase_eq_neg_integral
    (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule L (L ⊗[K] E)) (t : ⋀[L]^(Module.finrank L A) A) (ht : t ≠ 0) :
    V.nativeRestrictionDegreeOfOrdinaryBase hreg hN A =
      -∫ ω, ((V.toNormFamily.scalarExtension (L := L)).restrict A).determinant.logNorm t ω
        ∂(S.algebraicExtension L).v := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  exact degreeOfMeasurableDeterminant_eq_neg_integral
    (V.scalarExtensionRestrictionOfOrdinaryBase hreg hN A)
      (V.scalarExtensionRestrictionOfOrdinaryBase_determinant_isMeasurable hreg hN A)
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) ⟨t, ht⟩

/-- The actual rational determinant map and genuine measure transport identify
ordinary native degrees across a prescribed coefficient-field isomorphism. -/
theorem nativeRestrictionDegreeOfOrdinaryBase_algEquiv (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (σ : L ≃ₐ[K] M) (A : Submodule L (L ⊗[K] E)) :
    V.nativeRestrictionDegreeOfOrdinaryBase hreg hN
      (scalarExtensionSubspaceOrderIso (E := E) σ A) =
      V.nativeRestrictionDegreeOfOrdinaryBase hreg hN A := by
  let := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  let t := determinantGenerator (K := L) (E := A)
  have ht : t ≠ 0 := determinantGenerator_ne_zero
  let d := scalarExtensionRestrictionDeterminantEquiv σ A
  have hd : d t ≠ 0 := d.map_ne_zero_iff.mpr ht
  rw [V.nativeRestrictionDegreeOfOrdinaryBase_eq_neg_integral hreg hN _ (d t) hd,
    V.nativeRestrictionDegreeOfOrdinaryBase_eq_neg_integral hreg hN A t ht]
  exact congrArg (fun a : ℝ => -a)
    (V.toNormFamily.scalarExtension_restrict_determinant_integral_logNorm_algEquiv σ A t)

/-- Every actual native degree appears on both sides of the genuine subspace
bijection, so the entire extended-real supremum is preserved. -/
theorem iSup_nativeRestrictionDegreeOfOrdinaryBase_algEquiv (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (σ : L ≃ₐ[K] M) :
    (⨆ B : Submodule M (M ⊗[K] E),
      (V.nativeRestrictionDegreeOfOrdinaryBase hreg hN B : EReal)) =
    ⨆ A : Submodule L (L ⊗[K] E),
      (V.nativeRestrictionDegreeOfOrdinaryBase hreg hN A : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro B
    rw [← V.nativeRestrictionDegreeOfOrdinaryBase_algEquiv hreg hN σ.symm B]
    exact le_iSup (fun A : Submodule L (L ⊗[K] E) =>
      (V.nativeRestrictionDegreeOfOrdinaryBase hreg hN A : EReal)) _
  · apply iSup_le
    intro A
    rw [← V.nativeRestrictionDegreeOfOrdinaryBase_algEquiv hreg hN σ A]
    exact le_iSup (fun B : Submodule M (M ⊗[K] E) =>
      (V.nativeRestrictionDegreeOfOrdinaryBase hreg hN B : EReal)) _

/-- Rank preservation reindexes every actual positive-rank native mean,
without requiring that either supremum be attained. -/
theorem iSup_nativeMeanOfOrdinaryBase_algEquiv (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (σ : L ≃ₐ[K] M) :
    (⨆ B : {B : Submodule M (M ⊗[K] E) // 0 < Module.finrank M B},
      (V.nativeRestrictionDegreeOfOrdinaryBase hreg hN B.val /
        (Module.finrank M B.val : ℝ) : EReal)) =
    ⨆ A : {A : Submodule L (L ⊗[K] E) // 0 < Module.finrank L A},
      (V.nativeRestrictionDegreeOfOrdinaryBase hreg hN A.val /
        (Module.finrank L A.val : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro B
    let A := scalarExtensionSubspaceOrderIso (E := E) σ.symm B.val
    have hr : Module.finrank L A = Module.finrank M B.val :=
      scalarExtensionSubspaceOrderIso_finrank σ.symm B.val
    have hd := V.nativeRestrictionDegreeOfOrdinaryBase_algEquiv hreg hN σ.symm B.val
    have hA : 0 < Module.finrank L A := hr.symm ▸ B.property
    exact (le_of_eq (by rw [← hd, ← hr])).trans
      (le_iSup (fun A : {A : Submodule L (L ⊗[K] E) // 0 < Module.finrank L A} =>
        (V.nativeRestrictionDegreeOfOrdinaryBase hreg hN A.val /
          (Module.finrank L A.val : ℝ) : EReal)) ⟨A, hA⟩)
  · apply iSup_le
    intro A
    let B := scalarExtensionSubspaceOrderIso (E := E) σ A.val
    have hr : Module.finrank M B = Module.finrank L A.val :=
      scalarExtensionSubspaceOrderIso_finrank σ A.val
    have hd := V.nativeRestrictionDegreeOfOrdinaryBase_algEquiv hreg hN σ A.val
    have hB : 0 < Module.finrank M B := hr.symm ▸ A.property
    exact (le_of_eq (by rw [← hd, ← hr])).trans
      (le_iSup (fun B : {B : Submodule M (M ⊗[K] E) // 0 < Module.finrank M B} =>
        (V.nativeRestrictionDegreeOfOrdinaryBase hreg hN B.val /
          (Module.finrank M B.val : ℝ) : EReal)) ⟨B, hB⟩)

/-- The existing discrete absolute positive degree is computed over every
actual algebraic closure, with original regularity only. -/
theorem absolutePositiveDegreeOfCountableDiscreteBase_eq_iSup_of_isAlgClosed
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.absolutePositiveDegreeOfCountableDiscreteBase hN =
      ⨆ B : Submodule M (M ⊗[K] E),
        (V.nativeRestrictionDegreeOfCountableDiscreteBase hN B : EReal) := by
  let : IsAlgClosure K M := ⟨inferInstance, inferInstance⟩
  let σ := IsAlgClosure.equiv K (AlgebraicClosure K) M
  exact (V.iSup_nativeRestrictionDegreeOfOrdinaryBase_algEquiv
    (Or.inr ⟨inferInstance, inferInstance⟩) hN σ).symm

/-- Closure choice also preserves all actual positive-rank native means,
including the empty supremum convention in rank zero. -/
theorem absoluteMaximalSlopeOfCountableDiscreteBase_eq_iSup_of_isAlgClosed
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.absoluteMaximalSlopeOfCountableDiscreteBase hN =
      ⨆ B : {B : Submodule M (M ⊗[K] E) // 0 < Module.finrank M B},
        (V.nativeRestrictionDegreeOfCountableDiscreteBase hN B.val /
          (Module.finrank M B.val : ℝ) : EReal) := by
  let : IsAlgClosure K M := ⟨inferInstance, inferInstance⟩
  let σ := IsAlgClosure.equiv K (AlgebraicClosure K) M
  exact (V.iSup_nativeMeanOfOrdinaryBase_algEquiv
    (Or.inr ⟨inferInstance, inferInstance⟩) hN σ).symm

end ArakelovGeometry.AdelicVectorBundle
