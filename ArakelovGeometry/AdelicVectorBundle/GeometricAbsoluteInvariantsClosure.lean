/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.GeometricAbsoluteInvariants
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionIsomorphismDeterminantRational
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.EquivMeasure

/-!
# Actual geometric absolute invariants and closure choice

The canonical native bundle remains on the actual subspace. Its rational
restriction determinant and the genuine measure-preserving place map transport
its degree. The resulting bijection of all native subspaces identifies both
absolute suprema on every algebraic closure, without target-place regularity.
-/

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
variable {K L M E : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] {S : AdelicStructure K}

/-- The rational determinant of the actual restriction is transported directly
on the subspace, in every rank. -/
def scalarExtensionRestrictionDeterminantEquiv (σ : L ≃ₐ[K] M)
    (A : Submodule L (L ⊗[K] E)) :
    letI := RingHomInvPair.of_ringEquiv σ.toRingEquiv
    letI := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
    (⋀[L]^(Module.finrank L A) A) ≃ₛₗ[(σ.toRingEquiv : L →+* M)]
      (⋀[M]^(Module.finrank M (scalarExtensionSubspaceOrderIso (E := E) σ A))
        (scalarExtensionSubspaceOrderIso (E := E) σ A)) := by
  let := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  exact determinantSemilinearEquiv σ.toRingEquiv
    (scalarExtensionSubspaceSemilinearEquiv σ A)
    (scalarExtensionSubspaceOrderIso_finrank σ A).symm

namespace NormFamily
open AdelicStructure.ParameterSpaceExtension
variable [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K M]

local instance geometricClosureMeasurableSpaceL :
    MeasurableSpace (AdelicStructure.ParameterSpaceExtension S L) :=
  (S.algebraicExtension L).instMeasurableSpaceΩ
local instance geometricClosureMeasurableSpaceM :
    MeasurableSpace (AdelicStructure.ParameterSpaceExtension S M) :=
  (S.algebraicExtension M).instMeasurableSpaceΩ

/-- Actual restricted determinant norms follow the prescribed rational map
on every completed coefficient and every determinant vector. -/
theorem scalarExtension_restrict_determinant_norm_tmul_algEquiv
    (ξ : NormFamily S E) (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M)
    (A : Submodule L (L ⊗[K] E))
    (a : (pullbackAlgEquiv S σ x).abv.Completion)
    (z : ⋀[L]^(Module.finrank L A) A) :
    ((ξ.scalarExtension (L := M)).restrict
      (scalarExtensionSubspaceOrderIso (E := E) σ A)).determinant.norm x
        (algEquivCompletedFields S σ x a ⊗ₜ[M]
          scalarExtensionRestrictionDeterminantEquiv σ A z) =
      ((ξ.scalarExtension (L := L)).restrict A).determinant.norm
        (pullbackAlgEquiv S σ x) (a ⊗ₜ[L] z) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
    (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  let := RingHomInvPair.of_ringEquiv (algEquivCompletedFields S σ x).toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm (algEquivCompletedFields S σ x).toRingEquiv
  let η := (ξ.scalarExtension (L := L)).restrict A
  let θ := (ξ.scalarExtension (L := M)).restrict
    (scalarExtensionSubspaceOrderIso (E := E) σ A)
  let τ := (algEquivCompletedFields S σ x).toRingEquiv
  let e := completedScalarExtensionRestrictionEquiv σ x A
  let hr := (scalarExtensionSubspaceOrderIso_finrank σ A).symm
  have ht := completedDeterminantSemilinearEquiv_tmul σ.toRingEquiv τ
    (scalarExtensionSubspaceSemilinearEquiv σ A) e hr
    (algEquivCompletedFields_algebraMap S σ x)
    (completedScalarExtensionRestrictionEquiv_tmul σ x A) a z
  have hτ : ∀ b, ‖τ b‖ = ‖b‖ :=
    (isometry_algEquivCompletedFields S σ x).norm_map_of_map_zero
      (map_zero (algEquivCompletedFields S σ x))
  have he : ∀ v, θ.norm x (e v) = η.norm (pullbackAlgEquiv S σ x) v :=
    ξ.scalarExtension_restrict_norm_algEquiv σ x A
  have hn := completedDeterminantSeminorm_norm_eq τ
    (η.norm (pullbackAlgEquiv S σ x)) (η.determinant.norm (pullbackAlgEquiv S σ x))
    (θ.norm x) (θ.determinant.norm x) e hr hτ he
    (fun z ε hε ↦ η.exists_smul_determinant_ιMulti_norm_lt (pullbackAlgEquiv S σ x) z hε)
    (fun z ε hε ↦ θ.exists_smul_determinant_ιMulti_norm_lt x z hε)
    (η.determinant_norm_ιMulti_le (pullbackAlgEquiv S σ x))
    (θ.determinant_norm_ιMulti_le x) (a ⊗ₜ[L] z)
  exact (congrArg (θ.determinant.norm x) ht).symm.trans hn

/-- The genuine measure-preserving place equivalence identifies the actual
restriction determinant integrals. -/
theorem scalarExtension_restrict_determinant_integral_logNorm_algEquiv
    (ξ : NormFamily S E) (σ : L ≃ₐ[K] M)
    (A : Submodule L (L ⊗[K] E)) (z : ⋀[L]^(Module.finrank L A) A) :
    (∫ x, ((ξ.scalarExtension (L := M)).restrict
      (scalarExtensionSubspaceOrderIso (E := E) σ A)).determinant.logNorm
        (scalarExtensionRestrictionDeterminantEquiv σ A z) x ∂(S.algebraicExtension M).v) =
      ∫ y, ((ξ.scalarExtension (L := L)).restrict A).determinant.logNorm z y
        ∂(S.algebraicExtension L).v := by
  let η := (ξ.scalarExtension (L := L)).restrict A
  let θ := (ξ.scalarExtension (L := M)).restrict
    (scalarExtensionSubspaceOrderIso (E := E) σ A)
  let d := scalarExtensionRestrictionDeterminantEquiv σ A
  have hn : ∀ x : AdelicStructure.ParameterSpaceExtension S M,
      θ.determinant.logNorm (d z) x = η.determinant.logNorm z (pullbackAlgEquiv S σ x) := by
    intro x
    change Real.log (θ.determinant.norm x (1 ⊗ₜ[M] d z)) =
      Real.log (η.determinant.norm (pullbackAlgEquiv S σ x) (1 ⊗ₜ[L] z))
    have h := ξ.scalarExtension_restrict_determinant_norm_tmul_algEquiv σ x A 1 z
    simp only [map_one] at h
    exact congrArg Real.log h
  calc
    (∫ x, θ.determinant.logNorm (d z) x ∂(S.algebraicExtension M).v) =
        ∫ x, η.determinant.logNorm z (pullbackAlgEquiv S σ x)
          ∂(S.algebraicExtension M).v :=
      integral_congr_ae (Filter.Eventually.of_forall hn)
    _ = ∫ y, η.determinant.logNorm z y ∂(S.algebraicExtension L).v :=
      (AdelicStructure.Algebraic.measurePreserving_algEquivMeasurableEquiv S σ).integral_comp
        (algEquivMeasurableEquiv S σ).measurableEmbedding _

variable [S.IsProper] [IsAlgClosed L] [IsAlgClosed M]
  [MeasurableSingletonClass S.Ω]

/-- Produced native determinant measurability and actual rational integral
transport preserve the degree on the literal native subspace. -/
theorem nativeAlgebraicRestrictionDegreeOfPositiveAtoms_algEquiv
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (σ : L ≃ₐ[K] M) (A : Submodule L (L ⊗[K] E)) :
    ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms hξ hpos hS
      (scalarExtensionSubspaceOrderIso (E := E) σ A) =
      ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms hξ hpos hS A := by
  let := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  let t := determinantGenerator (K := L) (E := A)
  have ht : t ≠ 0 := determinantGenerator_ne_zero
  let d := scalarExtensionRestrictionDeterminantEquiv σ A
  have hd : d t ≠ 0 := by
    intro h
    apply ht
    apply d.injective
    simpa only [map_zero] using h
  rw [ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms_eq_neg_integral
    hξ hpos hS _ (d t) hd,
    ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms_eq_neg_integral
      hξ hpos hS A t ht]
  exact congrArg (fun a : ℝ => -a)
    (ξ.scalarExtension_restrict_determinant_integral_logNorm_algEquiv σ A t)

/-- Every native subspace is transported, so the entire positive-degree
supremum is preserved without an attainment assumption. -/
theorem iSup_nativeAlgebraicRestrictionDegreeOfPositiveAtoms_algEquiv
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (σ : L ≃ₐ[K] M) :
    (⨆ B : Submodule M (M ⊗[K] E),
      (ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms hξ hpos hS B : EReal)) =
    ⨆ A : Submodule L (L ⊗[K] E),
      (ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms hξ hpos hS A : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro B
    rw [← ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms_algEquiv hξ hpos hS σ.symm B]
    exact le_iSup (fun A : Submodule L (L ⊗[K] E) =>
      (ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms hξ hpos hS A : EReal)) _
  · apply iSup_le
    intro A
    rw [← ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms_algEquiv hξ hpos hS σ A]
    exact le_iSup (fun B : Submodule M (M ⊗[K] E) =>
      (ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms hξ hpos hS B : EReal)) _

/-- Positive-rank native means are transported in both directions, including
an empty index set. -/
theorem iSup_nativeMeanOfPositiveAtoms_algEquiv
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (σ : L ≃ₐ[K] M) :
    (⨆ B : {B : Submodule M (M ⊗[K] E) // 0 < Module.finrank M B},
      (ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms hξ hpos hS B.val /
        (Module.finrank M B.val : ℝ) : EReal)) =
    ⨆ A : {A : Submodule L (L ⊗[K] E) // 0 < Module.finrank L A},
      (ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms hξ hpos hS A.val /
        (Module.finrank L A.val : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro B
    let A := scalarExtensionSubspaceOrderIso (E := E) σ.symm B.val
    have hr : Module.finrank L A = Module.finrank M B.val :=
      scalarExtensionSubspaceOrderIso_finrank σ.symm B.val
    have hd := ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms_algEquiv
      hξ hpos hS σ.symm B.val
    have hA : 0 < Module.finrank L A := hr.symm ▸ B.property
    exact (le_of_eq (by rw [← hd, ← hr])).trans
      (le_iSup (fun A : {A : Submodule L (L ⊗[K] E) // 0 < Module.finrank L A} =>
        (ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms hξ hpos hS A.val /
          (Module.finrank L A.val : ℝ) : EReal)) ⟨A, hA⟩)
  · apply iSup_le
    intro A
    let B := scalarExtensionSubspaceOrderIso (E := E) σ A.val
    have hr : Module.finrank M B = Module.finrank L A.val :=
      scalarExtensionSubspaceOrderIso_finrank σ A.val
    have hd := ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms_algEquiv
      hξ hpos hS σ A.val
    have hB : 0 < Module.finrank M B := hr.symm ▸ A.property
    exact (le_of_eq (by rw [← hd, ← hr])).trans
      (le_iSup (fun B : {B : Submodule M (M ⊗[K] E) // 0 < Module.finrank M B} =>
        (ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms hξ hpos hS B.val /
          (Module.finrank M B.val : ℝ) : EReal)) ⟨B, hB⟩)

/-- The geometric absolute positive degree is computed over every algebraic
closure through its actual native restrictions. -/
theorem absolutePositiveDegreeOfPositiveAtoms_eq_iSup_of_isAlgClosed
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    ξ.absolutePositiveDegreeOfPositiveAtoms hξ hpos hS =
      ⨆ A : Submodule L (L ⊗[K] E),
        (ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms hξ hpos hS A : EReal) := by
  let : IsAlgClosure K L := ⟨inferInstance, inferInstance⟩
  exact (ξ.iSup_nativeAlgebraicRestrictionDegreeOfPositiveAtoms_algEquiv hξ hpos hS
    (IsAlgClosure.equiv K (AlgebraicClosure K) L)).symm

/-- The geometric absolute maximal slope is computed over every algebraic
closure, with its existing empty-supremum convention. -/
theorem absoluteMaximalSlopeOfPositiveAtoms_eq_iSup_of_isAlgClosed
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    ξ.absoluteMaximalSlopeOfPositiveAtoms hξ hpos hS =
      ⨆ A : {A : Submodule L (L ⊗[K] E) // 0 < Module.finrank L A},
        (ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms hξ hpos hS A.val /
          (Module.finrank L A.val : ℝ) : EReal) := by
  let : IsAlgClosure K L := ⟨inferInstance, inferInstance⟩
  exact (ξ.iSup_nativeMeanOfPositiveAtoms_algEquiv hξ hpos hS
    (IsAlgClosure.equiv K (AlgebraicClosure K) L)).symm

end NormFamily
end ArakelovGeometry
