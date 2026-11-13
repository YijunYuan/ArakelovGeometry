/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Algebraic.ClosureApproximation
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Discrete.Native.SubquotientDegree
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Isomorphism.DeterminantRational

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.EquivMeasure
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual determinant degree under scalar-field isomorphisms

The produced rational determinant map intertwines log norms along the actual
measure-preserving place equivalence. Target determinant measurability and
native subquotient degrees follow from these two transport producers.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
variable {K L M E : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [AddCommGroup E] [Module K E]
  {S : AdelicStructure K} [FiniteDimensional K E]
  [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K M]

namespace NormFamily
open AdelicStructure.ParameterSpaceExtension

local instance : MeasurableSpace (AdelicStructure.ParameterSpaceExtension S L) :=
  (S.algebraicExtension L).instMeasurableSpaceΩ
local instance : MeasurableSpace (AdelicStructure.ParameterSpaceExtension S M) :=
  (S.algebraicExtension M).instMeasurableSpaceΩ

/-- The actual rational determinant equivalence and place map produce target
determinant measurability from the source determinant alone. -/
theorem scalarExtension_subquotient_determinant_isMeasurable_algEquiv
    (ξ : NormFamily S E) (σ : L ≃ₐ[K] M)
    (B T : Submodule L (L ⊗[K] E)) (hTB : T ≤ B)
    [hdet : (((ξ.scalarExtension (L := L)).restrict B).quotient
      (T.comap B.subtype)).determinant.IsMeasurable] :
    (((ξ.scalarExtension (L := M)).restrict
      (scalarExtensionSubspaceOrderIso (E := E) σ B)).quotient
        ((scalarExtensionSubspaceOrderIso (E := E) σ T).comap
          (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype)).determinant.IsMeasurable := by
  let η := ((ξ.scalarExtension (L := L)).restrict B).quotient (T.comap B.subtype)
  let θ := ((ξ.scalarExtension (L := M)).restrict
    (scalarExtensionSubspaceOrderIso (E := E) σ B)).quotient
      ((scalarExtensionSubspaceOrderIso (E := E) σ T).comap
        (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype)
  let d := scalarExtensionSubquotientDeterminantEquiv σ B T
  change θ.determinant.IsMeasurable
  constructor
  intro z
  have hn : (fun x : AdelicStructure.ParameterSpaceExtension S M =>
      θ.determinant.norm x (1 ⊗ₜ[M] z)) =
      (fun x : AdelicStructure.ParameterSpaceExtension S M =>
        η.determinant.norm (pullbackAlgEquiv S σ x) (1 ⊗ₜ[L] d.symm z)) := by
    funext x
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    have h := ξ.scalarExtension_subquotient_determinant_norm_tmul_algEquiv
      σ x B T hTB 1 (d.symm z)
    have hd : scalarExtensionSubquotientDeterminantEquiv σ B T (d.symm z) = z :=
      d.apply_symm_apply z
    simp only [map_one, hd] at h
    dsimp only [θ, η]
    exact h
  change Measurable (fun x : AdelicStructure.ParameterSpaceExtension S M =>
    θ.determinant.norm x (1 ⊗ₜ[M] z))
  rw [hn]
  exact (hdet (d.symm z)).comp (algEquivMeasurableEquiv S σ).measurable

/-- Actual determinant logarithm integrals commute with the produced rational
map and the genuine measure-preserving place equivalence, in every rank. -/
theorem scalarExtension_subquotient_determinant_integral_logNorm_algEquiv
    (ξ : NormFamily S E) (σ : L ≃ₐ[K] M)
    (B T : Submodule L (L ⊗[K] E)) (hTB : T ≤ B)
    (z : ⋀[L]^(Module.finrank L (B ⧸ T.comap B.subtype)) (B ⧸ T.comap B.subtype)) :
    (∫ x, (((ξ.scalarExtension (L := M)).restrict
      (scalarExtensionSubspaceOrderIso (E := E) σ B)).quotient
        ((scalarExtensionSubspaceOrderIso (E := E) σ T).comap
          (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype)).determinant.logNorm
            (scalarExtensionSubquotientDeterminantEquiv σ B T z) x
              ∂(S.algebraicExtension M).v) =
      ∫ y, (((ξ.scalarExtension (L := L)).restrict B).quotient
        (T.comap B.subtype)).determinant.logNorm z y ∂(S.algebraicExtension L).v := by
  let η := ((ξ.scalarExtension (L := L)).restrict B).quotient (T.comap B.subtype)
  let θ := ((ξ.scalarExtension (L := M)).restrict
    (scalarExtensionSubspaceOrderIso (E := E) σ B)).quotient
      ((scalarExtensionSubspaceOrderIso (E := E) σ T).comap
        (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype)
  let d := scalarExtensionSubquotientDeterminantEquiv σ B T
  change (∫ x, θ.determinant.logNorm (d z) x ∂(S.algebraicExtension M).v) =
    ∫ y, η.determinant.logNorm z y ∂(S.algebraicExtension L).v
  have hn : (fun x : AdelicStructure.ParameterSpaceExtension S M =>
      θ.determinant.logNorm (d z) x) =
      (fun x : AdelicStructure.ParameterSpaceExtension S M =>
        η.determinant.logNorm z (pullbackAlgEquiv S σ x)) := by
    funext x
    change Real.log (θ.determinant.norm x (1 ⊗ₜ[M] d z)) =
      Real.log (η.determinant.norm (pullbackAlgEquiv S σ x) (1 ⊗ₜ[L] z))
    dsimp only [θ, η, d]
    exact ξ.scalarExtension_subquotient_determinant_log_norm_algEquiv σ x B T hTB z
  calc
    (∫ x, θ.determinant.logNorm (d z) x ∂(S.algebraicExtension M).v) =
        ∫ x, η.determinant.logNorm z (pullbackAlgEquiv S σ x)
          ∂(S.algebraicExtension M).v :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => congrFun hn x)
    _ = ∫ y, η.determinant.logNorm z y ∂(S.algebraicExtension L).v :=
      (AdelicStructure.Algebraic.measurePreserving_algEquivMeasurableEquiv S σ).integral_comp
        (algEquivMeasurableEquiv S σ).measurableEmbedding _

end NormFamily

namespace AdelicVectorBundle
variable [IsAlgClosed L] [IsAlgClosed M]
  [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]

/-- The actual native subquotient degree is preserved under any prescribed
isomorphism of algebraic closures. Both determinant measurability proofs come
from finite-stage descent; the equality follows by transporting the logarithm integral. -/
theorem degree_nativeSubquotientOfCountableDiscreteBase_algEquiv [S.IsProper]
    (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized]
    (σ : L ≃ₐ[K] M) (B T : Submodule L (L ⊗[K] V)) (hTB : T ≤ B) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
    let hdetL := V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase_determinant_isMeasurable
      B (T.comap B.subtype)
    let hdetM := V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase_determinant_isMeasurable
      (L := M) (scalarExtensionSubspaceOrderIso (E := V) σ B)
      ((scalarExtensionSubspaceOrderIso (E := V) σ T).comap
        (scalarExtensionSubspaceOrderIso (E := V) σ B).subtype)
    (V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase (L := M)
      (scalarExtensionSubspaceOrderIso (E := V) σ B)
      ((scalarExtensionSubspaceOrderIso (E := V) σ T).comap
        (scalarExtensionSubspaceOrderIso (E := V) σ B).subtype)).degreeOfMeasurableDeterminant
          (hdet := hdetM) =
    (V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase (L := L) B
      (T.comap B.subtype)).degreeOfMeasurableDeterminant
        (hdet := hdetL) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  let hNL := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
  let hNM := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := M)
  let U := V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase (L := L) B
    (T.comap B.subtype)
  let W := V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase (L := M)
    (scalarExtensionSubspaceOrderIso (E := V) σ B)
    ((scalarExtensionSubspaceOrderIso (E := V) σ T).comap
      (scalarExtensionSubspaceOrderIso (E := V) σ B).subtype)
  let hdetU : U.toNormFamily.determinant.IsMeasurable :=
    V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase_determinant_isMeasurable
      B (T.comap B.subtype)
  let hdetW : W.toNormFamily.determinant.IsMeasurable :=
    V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase_determinant_isMeasurable
      (L := M) (scalarExtensionSubspaceOrderIso (E := V) σ B)
      ((scalarExtensionSubspaceOrderIso (E := V) σ T).comap
        (scalarExtensionSubspaceOrderIso (E := V) σ B).subtype)
  change W.degreeOfMeasurableDeterminant (hN := ⟨hNM⟩) =
    U.degreeOfMeasurableDeterminant (hN := ⟨hNL⟩)
  let s := (U.determinant (hS := ⟨hNL⟩)).lineGenerator
  let d := scalarExtensionSubquotientDeterminantEquiv σ B T
  have hd : d s.val ≠ 0 := by
    intro h
    apply s.property
    apply d.injective
    simpa only [map_zero] using h
  have hi : (∫ x, W.toNormFamily.determinant.logNorm (d s.val) x
      ∂(S.algebraicExtension M).v) =
      ∫ y, U.toNormFamily.determinant.logNorm s.val y ∂(S.algebraicExtension L).v := by
    dsimp only [U, W, d]
    exact V.toNormFamily.scalarExtension_subquotient_determinant_integral_logNorm_algEquiv
      σ B T hTB s.val
  exact (degreeOfMeasurableDeterminant_eq_neg_integral W (hN := ⟨hNM⟩) ⟨d s.val, hd⟩).trans
    ((congrArg (fun a : ℝ => -a) hi).trans
      (degreeOfMeasurableDeterminant_eq_neg_integral U (hN := ⟨hNL⟩) s).symm)

omit [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] in
/-- The actual ordinary native subquotient degrees agree under scalar-field
isomorphism when the original curve has a common countable dense subfield.
Both extended degree contexts are produced from the original curve. -/
theorem degree_nativeSubquotient_algEquiv [S.IsProper]
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (σ : L ≃ₐ[K] M) (B T : Submodule L (L ⊗[K] V)) (hTB : T ≤ B) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
    let _ := hcount.algebraicExtension_of_isAlgClosed (L := L)
    let _ := hcount.algebraicExtension_of_isAlgClosed (L := M)
    (((V.scalarExtension (L := M)).restrictOfMeasurableBase
      (scalarExtensionSubspaceOrderIso (E := V) σ B)).quotientOfMeasurableBase
        ((scalarExtensionSubspaceOrderIso (E := V) σ T).comap
          (scalarExtensionSubspaceOrderIso (E := V) σ B).subtype)).degree
            (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M))⟩) =
    (((V.scalarExtension (L := L)).restrictOfMeasurableBase
      B).quotientOfMeasurableBase (T.comap B.subtype)).degree
        (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
  let hM := hcount.algebraicExtension_of_isAlgClosed (L := M)
  let hNL := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
  let hNM := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := M)
  let U := ((V.scalarExtension (L := L)).restrictOfMeasurableBase B
   ).quotientOfMeasurableBase (T.comap B.subtype)
  let W := ((V.scalarExtension (L := M)).restrictOfMeasurableBase
    (scalarExtensionSubspaceOrderIso (E := V) σ B)).quotientOfMeasurableBase
      ((scalarExtensionSubspaceOrderIso (E := V) σ T).comap
        (scalarExtensionSubspaceOrderIso (E := V) σ B).subtype)
  change W.degree (hN := ⟨hNM⟩) = U.degree (hN := ⟨hNL⟩)
  let s := (U.determinantOfMeasurableBase (hN := ⟨hNL⟩)).lineGenerator
    (hV := (U.determinantOfMeasurableBase_isLine (hN := ⟨hNL⟩)))
  let d := scalarExtensionSubquotientDeterminantEquiv σ B T
  have hd : d s.val ≠ 0 := by
    intro h
    apply s.property
    apply d.injective
    simpa only [map_zero] using h
  have hi : (∫ x, W.toNormFamily.determinant.logNorm (d s.val) x
      ∂(S.algebraicExtension M).v) =
      ∫ y, U.toNormFamily.determinant.logNorm s.val y ∂(S.algebraicExtension L).v := by
    dsimp only [U, W, d]
    exact V.toNormFamily.scalarExtension_subquotient_determinant_integral_logNorm_algEquiv
      σ B T hTB s.val
  exact (degree_eq_neg_integral W (hN := ⟨hNM⟩) ⟨d s.val, hd⟩).trans
    ((congrArg (fun a : ℝ => -a) hi).trans
      (degree_eq_neg_integral U (hN := ⟨hNL⟩) s).symm)

end AdelicVectorBundle
end ArakelovGeometry
