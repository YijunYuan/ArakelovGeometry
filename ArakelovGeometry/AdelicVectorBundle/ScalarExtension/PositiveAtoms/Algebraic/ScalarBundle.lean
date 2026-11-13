/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Determinant.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Degree

import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Domination.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.Algebraic.ScalarExtensionMeasurable

/-!
# Genuine positive-atomic ordinary algebraic scalar bundles

Actual primal and completed-dual regularity constructs the canonical adelic
bundle on ordinary algebraic scalar extension. Its measurable-determinant
degree is unchanged when the original determinant is measurable.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [MeasurableSingletonClass S.Ω]

namespace NormFamily

/-- The existing adelic bundle on the genuine ordinary algebraic scalar
family, with both regularities produced from original domination alone. -/
abbrev algebraicScalarBundleOfPositiveAtoms (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces] :
    AdelicVectorBundle (S.algebraicExtension L) where
  carrier := (L ⊗[K] E)
  toNormFamily := ξ.scalarExtension (L := L)
  toIsAdelic := {
    isMeasurable := by
      exact hξ.scalarExtension_isMeasurable_of_positive_atoms_of_isAlgebraic ξ
    dual_isMeasurable := by
      exact hξ.scalarExtension_dual_isMeasurable_of_positive_atoms_of_isAlgebraic ξ
    isDominated := by
      exact (hξ.scalarExtension_isStronglyDominated ξ
        (AdelicStructure.v_Ωinf_lt_top_of_forall_mem_Ωfin)).isDominated
  }

@[simp]
theorem algebraicScalarBundleOfPositiveAtoms_toNormFamily
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces] :
    (ξ.algebraicScalarBundleOfPositiveAtoms (L := L)).toNormFamily =
      ξ.scalarExtension (L := L) := rfl

/-- Ordinary algebraic scalar extension is strongly adelic on the actual
completed fibres, independently of original strong domination or regularity. -/
theorem algebraicScalarBundleOfPositiveAtoms_isStronglyAdelic
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces] :
    (ξ.algebraicScalarBundleOfPositiveAtoms (L := L)).IsStronglyAdelic :=
  hξ.scalarExtension_isStronglyDominated ξ (AdelicStructure.v_Ωinf_lt_top_of_forall_mem_Ωfin)

end NormFamily
namespace AdelicVectorBundle

/-- The actual positive-atomic ordinary scalar bundle preserves canonical
measurable-determinant degree, without density or discreteness assumptions. -/
theorem degreeOfMeasurableDeterminant_algebraicScalarBundleOfPositiveAtoms [S.IsProper]
    (V : AdelicVectorBundle S)
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces]
    [hdet : V.toNormFamily.determinant.IsMeasurable]
    [hN : S.IsArchimedeanNormalized] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.toNormFamily.algebraicScalarBundleOfPositiveAtoms (L := L)
     ).degreeOfMeasurableDeterminant (hdet := hdet.determinant_scalarExtension)
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
    V.degreeOfMeasurableDeterminant := by
  intro hp
  let := hp
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
  let D := V.determinant
  let hD := V.determinant_isLine
  let W := D.scalarExtensionLine (L := L) (hV := hD)
  let hW := D.scalarExtensionLine_isLine (L := L) (hV := hD)
  let B := V.toNormFamily.algebraicScalarBundleOfPositiveAtoms (L := L)
  let U := B.determinant (hm := hdet.determinant_scalarExtension) (hS := ⟨hLN⟩)
  let hU := B.determinant_isLine (hm := hdet.determinant_scalarExtension) (hS := ⟨hLN⟩)
  have hd : W.lineDegree (hV := hW) = U.lineDegree (hV := hU) := by
    apply lineDegree_eq_of_norm_rational_eq W U (hV := hW) (hW := hU)
      (determinantScalarExtensionEquiv K L V)
    intro x s
    change S.ParameterSpaceExtension L at x
    change (V.toNormFamily.determinant.scalarExtension (L := L)).norm x
        ((1 : x.abv.Completion) ⊗ₜ[L] s) =
      (V.toNormFamily.scalarExtension (L := L)).determinant.norm x
        ((1 : x.abv.Completion) ⊗ₜ[L] determinantScalarExtensionEquiv K L V s)
    have h := V.toNormFamily.determinant_scalarExtension_norm_eq x
      ((1 : x.abv.Completion) ⊗ₜ[L] determinantScalarExtensionEquiv K L V s)
    have he :
        ((determinantScalarExtensionEquiv K L V).symm.toLinearMap.baseChange
          x.abv.Completion)
            ((1 : x.abv.Completion) ⊗ₜ[L] determinantScalarExtensionEquiv K L V s) =
          (1 : x.abv.Completion) ⊗ₜ[L] s := by
      rw [LinearMap.baseChange_tmul]
      exact congrArg (fun t => (1 : x.abv.Completion) ⊗ₜ[L] t)
        ((determinantScalarExtensionEquiv K L V).symm_apply_apply s)
    exact (h.trans (congrArg
      ((V.toNormFamily.determinant.scalarExtension (L := L)).norm x) he)).symm
  change U.lineDegree (hV := hU) = D.lineDegree (hV := hD)
  exact hd.symm.trans (D.lineDegree_scalarExtensionLine (hV := hD))

end AdelicVectorBundle
end ArakelovGeometry
