/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DegreeDeterminant
public import ArakelovGeometry.AdelicVectorBundle.GeometricAlgebraicScalarExtensionMeasurable
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDegree

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

omit [MeasurableSingletonClass S.Ω] in
/-- The archimedean locus has finite measure when every place is nonarchimedean. -/
theorem positiveAtomicScalar_infinity_measure_lt_top
    (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) : S.v S.Ωinf < ⊤ := by
  have hinf : S.Ωinf = ∅ := by
    ext ω
    exact ⟨fun h => False.elim (h (hS ω)), fun h => False.elim h⟩
  rw [hinf, measure_empty]
  exact ENNReal.zero_lt_top

/-- The existing adelic bundle on the genuine ordinary algebraic scalar
family, with both regularities produced from original domination alone. -/
def algebraicScalarBundleOfPositiveAtoms (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    AdelicVectorBundle (S.algebraicExtension L) (L ⊗[K] E) where
  toNormFamily := ξ.scalarExtension (L := L)
  isMeasurable := hξ.scalarExtension_isMeasurable_of_positive_atoms_of_isAlgebraic ξ hpos hS
  dual_isMeasurable :=
    hξ.scalarExtension_dual_isMeasurable_of_positive_atoms_of_isAlgebraic ξ hpos hS
  isDominated := (hξ.scalarExtension_isStronglyDominated ξ
    (positiveAtomicScalar_infinity_measure_lt_top hS)).isDominated

@[simp]
theorem algebraicScalarBundleOfPositiveAtoms_toNormFamily
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    (ξ.algebraicScalarBundleOfPositiveAtoms (L := L) hξ hpos hS).toNormFamily =
      ξ.scalarExtension (L := L) := rfl

/-- Ordinary algebraic scalar extension is strongly adelic on the actual
completed fibres, independently of original strong domination or regularity. -/
theorem algebraicScalarBundleOfPositiveAtoms_isStronglyAdelic
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    (ξ.algebraicScalarBundleOfPositiveAtoms (L := L) hξ hpos hS).IsStronglyAdelic :=
  hξ.scalarExtension_isStronglyDominated ξ (positiveAtomicScalar_infinity_measure_lt_top hS)

end NormFamily
namespace AdelicVectorBundle

/-- The actual positive-atomic ordinary scalar bundle preserves canonical
measurable-determinant degree, without density or discreteness assumptions. -/
theorem degreeOfMeasurableDeterminant_algebraicScalarBundleOfPositiveAtoms [S.IsProper]
    (V : AdelicVectorBundle S E)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (hdet : V.toNormFamily.determinant.IsMeasurable)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.toNormFamily.algebraicScalarBundleOfPositiveAtoms (L := L)
      V.isDominated hpos hS).degreeOfMeasurableDeterminant hdet.determinant_scalarExtension
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) =
    V.degreeOfMeasurableDeterminant hdet hN := by
  intro hp
  let := hp
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
  let D := V.determinant hdet hN
  let hD := V.determinant_isLine hdet hN
  let W := D.scalarExtensionLine (L := L) hD
  let hW := D.scalarExtensionLine_isLine (L := L) hD
  let B := V.toNormFamily.algebraicScalarBundleOfPositiveAtoms (L := L)
    V.isDominated hpos hS
  let U := B.determinant hdet.determinant_scalarExtension hLN
  let hU := B.determinant_isLine hdet.determinant_scalarExtension hLN
  have hd : W.lineDegree hW = U.lineDegree hU := by
    apply lineDegree_eq_of_norm_rational_eq W U hW hU
      (determinantScalarExtensionEquiv K L E)
    intro x s
    change S.ParameterSpaceExtension L at x
    change (V.toNormFamily.determinant.scalarExtension (L := L)).norm x
        ((1 : x.abv.Completion) ⊗ₜ[L] s) =
      (V.toNormFamily.scalarExtension (L := L)).determinant.norm x
        ((1 : x.abv.Completion) ⊗ₜ[L] determinantScalarExtensionEquiv K L E s)
    have h := V.toNormFamily.determinant_scalarExtension_norm_eq x
      ((1 : x.abv.Completion) ⊗ₜ[L] determinantScalarExtensionEquiv K L E s)
    have he :
        ((determinantScalarExtensionEquiv K L E).symm.toLinearMap.baseChange
          x.abv.Completion)
            ((1 : x.abv.Completion) ⊗ₜ[L] determinantScalarExtensionEquiv K L E s) =
          (1 : x.abv.Completion) ⊗ₜ[L] s := by
      rw [LinearMap.baseChange_tmul]
      exact congrArg (fun t => (1 : x.abv.Completion) ⊗ₜ[L] t)
        ((determinantScalarExtensionEquiv K L E).symm_apply_apply s)
    exact (h.trans (congrArg
      ((V.toNormFamily.determinant.scalarExtension (L := L)).norm x) he)).symm
  change U.lineDegree hU = D.lineDegree hD
  exact hd.symm.trans (D.lineDegree_scalarExtensionLine hD)

end AdelicVectorBundle
end ArakelovGeometry
