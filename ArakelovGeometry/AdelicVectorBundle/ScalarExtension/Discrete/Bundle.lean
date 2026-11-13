/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Discrete.Basic

import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Domination.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Dual.Descent
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual algebraic scalar bundles over a countable discrete base

Finite-coordinate primal and dual descent provide the actual bundle for every
algebraic extension. Canonical coherence retains the existing finite,
common-density and line constructors.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u v w wE

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]

/-- The prescribed actual scalar family defines a bundle for every algebraic
extension of a countable discrete base. -/
abbrev scalarExtensionOfCountableDiscreteBase (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized] :
    AdelicVectorBundle (S.algebraicExtension L) where
  carrier := (L ⊗[K] V)
  toNormFamily := V.toNormFamily.scalarExtension (L := L)
  toIsAdelic := {
    isMeasurable := V.toNormFamily.scalarExtension_isMeasurable_of_countable_discrete
    dual_isMeasurable := by
      exact V.toNormFamily.scalarExtension_dual_isMeasurable_of_countable_discrete
    isDominated := by
      exact (NormFamily.IsDominated.scalarExtension_isStronglyDominated
        V.toNormFamily V.isDominated (S.v_Ωinf_lt_top_of_isRCLike)).isDominated
  }

@[simp]
theorem scalarExtensionOfCountableDiscreteBase_toNormFamily (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized] :
    (V.scalarExtensionOfCountableDiscreteBase (L := L)).toNormFamily =
      V.toNormFamily.scalarExtension (L := L) := rfl

/-- Strong domination is produced from the original bundle. -/
theorem scalarExtensionOfCountableDiscreteBase_isStronglyAdelic (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized] :
    (V.scalarExtensionOfCountableDiscreteBase (L := L)).IsStronglyAdelic :=
  NormFamily.IsDominated.scalarExtension_isStronglyDominated
    V.toNormFamily V.isDominated (S.v_Ωinf_lt_top_of_isRCLike)

/-- The actual scalar family has ultrametric finite-place norms. -/
theorem scalarExtensionOfCountableDiscreteBase_isUltrametric (V : AdelicVectorBundle S)
    [S.IsArchimedeanNormalized] :
    (V.scalarExtensionOfCountableDiscreteBase (L := L)).toNormFamily.IsUltrametric :=
  V.toNormFamily.scalarExtension_isUltrametric

/-- Scalar rank preservation includes the zero bundle. -/
theorem scalarExtensionOfCountableDiscreteBase_rank (V : AdelicVectorBundle S)
    [S.IsArchimedeanNormalized] :
    (V.scalarExtensionOfCountableDiscreteBase (L := L)).rank = V.rank :=
  Module.finrank_baseChange

/-- The algebraic and accepted finite discrete constructors agree. -/
theorem scalarExtensionOfCountableDiscreteBase_eq_of_finiteDimensional
    [FiniteDimensional K L] (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized] :
    V.scalarExtensionOfCountableDiscreteBase (L := L) =
      V.scalarExtensionOfCountableDiscrete (L := L) := by
  rfl

/-- The algebraic discrete and common-density constructions have identical actual norms. -/
theorem scalarExtensionOfCountableDiscreteBase_eq_scalarExtension
    (V : AdelicVectorBundle S) [hS : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized] :
    V.scalarExtensionOfCountableDiscreteBase (L := L) =
      V.scalarExtension (L := L) (hS := hS) := by
  rfl

/-- On lines this is the accepted all-algebraic actual scalar line. -/
theorem scalarExtensionOfCountableDiscreteBase_eq_scalarExtensionLine
    (V : AdelicVectorBundle S) [hV : V.IsLine]
    [hN : S.IsArchimedeanNormalized] :
    V.scalarExtensionOfCountableDiscreteBase (L := L) =
      V.scalarExtensionLine (L := L) (hV := hV) := by
  rfl

instance scalarExtensionOfCountableDiscreteBase_isLine
    (V : AdelicVectorBundle S) [hV : V.IsLine]
    [hN : S.IsArchimedeanNormalized] :
    (V.scalarExtensionOfCountableDiscreteBase (L := L)).IsLine :=
  ⟨Module.finrank_baseChange.trans hV.rank_eq_one⟩

/-- Proper-curve line degree is preserved for arbitrary algebraic extensions. -/
theorem lineDegree_scalarExtensionOfCountableDiscreteBase [S.IsProper]
    (V : AdelicVectorBundle S) [hV : V.IsLine]
    [hN : S.IsArchimedeanNormalized] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.scalarExtensionOfCountableDiscreteBase (L := L)).lineDegree
      (hV := (V.scalarExtensionOfCountableDiscreteBase_isLine)) = V.lineDegree := by
  intro hp
  let := hp
  simpa only [V.scalarExtensionOfCountableDiscreteBase_eq_scalarExtensionLine] using
    V.lineDegree_scalarExtensionLine (L := L)

/-- For finite extensions the actual vector degree is preserved; extended
discreteness and normalization are both derived. -/
theorem degree_scalarExtensionOfCountableDiscreteBase [S.IsProper] [FiniteDimensional K L]
    (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.scalarExtensionOfCountableDiscreteBase (L := L)).degree
      (hS :=
        ⟨(Or.inl (AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
        (S := S) (L := L)))⟩)
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
        V.degree := by
  intro hp
  let := hp
  rw [V.scalarExtensionOfCountableDiscreteBase_eq_of_finiteDimensional]
  exact V.degree_scalarExtensionOfCountableDiscrete

end

end ArakelovGeometry.AdelicVectorBundle
