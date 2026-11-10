/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDualDescent

/-!
# Actual algebraic scalar bundles over a countable discrete base

Finite-coordinate primal and dual descent provide the actual bundle for every
algebraic extension. Canonical coherence retains the existing finite,
common-density and line constructors.
-/

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
def scalarExtensionOfCountableDiscreteBase (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    AdelicVectorBundle (S.algebraicExtension L) (L ⊗[K] E) where
  toNormFamily := V.toNormFamily.scalarExtension (L := L)
  isMeasurable := V.toNormFamily.scalarExtension_isMeasurable_of_countable_discrete hN
  dual_isMeasurable := V.toNormFamily.scalarExtension_dual_isMeasurable_of_countable_discrete
  isDominated := (NormFamily.IsDominated.scalarExtension_isStronglyDominated
    V.toNormFamily V.isDominated (S.v_Ωinf_lt_top_of_isRCLike hN)).isDominated

@[simp]
theorem scalarExtensionOfCountableDiscreteBase_toNormFamily (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.scalarExtensionOfCountableDiscreteBase (L := L) hN).toNormFamily =
      V.toNormFamily.scalarExtension (L := L) := rfl

/-- Strong domination is produced from the original bundle. -/
theorem scalarExtensionOfCountableDiscreteBase_isStronglyAdelic (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.scalarExtensionOfCountableDiscreteBase (L := L) hN).IsStronglyAdelic :=
  NormFamily.IsDominated.scalarExtension_isStronglyDominated
    V.toNormFamily V.isDominated (S.v_Ωinf_lt_top_of_isRCLike hN)

/-- The actual scalar family has ultrametric finite-place norms. -/
theorem scalarExtensionOfCountableDiscreteBase_isUltrametric (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.scalarExtensionOfCountableDiscreteBase (L := L) hN).toNormFamily.IsUltrametric :=
  V.toNormFamily.scalarExtension_isUltrametric

/-- Scalar rank preservation includes the zero bundle. -/
theorem scalarExtensionOfCountableDiscreteBase_rank (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.scalarExtensionOfCountableDiscreteBase (L := L) hN).rank = V.rank :=
  Module.finrank_baseChange

/-- The algebraic and accepted finite discrete constructors agree. -/
theorem scalarExtensionOfCountableDiscreteBase_eq_of_finiteDimensional
    [FiniteDimensional K L] (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.scalarExtensionOfCountableDiscreteBase (L := L) hN =
      V.scalarExtensionOfCountableDiscrete (L := L) hN := by
  apply AdelicVectorBundle.ext
  rfl

/-- The algebraic discrete and common-density constructions have identical actual norms. -/
theorem scalarExtensionOfCountableDiscreteBase_eq_scalarExtension
    (V : AdelicVectorBundle S E) (hS : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.scalarExtensionOfCountableDiscreteBase (L := L) hN =
      V.scalarExtension (L := L) hS hN := by
  apply AdelicVectorBundle.ext
  rfl

/-- On lines this is the accepted all-algebraic actual scalar line. -/
theorem scalarExtensionOfCountableDiscreteBase_eq_scalarExtensionLine
    (V : AdelicVectorBundle S E) (hV : V.IsLine)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.scalarExtensionOfCountableDiscreteBase (L := L) hN =
      V.scalarExtensionLine (L := L) hV := by
  apply AdelicVectorBundle.ext
  rfl

theorem scalarExtensionOfCountableDiscreteBase_isLine
    (V : AdelicVectorBundle S E) (hV : V.IsLine)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.scalarExtensionOfCountableDiscreteBase (L := L) hN).IsLine :=
  Module.finrank_baseChange.trans hV

/-- Proper-curve line degree is preserved for arbitrary algebraic extensions. -/
theorem lineDegree_scalarExtensionOfCountableDiscreteBase [S.IsProper]
    (V : AdelicVectorBundle S E) (hV : V.IsLine)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.scalarExtensionOfCountableDiscreteBase (L := L) hN).lineDegree
      (V.scalarExtensionOfCountableDiscreteBase_isLine hV hN) = V.lineDegree hV := by
  intro hp
  let := hp
  rw [V.scalarExtensionOfCountableDiscreteBase_eq_scalarExtensionLine hV hN]
  exact V.lineDegree_scalarExtensionLine hV

/-- For finite extensions the actual vector degree is preserved; extended
discreteness and normalization are both derived. -/
theorem degree_scalarExtensionOfCountableDiscreteBase [S.IsProper] [FiniteDimensional K L]
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.scalarExtensionOfCountableDiscreteBase (L := L) hN).degree
      (Or.inl (AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
        (S := S) (L := L)))
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) =
        V.degree (Or.inl inferInstance) hN := by
  intro hp
  let := hp
  rw [V.scalarExtensionOfCountableDiscreteBase_eq_of_finiteDimensional hN]
  exact V.degree_scalarExtensionOfCountableDiscrete hN

end

end ArakelovGeometry.AdelicVectorBundle
