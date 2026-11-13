/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Measurability.Density.FiniteExtension
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Degree
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Hermitian.Basic

import ArakelovGeometry.AdelicVectorBundle.Measurability.Countable
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Hermitian.Dual
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Hermitian.Measurable
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.HermitianComparison.Degree
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.HermitianComparison.Domination
import Mathlib.CategoryTheory.Category.Init

/-!
# Degree of the actual Hermitian extended determinant line

The proved actual determinant norm identity constructs the Hermitian extended
determinant as an adelic line for every algebraic field extension. Its line
degree equals the original vector degree under the original degree context.
Under original common countable density, primal and dual measurability and
domination construct the actual Hermitian extended vector bundle. For finite
extensions the proved target common density gives equality of vector degrees.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

universe u v w wL

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- Common countable density gives measurability of the actual Hermitian
extended dual through the canonical completed dual transport. -/
theorem IsMeasurable.hermitianScalarExtension_dual_of_common_countable_dense_subfield
    (ξ : NormFamily S E)
    [hS : S.IsArchimedeanNormalized]
    [hL : (S.algebraicExtension L).IsArchimedeanNormalized]
    [hH : ξ.IsHermitian] (hm : ξ.IsMeasurable)
    (hcount : S.HasCommonCountableDenseSubfield) :
    (hermitianScalarExtension (L := L) ξ).dual.IsMeasurable := by
  let d := dualBaseChangeEquiv K L E
  let θ := hermitianScalarExtension (L := L) ξ.dual (hξ := hH.dual)
  have hθ : θ.IsMeasurable :=
    IsMeasurable.hermitianScalarExtension_of_common_countable_dense_subfield
      ξ.dual (hm.dual_of_common_countable_dense_subfield hcount) hcount
  have he : (hermitianScalarExtension ξ).dual =
      θ.pullback d.symm.toLinearMap d.symm.injective := by
    apply NormFamily.ext
    intro x z
    change S.ParameterSpaceExtension L at x
    change x.abv.Completion ⊗[L] Module.Dual L (L ⊗[K] E) at z
    change (hermitianScalarExtension ξ).dual.norm x z =
      θ.norm x (d.symm.toLinearMap.baseChange x.abv.Completion z)
    have hc : d.toLinearMap.baseChange x.abv.Completion
        (d.symm.toLinearMap.baseChange x.abv.Completion z) = z :=
      (LinearEquiv.baseChange L x.abv.Completion _ _ d).apply_symm_apply z
    have h := hermitianScalarExtension_dual ξ x
      (d.symm.toLinearMap.baseChange x.abv.Completion z)
    rw [hc] at h
    exact h.symm
  rw [he]
  exact hθ.pullback d.symm.toLinearMap d.symm.injective

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w wL

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The actual determinant of the Hermitian scalar extension is an adelic
line. Original determinant measurability and domination suffice; whole-vector
extension measurability is not a hypothesis. -/
abbrev hermitianScalarExtensionDeterminant (V : AdelicVectorBundle S)
    [hbase : S.HasMeasurableBase]
    [hS : S.IsArchimedeanNormalized]
    [hL : (S.algebraicExtension L).IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] :
    AdelicVectorBundle (S.algebraicExtension L) :=
  ofLine (NormFamily.hermitianScalarExtension V.toNormFamily).determinant
    NormFamily.determinant_finrank
    (hm := by
      exact NormFamily.IsMeasurable.determinant_hermitianScalarExtension V.toNormFamily
        (V.isMeasurable.determinant_of_discrete_or_countable))
    (hd := by
      exact NormFamily.IsDominated.determinant_hermitianScalarExtension V.toNormFamily
        (V.determinantOfMeasurableBase).isDominated
        (V.isMeasurable.determinant_of_discrete_or_countable))

@[simp]
theorem hermitianScalarExtensionDeterminant_toNormFamily (V : AdelicVectorBundle S)
    [hbase : S.HasMeasurableBase]
    [hS : S.IsArchimedeanNormalized]
    [hL : (S.algebraicExtension L).IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] :
    (V.hermitianScalarExtensionDeterminant (L := L)).toNormFamily =
      (NormFamily.hermitianScalarExtension V.toNormFamily).determinant := rfl

/-- The actual Hermitian extended determinant has rank one in every
original rank, including zero. -/
instance hermitianScalarExtensionDeterminant_isLine (V : AdelicVectorBundle S)
    [hbase : S.HasMeasurableBase]
    [hS : S.IsArchimedeanNormalized]
    [hL : (S.algebraicExtension L).IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] :
    (V.hermitianScalarExtensionDeterminant (L := L)).IsLine :=
  ⟨NormFamily.determinant_finrank⟩

/-- The actual Hermitian and ordinary extended determinant adelic lines
are equal through their proved norm-family identity. -/
theorem hermitianScalarExtensionDeterminant_eq_scalarExtensionDeterminant
    (V : AdelicVectorBundle S)
    [hbase : S.HasMeasurableBase]
    [hS : S.IsArchimedeanNormalized]
    [hL : (S.algebraicExtension L).IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] :
    V.hermitianScalarExtensionDeterminant (L := L) =
      V.scalarExtensionDeterminant (L := L) := by
  apply AdelicVectorBundle.ext
    (hξ := (V.hermitianScalarExtensionDeterminant (L := L)).toIsAdelic)
    (hη := (V.scalarExtensionDeterminant (L := L)).toIsAdelic)
  exact NormFamily.hermitianScalarExtension_determinant_eq_scalarExtension (L := L) V.toNormFamily

/-- The actual Hermitian extended determinant-line degree equals the
original vector-bundle degree for every algebraic extension. -/
theorem lineDegree_hermitianScalarExtensionDeterminant [S.IsProper]
    (V : AdelicVectorBundle S)
    [hbase : S.HasMeasurableBase]
    [hS : S.IsArchimedeanNormalized]
    [hL : (S.algebraicExtension L).IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.hermitianScalarExtensionDeterminant (L := L)).lineDegree
      (hV := (V.hermitianScalarExtensionDeterminant_isLine)) = V.degree := by
  intro hp
  let := hp
  have hdegree :
      (V.hermitianScalarExtensionDeterminant (L := L)).lineDegree
        (hV := (V.hermitianScalarExtensionDeterminant_isLine)) =
      (V.scalarExtensionDeterminant (L := L)).lineDegree
        (hV := (V.scalarExtensionDeterminant_isLine)) := by
    apply lineDegree_eq_of_norm_rational_eq
      (V.hermitianScalarExtensionDeterminant (L := L))
      (V.scalarExtensionDeterminant (L := L)) (LinearEquiv.refl L _)
      (hV := V.hermitianScalarExtensionDeterminant_isLine)
      (hW := V.scalarExtensionDeterminant_isLine)
    intro x s
    change S.ParameterSpaceExtension L at x
    change (NormFamily.hermitianScalarExtension V.toNormFamily).determinant.norm x
        ((1 : x.abv.Completion) ⊗ₜ[L] s) =
      (V.toNormFamily.scalarExtension (L := L)).determinant.norm x
        ((1 : x.abv.Completion) ⊗ₜ[L] s)
    exact NormFamily.hermitianScalarExtension_determinant_norm_eq_scalarExtension
      V.toNormFamily x _
  exact hdegree.trans (V.lineDegree_scalarExtensionDeterminant (L := L))

/-- The actual Hermitian scalar extension is an adelic vector bundle under
original common countable density. Both measurability clauses and domination
are proved for the specified actual Hermitian norm. -/
abbrev hermitianScalarExtension (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hS : S.IsArchimedeanNormalized]
    [hL : (S.algebraicExtension L).IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] :
    AdelicVectorBundle (S.algebraicExtension L) where
  carrier := (L ⊗[K] V)
  toNormFamily := NormFamily.hermitianScalarExtension V.toNormFamily
  toIsAdelic := {
    isMeasurable := by
      exact NormFamily.IsMeasurable.hermitianScalarExtension_of_common_countable_dense_subfield
        V.toNormFamily V.isMeasurable hcount
    dual_isMeasurable :=
      NormFamily.IsMeasurable.hermitianScalarExtension_dual_of_common_countable_dense_subfield
        V.toNormFamily V.isMeasurable hcount
    isDominated := by
      exact NormFamily.IsDominated.hermitianScalarExtension V.toNormFamily V.isDominated
  }

@[simp]
theorem hermitianScalarExtension_toNormFamily (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hS : S.IsArchimedeanNormalized]
    [hL : (S.algebraicExtension L).IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] :
    (V.hermitianScalarExtension (L := L)).toNormFamily =
      NormFamily.hermitianScalarExtension V.toNormFamily := rfl

/-- The produced Hermitian extended bundle is Hermitian for the specified
usual Archimedean norms on the extending completed fields. -/
instance hermitianScalarExtension_isHermitian (V : AdelicVectorBundle S)
    [S.HasCommonCountableDenseSubfield]
    [hS : S.IsArchimedeanNormalized]
    [hL : (S.algebraicExtension L).IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] :
    (V.hermitianScalarExtension (L := L)).IsHermitian :=
  NormFamily.hermitianScalarExtension_isHermitian V.toNormFamily

/-- Strong domination is produced for the actual extended Hermitian bundle. -/
instance hermitianScalarExtension_isStronglyAdelic (V : AdelicVectorBundle S)
    [S.HasCommonCountableDenseSubfield]
    [hS : S.IsArchimedeanNormalized]
    [hL : (S.algebraicExtension L).IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] :
    (V.hermitianScalarExtension (L := L)).IsStronglyAdelic :=
  NormFamily.IsDominated.hermitianScalarExtension_isStronglyDominated
    V.toNormFamily V.isDominated

/-- The actual finite Hermitian scalar-extended vector bundle has the
original vector degree. Target common countable density is proved from the
finite extension, while the determinant-line producer works algebraically. -/
theorem degree_hermitianScalarExtension_of_finiteDimensional [S.IsProper]
    [FiniteDimensional K L] (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hS : S.IsArchimedeanNormalized]
    [hL : (S.algebraicExtension L).IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.hermitianScalarExtension (L := L)).degree
      (hS := ⟨(Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L)))⟩) =
        V.degree := by
  intro hp
  let := hp
  let hLS := hcount.algebraicExtension_of_finiteDimensional (L := L)
  let W := V.hermitianScalarExtension (L := L)
  have hdegree : (W.determinantOfMeasurableBase).lineDegree
        (hV := (W.determinantOfMeasurableBase_isLine)) =
      (V.hermitianScalarExtensionDeterminant (L := L)).lineDegree
        (hV := (V.hermitianScalarExtensionDeterminant_isLine)) := by
    apply lineDegree_eq_of_norm_rational_eq
      W.determinantOfMeasurableBase
      (V.hermitianScalarExtensionDeterminant (L := L)) (LinearEquiv.refl L _)
      (hV := W.determinantOfMeasurableBase_isLine)
      (hW := V.hermitianScalarExtensionDeterminant_isLine)
    intro x s
    rfl
  exact hdegree.trans
    (V.lineDegree_hermitianScalarExtensionDeterminant (L := L))

end ArakelovGeometry.AdelicVectorBundle

end
