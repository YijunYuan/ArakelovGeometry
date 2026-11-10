/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Determinant.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.Algebraic.NativeDeterminant
import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Subquotient
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Domination.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.Algebraic.NativeSubquotientMeasurable
import Mathlib.CategoryTheory.Category.Init

/-!
# Genuine algebraic-closure geometric native bundles and their determinant degrees

Produced norm, dual and determinant regularity constructs the existing adelic
bundle and degree objects on literal native relative quotients. The original
family need only be dominated; ordinary scalar extension supplies strong
domination. All-finite positive atomic hypotheses allow uncountable fields.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.NormFamily

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

variable [MeasurableSingletonClass S.Ω]

open IsDominated

/-- The canonical adelic bundle on the actual algebraic-closure native relative quotient,
with both norm/dual measurability and domination supplied by proved producers. -/
def nativeAlgebraicSubquotientOfPositiveAtoms (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    AdelicVectorBundle (S.algebraicExtension L) (B ⧸ U) where
  toNormFamily := ((ξ.scalarExtension (L := L)).restrict B).quotient U
  isMeasurable := by
    exact scalarExtension_restrict_quotient_isMeasurable_of_positive_atoms_of_isAlgClosed
      ξ hξ hpos hS B U
  dual_isMeasurable := by
    exact scalarExtension_restrict_quotient_dual_isMeasurable_of_positive_atoms_of_isAlgClosed
      ξ hξ hpos hS B U
  isDominated := by
    exact ((hξ.scalarExtension_isStronglyDominated ξ
      (AdelicStructure.v_Ωinf_lt_top_of_forall_mem_Ωfin hS)).isDominated.restrict B).quotient U

@[simp]
theorem nativeAlgebraicSubquotientOfPositiveAtoms_toNormFamily
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    (ξ.nativeAlgebraicSubquotientOfPositiveAtoms hξ hpos hS B U).toNormFamily =
      ((ξ.scalarExtension (L := L)).restrict B).quotient U := rfl

/-- The produced actual native bundle is strongly adelic even when the
original dominated family is not strongly dominated or measurable. -/
theorem nativeAlgebraicSubquotientOfPositiveAtoms_isStronglyAdelic
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    (ξ.nativeAlgebraicSubquotientOfPositiveAtoms hξ hpos hS B U).IsStronglyAdelic := by
  have hn := AdelicStructure.isRCLikeNormedField_algebraicExtension_of_forall_mem_Ωfin (L := L) hS
  exact ((hξ.scalarExtension_isStronglyDominated ξ
    (AdelicStructure.v_Ωinf_lt_top_of_forall_mem_Ωfin hS)).restrict B hn).quotient U hn

/-- The actual determinant line of the produced native bundle is adelic,
using the separately produced determinant measurability. -/
def nativeAlgebraicDeterminantOfPositiveAtoms (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    AdelicVectorBundle (S.algebraicExtension L)
      (⋀[L]^(Module.finrank L (B ⧸ U)) (B ⧸ U)) :=
  (ξ.nativeAlgebraicSubquotientOfPositiveAtoms hξ hpos hS B U).determinant
    (scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
      ξ hξ hpos hS B U) (AdelicStructure.isRCLikeNormedField_algebraicExtension_of_forall_mem_Ωfin
        hS)

@[simp]
theorem nativeAlgebraicDeterminantOfPositiveAtoms_toNormFamily
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    (ξ.nativeAlgebraicDeterminantOfPositiveAtoms hξ hpos hS B U).toNormFamily =
      (((ξ.scalarExtension (L := L)).restrict B).quotient U).determinant := rfl

/-- The genuine determinant bundle has rank one also when the relative
quotient has rank zero. -/
theorem nativeAlgebraicDeterminantOfPositiveAtoms_isLine
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    (ξ.nativeAlgebraicDeterminantOfPositiveAtoms hξ hpos hS B U).IsLine :=
  determinant_finrank (K := L) (E := B ⧸ U)

local instance nativeAlgebraic_isProper_algebraicExtension [S.IsProper] :
    (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- A nonzero rational generator computes the canonical actual native degree
from its proved integrable determinant logarithm, with no countable density. -/
theorem native_algebraic_degree_eq_neg_integral [S.IsProper]
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B)
    (t : {z : ⋀[L]^(Module.finrank L (B ⧸ U)) (B ⧸ U) // z ≠ 0}) :
    (ξ.nativeAlgebraicSubquotientOfPositiveAtoms hξ hpos hS B U).degreeOfMeasurableDeterminant
      (scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
        ξ hξ hpos hS B U) (AdelicStructure.isRCLikeNormedField_algebraicExtension_of_forall_mem_Ωfin
          hS) =
      -(∫ x, (((ξ.scalarExtension (L := L)).restrict B).quotient U).determinant.logNorm t.val x
        ∂(S.algebraicExtension L).v) :=
  AdelicVectorBundle.degreeOfMeasurableDeterminant_eq_neg_integral _ _ _ t

/-- A zero native relative quotient has canonical degree zero. Its actual
determinant bundle is still the scalar unit line. -/
theorem native_algebraic_degree_eq_zero_of_finrank_eq_zero [S.IsProper]
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B)
    (hr : Module.finrank L (B ⧸ U) = 0) :
    (ξ.nativeAlgebraicSubquotientOfPositiveAtoms hξ hpos hS B U).degreeOfMeasurableDeterminant
      (scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
        ξ hξ hpos hS B U) (AdelicStructure.isRCLikeNormedField_algebraicExtension_of_forall_mem_Ωfin
          hS) = 0 := by
  let t := exteriorPower.ιMulti L (Module.finrank L (B ⧸ U)) (fun _ ↦ (0 : B ⧸ U))
  have ht : t ≠ 0 := AdelicVectorBundle.determinant_empty_ne_zero hr
  rw [native_algebraic_degree_eq_neg_integral ξ hξ hpos hS B U ⟨t, ht⟩]
  have he : (((ξ.scalarExtension (L := L)).restrict B).quotient U).determinant.logNorm t = 0 := by
    funext x
    have hn := (((ξ.scalarExtension (L := L)).restrict B).quotient U
      ).determinant_norm_empty_tmul hr x 1 (fun _ ↦ 0)
    change Real.log _ = 0
    rw [hn]
    simp
  simp only [he, Pi.zero_apply, integral_zero, neg_zero]

end ArakelovGeometry.NormFamily
