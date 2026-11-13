/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Determinant.Basic
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Subquotient
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Domination.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.NativeDeterminantMeasurable

import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.NativeSubquotientMeasurable

/-!
# Genuine finite geometric native bundles and their determinant degrees

Produced norm, dual and determinant regularity constructs the existing adelic
bundle and degree objects on literal native relative quotients. The original
family need only be dominated; finite scalar extension supplies strong
domination. All-finite positive atomic hypotheses allow uncountable fields.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.NormFamily

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

variable [MeasurableSingletonClass S.Ω]

/-- The canonical adelic bundle on the actual finite native relative quotient,
with both norm/dual measurability and domination supplied by proved producers. -/
abbrev nativeSubquotientOfPositiveSingletons (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces]
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    AdelicVectorBundle (S.algebraicExtension L) where
  carrier := (B ⧸ U)
  toNormFamily := ((ξ.scalarExtension (L := L)).restrict B).quotient U
  toIsAdelic := {
    isMeasurable := by
      exact IsDominated.scalarExtension_restrict_quotient_isMeasurable_of_pos_singletons
        ξ hξ B U
    dual_isMeasurable := by
      exact IsDominated.scalarExtension_restrict_quotient_dual_isMeasurable_of_pos_singletons
        ξ hξ B U
    isDominated := by
      exact ((hξ.scalarExtension_isStronglyDominated ξ
        (AdelicStructure.v_Ωinf_lt_top_of_forall_mem_Ωfin)).isDominated.restrict B).quotient U
  }

@[simp]
theorem nativeSubquotientOfPositiveSingletons_toNormFamily
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces]
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    (ξ.nativeSubquotientOfPositiveSingletons B U).toNormFamily =
      ((ξ.scalarExtension (L := L)).restrict B).quotient U := rfl

instance nativeSubquotientOfPositiveSingletons_determinant_isMeasurable
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [S.HasPositiveSingletons] [S.HasOnlyFinitePlaces]
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    (ξ.nativeSubquotientOfPositiveSingletons B U).toNormFamily.determinant.IsMeasurable :=
  IsDominated.scalarExtension_restrict_quotient_determinant_isMeasurable_of_pos_singletons
    ξ hξ B U

/-- The produced actual native bundle is strongly adelic even when the
original dominated family is not strongly dominated or measurable. -/
instance nativeSubquotientOfPositiveSingletons_isStronglyAdelic
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces]
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    (ξ.nativeSubquotientOfPositiveSingletons B U).IsStronglyAdelic := by
  exact ((hξ.scalarExtension_isStronglyDominated ξ
    (AdelicStructure.v_Ωinf_lt_top_of_forall_mem_Ωfin)).restrict B).quotient U

/-- The actual determinant line of the produced native bundle is adelic,
using the separately produced determinant measurability. -/
abbrev nativeDeterminantOfPositiveSingletons (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces]
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    AdelicVectorBundle (S.algebraicExtension L) :=
  (ξ.nativeSubquotientOfPositiveSingletons B U).determinant
    (hm :=
      IsDominated.scalarExtension_restrict_quotient_determinant_isMeasurable_of_pos_singletons
      ξ hξ B U)

@[simp]
theorem nativeDeterminantOfPositiveSingletons_toNormFamily
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces]
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    (ξ.nativeDeterminantOfPositiveSingletons B U).toNormFamily =
      (((ξ.scalarExtension (L := L)).restrict B).quotient U).determinant := rfl

/-- The genuine determinant bundle has rank one also when the relative
quotient has rank zero. -/
instance nativeDeterminantOfPositiveSingletons_isLine
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces]
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    (ξ.nativeDeterminantOfPositiveSingletons B U).IsLine :=
  ⟨determinant_finrank (K := L) (E := B ⧸ U)⟩

local instance [S.IsProper] : (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- A nonzero rational generator computes the canonical actual native degree
from its proved integrable determinant logarithm, with no countable density. -/
theorem native_degree_eq_neg_integral [S.IsProper]
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces]
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B)
    (t : {z : ⋀[L]^(Module.finrank L (B ⧸ U)) (B ⧸ U) // z ≠ 0}) :
    (ξ.nativeSubquotientOfPositiveSingletons B U).degreeOfMeasurableDeterminant
      (hdet :=
        IsDominated.scalarExtension_restrict_quotient_determinant_isMeasurable_of_pos_singletons
        ξ hξ B U) =
      -(∫ x, (((ξ.scalarExtension (L := L)).restrict B).quotient U).determinant.logNorm t.val x
        ∂(S.algebraicExtension L).v) :=
  AdelicVectorBundle.degreeOfMeasurableDeterminant_eq_neg_integral
    (ξ.nativeSubquotientOfPositiveSingletons B U) t

/-- A zero native relative quotient has canonical degree zero. Its actual
determinant bundle is still the scalar unit line. -/
theorem native_degree_eq_zero_of_finrank_eq_zero [S.IsProper]
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveSingletons] [hS : S.HasOnlyFinitePlaces]
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B)
    (hr : Module.finrank L (B ⧸ U) = 0) :
    (ξ.nativeSubquotientOfPositiveSingletons B U).degreeOfMeasurableDeterminant
      (hdet :=
        (IsDominated.scalarExtension_restrict_quotient_determinant_isMeasurable_of_pos_singletons
        ξ hξ B U)) = 0 := by
  let t := exteriorPower.ιMulti L (Module.finrank L (B ⧸ U)) (fun _ ↦ (0 : B ⧸ U))
  have ht : t ≠ 0 := AdelicVectorBundle.determinant_empty_ne_zero hr
  rw [native_degree_eq_neg_integral ξ B U ⟨t, ht⟩]
  have he : (((ξ.scalarExtension (L := L)).restrict B).quotient U).determinant.logNorm t = 0 := by
    funext x
    have hn := (((ξ.scalarExtension (L := L)).restrict B).quotient U
      ).determinant_norm_empty_tmul hr x 1 (fun _ ↦ 0)
    change Real.log _ = 0
    rw [hn]
    simp
  simp only [he, Pi.zero_apply, integral_zero, neg_zero]

end ArakelovGeometry.NormFamily
