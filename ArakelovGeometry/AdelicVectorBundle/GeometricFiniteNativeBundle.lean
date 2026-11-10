/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DegreeDeterminant
public import ArakelovGeometry.AdelicVectorBundle.GeometricNativeDeterminantMeasurable
public import ArakelovGeometry.AdelicVectorBundle.StrongSubquotient

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

/-- An algebraic extension of an all-finite adelic structure has no archimedean places. -/
theorem allFinite_archimedean_normalization
    (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion := by
  intro x hx
  apply False.elim
  apply hx
  change IsNonarchimedean x.abv
  apply (AbsoluteValue.isNonarchimedean_restriction_iff (K := K) x.abv).mp
  rw [x.restrict_eq]
  exact hS x.base

/-- The archimedean locus of an all-finite adelic structure has finite measure. -/
theorem allFinite_infinity_measure_lt_top
    (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) : S.v S.Ωinf < ⊤ := by
  have hinf : S.Ωinf = ∅ := by
    ext ω
    exact ⟨fun h ↦ False.elim (h (hS ω)), fun h ↦ False.elim h⟩
  rw [hinf, measure_empty]
  exact ENNReal.zero_lt_top

variable [MeasurableSingletonClass S.Ω]

/-- The canonical adelic bundle on the actual finite native relative quotient,
with both norm/dual measurability and domination supplied by proved producers. -/
def nativeSubquotientOfPositiveAtoms (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    AdelicVectorBundle (S.algebraicExtension L) (B ⧸ U) where
  toNormFamily := ((ξ.scalarExtension (L := L)).restrict B).quotient U
  isMeasurable :=
    IsDominated.scalarExtension_restrict_quotient_isMeasurable_of_positive_atoms ξ hξ hpos hS B U
  dual_isMeasurable :=
    IsDominated.scalarExtension_restrict_quotient_dual_isMeasurable_of_positive_atoms
      ξ hξ hpos hS B U
  isDominated := ((hξ.scalarExtension_isStronglyDominated ξ
    (allFinite_infinity_measure_lt_top hS)).isDominated.restrict B).quotient U

@[simp]
theorem nativeSubquotientOfPositiveAtoms_toNormFamily
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    (ξ.nativeSubquotientOfPositiveAtoms hξ hpos hS B U).toNormFamily =
      ((ξ.scalarExtension (L := L)).restrict B).quotient U := rfl

/-- The produced actual native bundle is strongly adelic even when the
original dominated family is not strongly dominated or measurable. -/
theorem nativeSubquotientOfPositiveAtoms_isStronglyAdelic
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    (ξ.nativeSubquotientOfPositiveAtoms hξ hpos hS B U).IsStronglyAdelic := by
  have hn := allFinite_archimedean_normalization (L := L) hS
  exact ((hξ.scalarExtension_isStronglyDominated ξ
    (allFinite_infinity_measure_lt_top hS)).restrict B hn).quotient U hn

/-- The actual determinant line of the produced native bundle is adelic,
using the separately produced determinant measurability. -/
def nativeDeterminantOfPositiveAtoms (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    AdelicVectorBundle (S.algebraicExtension L)
      (⋀[L]^(Module.finrank L (B ⧸ U)) (B ⧸ U)) :=
  (ξ.nativeSubquotientOfPositiveAtoms hξ hpos hS B U).determinant
    (IsDominated.scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms
      ξ hξ hpos hS B U) (allFinite_archimedean_normalization hS)

@[simp]
theorem nativeDeterminantOfPositiveAtoms_toNormFamily
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    (ξ.nativeDeterminantOfPositiveAtoms hξ hpos hS B U).toNormFamily =
      (((ξ.scalarExtension (L := L)).restrict B).quotient U).determinant := rfl

/-- The genuine determinant bundle has rank one also when the relative
quotient has rank zero. -/
theorem nativeDeterminantOfPositiveAtoms_isLine
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    (ξ.nativeDeterminantOfPositiveAtoms hξ hpos hS B U).IsLine :=
  determinant_finrank (K := L) (E := B ⧸ U)

local instance [S.IsProper] : (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- A nonzero rational generator computes the canonical actual native degree
from its proved integrable determinant logarithm, with no countable density. -/
theorem native_degree_eq_neg_integral [S.IsProper]
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B)
    (t : {z : ⋀[L]^(Module.finrank L (B ⧸ U)) (B ⧸ U) // z ≠ 0}) :
    (ξ.nativeSubquotientOfPositiveAtoms hξ hpos hS B U).degreeOfMeasurableDeterminant
      (IsDominated.scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms
        ξ hξ hpos hS B U) (allFinite_archimedean_normalization hS) =
      -(∫ x, (((ξ.scalarExtension (L := L)).restrict B).quotient U).determinant.logNorm t.val x
        ∂(S.algebraicExtension L).v) :=
  AdelicVectorBundle.degreeOfMeasurableDeterminant_eq_neg_integral _ _ _ t

/-- A zero native relative quotient has canonical degree zero. Its actual
determinant bundle is still the scalar unit line. -/
theorem native_degree_eq_zero_of_finrank_eq_zero [S.IsProper]
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B)
    (hr : Module.finrank L (B ⧸ U) = 0) :
    (ξ.nativeSubquotientOfPositiveAtoms hξ hpos hS B U).degreeOfMeasurableDeterminant
      (IsDominated.scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms
        ξ hξ hpos hS B U) (allFinite_archimedean_normalization hS) = 0 := by
  let t := exteriorPower.ιMulti L (Module.finrank L (B ⧸ U)) (fun _ ↦ (0 : B ⧸ U))
  have ht : t ≠ 0 := AdelicVectorBundle.determinant_empty_ne_zero hr
  rw [native_degree_eq_neg_integral ξ hξ hpos hS B U ⟨t, ht⟩]
  have he : (((ξ.scalarExtension (L := L)).restrict B).quotient U).determinant.logNorm t = 0 := by
    funext x
    have hn := (((ξ.scalarExtension (L := L)).restrict B).quotient U
      ).determinant_norm_empty_tmul hr x 1 (fun _ ↦ 0)
    change Real.log _ = 0
    rw [hn]
    simp
  simp only [he, Pi.zero_apply, integral_zero, neg_zero]

end ArakelovGeometry.NormFamily
