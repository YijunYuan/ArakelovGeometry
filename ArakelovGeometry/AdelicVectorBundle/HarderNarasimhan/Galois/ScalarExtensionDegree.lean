/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Algebraic.ClosureApproximation
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.HermitianComparison.DeterminantDegree
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Isomorphism.Subspace
public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic

import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Galois.ScalarExtensionNorm
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual Hermitian restricted degree under coefficient automorphisms

Original common countable density produces the degree context on finite and
algebraically closed algebraic extensions. The genuine restricted determinant
integral identity then gives degree and mean-slope transport in every rank.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local instance hermitianGaloisScalarDegreeProper : (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

private theorem hermitianDegree_exists_nonzero_determinant
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V] :
    ∃ z : ⋀[F]^(Module.finrank F V) V, z ≠ 0 := by
  let : Nontrivial (⋀[F]^(Module.finrank F V) V) :=
    Module.nontrivial_of_finrank_pos (R := F) (by
      rw [NormFamily.determinant_finrank]
      exact Nat.zero_lt_one)
  exact exists_ne 0

/-- Original common density and finite extension produce the actual target
degree context, and coefficient transport preserves every genuine restriction degree. -/
theorem degree_hermitianScalarExtension_restrict_algEquiv_of_finiteDimensional
    [FiniteDimensional K L] (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (σ : L ≃ₐ[K] L)
    (B : Submodule L (L ⊗[K] V)) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    (W.restrictOfMeasurableBase (scalarExtensionSubspaceOrderIso σ B) (hS := ⟨hLS⟩)).degree
        (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) =
      (W.restrictOfMeasurableBase B (hS := ⟨hLS⟩)).degree (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) := by
  intro hLN hLS W
  let := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  obtain ⟨z, hz⟩ := hermitianDegree_exists_nonzero_determinant (F := L) (V := B)
  let d := determinantSemilinearEquiv σ.toRingEquiv
    (scalarExtensionSubspaceSemilinearEquiv σ B)
    (scalarExtensionSubspaceOrderIso_finrank σ B).symm
  have hdz : d z ≠ 0 := fun h => hz ((d.map_eq_zero_iff).mp h)
  rw [degree_eq_neg_integral _ (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) ⟨d z, hdz⟩,
    degree_eq_neg_integral _ (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) ⟨z, hz⟩]
  exact congrArg Neg.neg
    (V.toNormFamily.hermitianScalarExtension_restrict_determinant_integral_logNorm_algEquiv
  σ B z)

/-- Original common density produces density on the actual closed algebraic
curve; every genuine Hermitian restriction has coefficient-invariant degree. -/
theorem degree_hermitianScalarExtension_restrict_algEquiv_of_isAlgClosed
    [IsAlgClosed L] (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (σ : L ≃ₐ[K] L)
    (B : Submodule L (L ⊗[K] V)) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    (W.restrictOfMeasurableBase (scalarExtensionSubspaceOrderIso σ B) (hS := ⟨hLS⟩)).degree
        (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) =
      (W.restrictOfMeasurableBase B (hS := ⟨hLS⟩)).degree (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) := by
  intro hLN hLS W
  let := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  obtain ⟨z, hz⟩ := hermitianDegree_exists_nonzero_determinant (F := L) (V := B)
  let d := determinantSemilinearEquiv σ.toRingEquiv
    (scalarExtensionSubspaceSemilinearEquiv σ B)
    (scalarExtensionSubspaceOrderIso_finrank σ B).symm
  have hdz : d z ≠ 0 := fun h => hz ((d.map_eq_zero_iff).mp h)
  rw [degree_eq_neg_integral _ (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) ⟨d z, hdz⟩,
    degree_eq_neg_integral _ (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) ⟨z, hz⟩]
  exact congrArg Neg.neg
    (V.toNormFamily.hermitianScalarExtension_restrict_determinant_integral_logNorm_algEquiv
  σ B z)

/-- The genuine finite-extension restriction mean slopes agree; zero rank
uses the existing total real quotient convention. -/
theorem slope_hermitianScalarExtension_restrict_algEquiv_of_finiteDimensional
    [FiniteDimensional K L] (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (σ : L ≃ₐ[K] L)
    (B : Submodule L (L ⊗[K] V)) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    (W.restrictOfMeasurableBase (scalarExtensionSubspaceOrderIso σ B) (hS := ⟨hLS⟩)).slope
        (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) =
      (W.restrictOfMeasurableBase B (hS := ⟨hLS⟩)).slope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) := by
  intro hLN hLS W
  dsimp only [slope]
  rw [V.degree_hermitianScalarExtension_restrict_algEquiv_of_finiteDimensional
     σ B, scalarExtensionSubspaceOrderIso_finrank σ B]

/-- The actual closed-extension restriction mean slopes agree for every
coefficient automorphism, including the empty restriction. -/
theorem slope_hermitianScalarExtension_restrict_algEquiv_of_isAlgClosed
    [IsAlgClosed L] (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (σ : L ≃ₐ[K] L)
    (B : Submodule L (L ⊗[K] V)) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    (W.restrictOfMeasurableBase (scalarExtensionSubspaceOrderIso σ B) (hS := ⟨hLS⟩)).slope
        (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) =
      (W.restrictOfMeasurableBase B (hS := ⟨hLS⟩)).slope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) := by
  intro hLN hLS W
  dsimp only [slope]
  rw [V.degree_hermitianScalarExtension_restrict_algEquiv_of_isAlgClosed
     σ B, scalarExtensionSubspaceOrderIso_finrank σ B]

end ArakelovGeometry.AdelicVectorBundle
