/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Destabilizing
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Algebraic.ClosureApproximation
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.HermitianComparison.DeterminantDegree
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Isomorphism.Subspace

import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Descent.Subspace
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Galois.ScalarExtensionDegree
import Mathlib.CategoryTheory.Category.Init

/-!
# Coefficient invariance of the actual Hermitian destabilizing subspace

Actual restricted slope transport and the produced largest-maximizer property
fix the largest destabilizing subspace over finite or closed algebraic extensions.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local instance hermitianGaloisDestabilizingProper : (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- The genuine finite-extension largest destabilizer is fixed by every
coefficient automorphism; regularity and Hermitianity are produced. -/
theorem destabilizingSubspace_hermitianScalarExtension_algEquiv_of_finiteDimensional
    [FiniteDimensional K L] (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (hr : 0 < Module.finrank K V)
    (σ : L ≃ₐ[K] L) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    let hLH := V.hermitianScalarExtension_isHermitian (hL := ⟨hLN⟩)
    let hrL : 0 < Module.finrank L (L ⊗[K] V) :=
      (Module.finrank_baseChange (R := L) (S := K) (M' := V)).symm ▸ hr
    scalarExtensionSubspaceOrderIso σ (W.destabilizingSubspace (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
        (hV := hLH) hrL) =
      W.destabilizingSubspace (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) hrL := by
  intro hLN hLS W hLH hrL
  let D := W.destabilizingSubspace (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) hrL
  have hp := W.destabilizingSubspace_finrank_pos (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) hrL
  apply Submodule.eq_of_le_of_finrank_eq
  · apply W.le_destabilizingSubspace_of_slope_eq_maximalSlope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
      (hV := hLH) hrL
    · rw [scalarExtensionSubspaceOrderIso_finrank]
      exact hp
    · rw [V.slope_hermitianScalarExtension_restrict_algEquiv_of_finiteDimensional
         σ D]
      exact W.slope_destabilizingSubspace_eq_maximalSlope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
          (hV := hLH) hrL
  · exact scalarExtensionSubspaceOrderIso_finrank σ D

/-- The genuine closed-extension largest destabilizer is fixed by every
coefficient automorphism, without assuming perfectness or stability. -/
theorem destabilizingSubspace_hermitianScalarExtension_algEquiv_of_isAlgClosed
    [IsAlgClosed L] (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (hr : 0 < Module.finrank K V)
    (σ : L ≃ₐ[K] L) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    let hLH := V.hermitianScalarExtension_isHermitian (hL := ⟨hLN⟩)
    let hrL : 0 < Module.finrank L (L ⊗[K] V) :=
      (Module.finrank_baseChange (R := L) (S := K) (M' := V)).symm ▸ hr
    scalarExtensionSubspaceOrderIso σ (W.destabilizingSubspace (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
        (hV := hLH) hrL) =
      W.destabilizingSubspace (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) hrL := by
  intro hLN hLS W hLH hrL
  let D := W.destabilizingSubspace (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) hrL
  have hp := W.destabilizingSubspace_finrank_pos (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) hrL
  apply Submodule.eq_of_le_of_finrank_eq
  · apply W.le_destabilizingSubspace_of_slope_eq_maximalSlope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
      (hV := hLH) hrL
    · rw [scalarExtensionSubspaceOrderIso_finrank]
      exact hp
    · rw [V.slope_hermitianScalarExtension_restrict_algEquiv_of_isAlgClosed
         σ D]
      exact W.slope_destabilizingSubspace_eq_maximalSlope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
          (hV := hLH) hrL
  · exact scalarExtensionSubspaceOrderIso_finrank σ D

/-- The actual first destabilizer over a finite Galois extension descends
uniquely, with coefficient stability proved rather than assumed. -/
theorem existsUnique_baseChange_destabilizingSubspace_hermitianScalarExtension
    [FiniteDimensional K L] [IsGalois K L] (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (hr : 0 < Module.finrank K V) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    let hLH := V.hermitianScalarExtension_isHermitian (hL := ⟨hLN⟩)
    let hrL : 0 < Module.finrank L (L ⊗[K] V) :=
      (Module.finrank_baseChange (R := L) (S := K) (M' := V)).symm ▸ hr
    ∃! U : Submodule K V, U.baseChange L = W.destabilizingSubspace (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
        (hV := hLH) hrL := by
  intro hLN hLS W hLH hrL
  let D := W.destabilizingSubspace (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) hrL
  apply HermitianAbsoluteDescent.existsUnique_baseChange_eq_of_stable
  intro σ x hx
  have hfixed := V.destabilizingSubspace_hermitianScalarExtension_algEquiv_of_finiteDimensional
     hr σ
  change scalarExtensionSubspaceOrderIso σ D = D at hfixed
  change scalarExtensionSemilinearEquiv σ x ∈ D
  rw [← hfixed]
  exact ⟨x, hx, rfl⟩

end ArakelovGeometry.AdelicVectorBundle
