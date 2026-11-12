/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.HermitianComparison.DeterminantDegree
public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic

import ArakelovGeometry.AdelicVectorBundle.Degree.Isometry
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Hermitian.Tensor
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Subspace.Basic
import Mathlib.CategoryTheory.Category.Init

/-!
# Genuine restriction and Hermitian scalar extension

The canonical tensor equivalence identifies the extension of an actual
restriction with the restriction to its native base change, isometrically on
every completed vector. Finite extensions therefore preserve restricted degree
and mean slope under the original common countable density hypothesis.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

variable {K L E F : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- Genuine pullback commutes isometrically with Hermitian scalar extension
on every actual completed vector, at finite and infinite places. -/
theorem hermitianScalarExtension_pullback_norm_eq (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized]
    [hLN : (S.algebraicExtension L).IsArchimedeanNormalized]
    [hH : ξ.IsHermitian] (f : F →ₗ[K] E) (hf : Function.Injective f)
    (x : S.ParameterSpaceExtension L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] F)) :
    (ξ.hermitianScalarExtension).norm x
        ((f.baseChange L).baseChange x.abv.Completion z) =
      ((ξ.pullback f hf).hermitianScalarExtension (hξ := (hH.pullback f hf))).norm x z := by
  by_cases hx : x ∈ (S.algebraicExtension L).Ωfin
  · rw [hermitianScalarExtension_norm_of_finite ξ x hx,
      hermitianScalarExtension_norm_of_finite (ξ.pullback f hf)
        (hξ := (hH.pullback f hf)) x hx]
    exact ξ.injectiveScalarExtensionSeminorm_pullback_eq (hξ := hH.1) f hf x
      ((AdelicStructure.mem_Ωfin_algebraicExtension_iff x).mp hx) z
  · have hxinf : x ∈ (S.algebraicExtension L).Ωinf := hx
    have hb : x.base ∈ S.Ωinf := (scalarExtension_mem_Ωinf_iff x).mp hxinf
    let := hN x.base hb
    let := IsRCLikeNormedField.rclike (S.ϕ x.base).Completion
    let : IsRCLikeNormedField x.abv.Completion := hLN x hxinf
    let := IsRCLikeNormedField.rclike x.abv.Completion
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    let := ξ.fibreNormedAddCommGroup x.base
    let := ξ.fibreNormedSpace x.base
    let := ξ.fiberInnerProductSpace x.base hb
    let := (ξ.pullback f hf).fibreNormedAddCommGroup x.base
    let := (ξ.pullback f hf).fibreNormedSpace x.base
    let := (ξ.pullback f hf).fiberInnerProductSpace x.base hb
    let := normedAlgebraInnerProductSpace
      (k := (S.ϕ x.base).Completion) (L := x.abv.Completion)
    let j : ((S.ϕ x.base).Completion ⊗[K] F) →ₗᵢ[(S.ϕ x.base).Completion]
        ((S.ϕ x.base).Completion ⊗[K] E) :=
      { toLinearMap := f.baseChange (S.ϕ x.base).Completion, norm_map' := fun _ => rfl }
    rw [hermitianScalarExtension_norm_eq_tensor_norm ξ x hxinf,
      hermitianScalarExtension_norm_eq_tensor_norm (ξ.pullback f hf)
        (hξ := (hH.pullback f hf)) x hxinf, completedScalarExtensionEquiv_baseChange]
    change ‖j.lTensor x.abv.Completion
        (completedScalarExtensionEquiv F (S.ϕ x.base) x.abv x.restrict_eq z)‖ = _
    exact (j.lTensor x.abv.Completion).norm_map _

omit [AddCommGroup F] [Module K F] [FiniteDimensional K F] in
/-- The canonical native subspace tensor equivalence identifies the genuine
Hermitian extension of a restriction with the restriction of the extension. -/
theorem hermitianScalarExtension_restrict_norm_eq (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized]
    [hLN : (S.algebraicExtension L).IsArchimedeanNormalized]
    [hH : ξ.IsHermitian] (U : Submodule K E) (x : S.ParameterSpaceExtension L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] U)) :
    ((ξ.hermitianScalarExtension).restrict (U.baseChange L)).norm x
        ((Submodule.toBaseChange.toLinearEquiv L U).toLinearMap.baseChange
          x.abv.Completion z) =
      ((ξ.restrict U).hermitianScalarExtension (hξ := (hH.restrict U))).norm x z := by
  change (ξ.hermitianScalarExtension).norm x
      ((U.baseChange L).subtype.baseChange x.abv.Completion
        ((Submodule.toBaseChange.toLinearEquiv L U).toLinearMap.baseChange
          x.abv.Completion z)) = _
  have he : (U.baseChange L).subtype.comp
      (Submodule.toBaseChange.toLinearEquiv L U).toLinearMap =
      U.subtype.baseChange L := rfl
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, he]
  exact ξ.hermitianScalarExtension_pullback_norm_eq
     U.subtype U.subtype_injective x z

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local instance hermitianScalarRestrictionProper : (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- Finite Hermitian extension preserves the actual canonical degree of
each native restriction, through its genuine completed isometry. -/
theorem degree_restrict_hermitianScalarExtension_of_finiteDimensional
    [FiniteDimensional K L] (V : AdelicVectorBundle S E)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (U : Submodule K E) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    (W.restrictOfMeasurableBase (U.baseChange L) (hS := ⟨hLS⟩)).degree (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) =
      (V.restrictOfMeasurableBase U).degree := by
  intro hLN hLS W
  let R := V.restrictOfMeasurableBase U
  let Rext := R.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩) (hV := (hH.restrict U))
  have he : Rext.degree (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) =
      (W.restrictOfMeasurableBase (U.baseChange L) (hS := ⟨hLS⟩)).degree (hS := ⟨hLS⟩)
          (hN := ⟨hLN⟩) :=
    Rext.degree_eq_of_completed_isometry _ (Submodule.toBaseChange.toLinearEquiv L U)
      (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (fun x z =>
          V.toNormFamily.hermitianScalarExtension_restrict_norm_eq
            (hLN := ⟨hLN⟩) U x z)
  exact he.symm.trans
    (R.degree_hermitianScalarExtension_of_finiteDimensional (hL := ⟨hLN⟩) (hV := (hH.restrict U)))

/-- The same genuine native restrictions preserve mean slope in every
rank, including the existing real zero-rank quotient convention. -/
theorem slope_restrict_hermitianScalarExtension_of_finiteDimensional
    [FiniteDimensional K L] (V : AdelicVectorBundle S E)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (U : Submodule K E) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    (W.restrictOfMeasurableBase (U.baseChange L) (hS := ⟨hLS⟩)).slope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) =
      (V.restrictOfMeasurableBase U).slope := by
  intro hLN hLS W
  have hr : Module.finrank L (U.baseChange L) = Module.finrank K U :=
    (Submodule.toBaseChange.toLinearEquiv L U).finrank_eq.symm.trans Module.finrank_baseChange
  dsimp only [slope]
  rw [V.degree_restrict_hermitianScalarExtension_of_finiteDimensional U, hr]

end ArakelovGeometry.AdelicVectorBundle
