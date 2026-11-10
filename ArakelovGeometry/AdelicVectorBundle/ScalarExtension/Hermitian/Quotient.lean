/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.HermitianComparison.DeterminantDegree
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.QuotientEquiv
public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic
import ArakelovGeometry.AdelicVectorBundle.Degree.Isometry
import ArakelovGeometry.AdelicVectorBundle.Dual.Bidual
import ArakelovGeometry.AdelicVectorBundle.Dual.Map
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Hermitian.Dual
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Hermitian.Restriction
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Quotient
import ArakelovGeometry.AdelicVectorBundle.Slope.Quotient
import Mathlib.CategoryTheory.Category.Init

/-!
# Genuine quotient and Hermitian scalar extension

Dual transport and pullback isometry compare the actual pushforward dual norms.
Ultrametric and Archimedean biduality then identify the genuine quotient norms.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry.NormFamily

variable {K L E F : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- Duality and the genuine transpose pullback isometry identify the actual
completed dual norms of extended pushforwards in every place. -/
theorem hermitianScalarExtension_pushforward_dual_norm_eq (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hLN : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
    (hH : ξ.IsHermitian hN) (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (x : S.ParameterSpaceExtension L)
    (z : x.abv.Completion ⊗[L] Module.Dual L (L ⊗[K] F)) :
    ((ξ.hermitianScalarExtension hN hLN hH).pushforward (π.baseChange L)
      (LinearMap.baseChange_surjective L hπ)).dual.norm x z =
      ((ξ.pushforward π hπ).hermitianScalarExtension hN hLN
        (hH.pushforward π hπ)).dual.norm x z := by
  obtain ⟨d, rfl⟩ := LinearMap.baseChange_surjective x.abv.Completion
    (dualBaseChangeEquiv K L F).surjective z
  erw [(ξ.hermitianScalarExtension hN hLN hH).pushforward_dual_norm_eq,
    dualBaseChangeEquiv_dualMap_baseChange,
    ← ξ.hermitianScalarExtension_dual hN hLN hH,
    ← (ξ.pushforward π hπ).hermitianScalarExtension_dual hN hLN (hH.pushforward π hπ)]
  have he := ξ.dual.hermitianScalarExtension_pullback_norm_eq hN hLN hH.dual
    π.dualMap (LinearMap.dualMap_injective_of_surjective hπ) x d
  change (ξ.dual.hermitianScalarExtension hN hLN hH.dual).norm x
      ((π.dualMap.baseChange L).baseChange x.abv.Completion d) =
    ((ξ.pushforward π hπ).dual.hermitianScalarExtension hN hLN
      (hH.pushforward π hπ).dual).norm x d
  have hc (α β : NormFamily S (Module.Dual K F)) (h : α = β)
      (hα : α.IsHermitian hN) (hβ : β.IsHermitian hN) :
      α.hermitianScalarExtension hN hLN hα =
        β.hermitianScalarExtension hN hLN hβ := by
    subst β
    rfl
  have heq := hc _ _ (ξ.pushforward_dual π hπ)
    (hH.pushforward π hπ).dual
    (hH.dual.pullback π.dualMap (LinearMap.dualMap_injective_of_surjective hπ))
  exact he.trans (congrArg (fun τ => τ.norm x d) heq).symm

/-- Every actual completed pushforward commutes isometrically with Hermitian
extension; normalized biduality recovers both norms from their produced duals. -/
theorem hermitianScalarExtension_pushforward_norm_eq (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hLN : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
    (hH : ξ.IsHermitian hN) (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (x : S.ParameterSpaceExtension L) (z : x.abv.Completion ⊗[L] (L ⊗[K] F)) :
    ((ξ.hermitianScalarExtension hN hLN hH).pushforward (π.baseChange L)
      (LinearMap.baseChange_surjective L hπ)).norm x z =
      ((ξ.pushforward π hπ).hermitianScalarExtension hN hLN
        (hH.pushforward π hπ)).norm x z := by
  let η := (ξ.hermitianScalarExtension hN hLN hH).pushforward (π.baseChange L)
    (LinearMap.baseChange_surjective L hπ)
  let θ := (ξ.pushforward π hπ).hermitianScalarExtension hN hLN (hH.pushforward π hπ)
  have hη : η.IsHermitian hLN :=
    (ξ.hermitianScalarExtension_isHermitian hN hLN hH).pushforward _ _
  have hθ : θ.IsHermitian hLN :=
    (ξ.pushforward π hπ).hermitianScalarExtension_isHermitian hN hLN (hH.pushforward π hπ)
  have heη := congrArg (fun τ => τ.norm x z) (η.dual_dual_pullback_eq hη.1 hLN)
  have heθ := congrArg (fun τ => τ.norm x z) (θ.dual_dual_pullback_eq hθ.1 hLN)
  change η.norm x z = θ.norm x z
  rw [← heη, ← heθ]
  change η.dual.dual.norm x _ = θ.dual.dual.norm x _
  erw [η.dual.dual_norm_eq_sSup, θ.dual.dual_norm_eq_sSup]
  apply congrArg sSup
  apply congrArg Set.range
  funext d
  exact congrArg (fun t : ℝ =>
    ‖dualBaseChangeEquiv L x.abv.Completion (Module.Dual L (L ⊗[K] F))
      ((Module.Dual.eval L (L ⊗[K] F)).baseChange x.abv.Completion z) d‖ / t)
    (ξ.hermitianScalarExtension_pushforward_dual_norm_eq hN hLN hH π hπ x d)

omit [AddCommGroup F] [Module K F] [FiniteDimensional K F] in
/-- The actual quotient tensor equivalence is an isometry from the Hermitian
extension of the genuine quotient to the native quotient of the extension. -/
theorem hermitianScalarExtension_quotient_norm_eq (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hLN : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
    (hH : ξ.IsHermitian hN) (U : Submodule K E) (x : S.ParameterSpaceExtension L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] (E ⧸ U))) :
    ((ξ.hermitianScalarExtension hN hLN hH).quotient (U.baseChange L)).norm x
      ((tensorQuotientBaseChangeEquiv (L := L) U).toLinearMap.baseChange
        x.abv.Completion z) =
      ((ξ.quotient U).hermitianScalarExtension hN hLN (hH.quotient U)).norm x z := by
  let e := tensorQuotientBaseChangeEquiv (L := L) U
  have he : e.toLinearMap.comp (U.mkQ.baseChange L) = (U.baseChange L).mkQ :=
    tensorQuotientBaseChangeEquiv_comp_mkQ U
  let η := ξ.hermitianScalarExtension hN hLN hH
  have hc := η.pushforward_comp_norm (U.mkQ.baseChange L)
    (LinearMap.baseChange_surjective L U.mkQ_surjective)
    e.toLinearMap e.surjective x (e.toLinearMap.baseChange x.abv.Completion z)
  simp only [he] at hc
  have hi := (η.pushforward (U.mkQ.baseChange L)
    (LinearMap.baseChange_surjective L U.mkQ_surjective)).pushforward_norm_of_injective
    e.toLinearMap e.surjective e.injective x z
  calc
    _ = (η.pushforward (U.mkQ.baseChange L)
      (LinearMap.baseChange_surjective L U.mkQ_surjective)).norm x z := hc.symm.trans hi
    _ = _ := ξ.hermitianScalarExtension_pushforward_norm_eq hN hLN hH
      U.mkQ U.mkQ_surjective x z

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local instance hermitianScalarQuotientProper : (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- Finite Hermitian extension preserves actual native quotient degree
via the genuine canonical quotient tensor isometry. -/
theorem degree_quotient_hermitianScalarExtension_of_finiteDimensional
    [FiniteDimensional K L] (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) (U : Submodule K E) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    (W.quotientOfMeasurableBase (U.baseChange L) hLS).degree hLS hLN =
      (V.quotientOfMeasurableBase U (Or.inr hcount)).degree (Or.inr hcount) hN := by
  intro hLN hLS W
  let Q := V.quotientOfMeasurableBase U (Or.inr hcount)
  let Qext := Q.hermitianScalarExtension (L := L) hcount hN hLN (hH.quotient U)
  have he : Qext.degree hLS hLN =
      (W.quotientOfMeasurableBase (U.baseChange L) hLS).degree hLS hLN :=
    Qext.degree_eq_of_completed_isometry _ (tensorQuotientBaseChangeEquiv (L := L) U)
      hLS hLN (fun x z => V.toNormFamily.hermitianScalarExtension_quotient_norm_eq
        hN hLN hH U x z)
  exact he.symm.trans
    (Q.degree_hermitianScalarExtension_of_finiteDimensional hcount hN hLN (hH.quotient U))

/-- Native quotient means are preserved in every rank by genuine degree
isometry and the canonical quotient tensor rank. -/
theorem slope_quotient_hermitianScalarExtension_of_finiteDimensional
    [FiniteDimensional K L] (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) (U : Submodule K E) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    (W.quotientOfMeasurableBase (U.baseChange L) hLS).slope hLS hLN =
      (V.quotientOfMeasurableBase U (Or.inr hcount)).slope (Or.inr hcount) hN := by
  intro hLN hLS W
  have hr : Module.finrank L ((L ⊗[K] E) ⧸ U.baseChange L) =
      Module.finrank K (E ⧸ U) :=
    (tensorQuotientBaseChangeEquiv (L := L) U).finrank_eq.symm.trans Module.finrank_baseChange
  dsimp only [slope]
  rw [V.degree_quotient_hermitianScalarExtension_of_finiteDimensional hcount hN hH U, hr]

end ArakelovGeometry.AdelicVectorBundle
