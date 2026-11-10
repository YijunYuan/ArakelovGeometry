/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HermitianScalarExtension
public import ArakelovGeometry.Analysis.HermitianScalarExtensionDual

/-!
# Duality for Hermitian scalar extension of norm families

The canonical completed pairing identifies Hermitian extension of the dual
with the dual of the actual Hermitian extension, at every place.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

universe u v w wE

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E)
  (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hL : ∀ x ∈ (S.algebraicExtension L).Ωinf,
    IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
  (hξ : ξ.IsHermitian hS)

/-- At an infinite extending place, exact extension of the Hermitian
pairing commutes with the actual completed dual norm. -/
theorem hermitianScalarExtension_dual_of_infinite (x : S.ParameterSpaceExtension L)
    (hx : x ∈ (S.algebraicExtension L).Ωinf)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] Module.Dual K E)) :
    (hermitianScalarExtension ξ.dual hS hL hξ.dual).norm x z =
      (hermitianScalarExtension ξ hS hL hξ).dual.norm x
        ((dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion z) := by
  classical
  let := hS x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
  let := IsRCLikeNormedField.rclike (S.ϕ x.base).Completion
  let : IsRCLikeNormedField x.abv.Completion := hL x hx
  let := IsRCLikeNormedField.rclike x.abv.Completion
  let : NormedAlgebra (S.ϕ x.base).Completion x.abv.Completion :=
    AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let := hξ.fibreInnerProductSpace x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
  let := ξ.dual.fibreNormedAddCommGroup x.base
  let := ξ.dual.fibreNormedSpace x.base
  let := hξ.dual.fibreInnerProductSpace x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
  let b := stdOrthonormalBasis (S.ϕ x.base).Completion ((S.ϕ x.base).Completion ⊗[K] E)
  let c := stdOrthonormalBasis (S.ϕ x.base).Completion
    ((S.ϕ x.base).Completion ⊗[K] Module.Dual K E)
  let e := completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq
  have hn (y : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
      (hermitianScalarExtension ξ hS hL hξ).norm x y =
        hermitianScalarExtensionSeminorm b (e y) := by
    rw [hermitianScalarExtension_norm_of_infinite ξ hS hL hξ x hx y]
    rfl
  rw [hermitianScalarExtension_norm_of_infinite ξ.dual hS hL hξ.dual x hx z]
  refine Eq.trans ?_ ((hermitianScalarExtension ξ hS hL hξ).dual_norm_eq_sSup x
    ((dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion z)).symm
  change hermitianScalarExtensionSeminorm c
    (completedScalarExtensionEquiv (Module.Dual K E) (S.ϕ x.base) x.abv x.restrict_eq z) = _
  rw [hermitianScalarExtension_dual_eq_sSup b c
    (dualBaseChangeEquiv K (S.ϕ x.base).Completion E) (fun _ ↦ rfl)]
  congr 1
  ext r
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨y, rfl⟩ := e.surjective t
    refine ⟨y, ?_⟩
    exact congrArg₂ (fun a b : ℝ ↦ a / b)
      (congrArg (fun a : x.abv.Completion ↦ ‖a‖) (completedScalarExtensionEquiv_dual_apply
        (S.ϕ x.base) x.abv x.restrict_eq z y).symm) (hn y)
  · rintro ⟨y, rfl⟩
    refine ⟨e y, ?_⟩
    exact (congrArg₂ (fun a b : ℝ ↦ a / b)
      (congrArg (fun a : x.abv.Completion ↦ ‖a‖) (completedScalarExtensionEquiv_dual_apply
        (S.ϕ x.base) x.abv x.restrict_eq z y).symm) (hn y)).symm

/-- At a finite extending place, Hermitian scalar-extension duality is
the already proved non-Archimedean injective duality on the same fibres. -/
theorem hermitianScalarExtension_dual_of_finite (x : S.ParameterSpaceExtension L)
    (hx : x ∈ (S.algebraicExtension L).Ωfin)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] Module.Dual K E)) :
    (hermitianScalarExtension ξ.dual hS hL hξ.dual).norm x z =
      (hermitianScalarExtension ξ hS hL hξ).dual.norm x
        ((dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion z) := by
  rw [hermitianScalarExtension_norm_of_finite ξ.dual hS hL hξ.dual x hx z]
  refine (ξ.injectiveScalarExtension_dual x hx z).trans ?_
  refine ((ξ.injectiveScalarExtension (L := L)).dual_norm_eq_sSup x _).trans ?_
  refine Eq.trans ?_ ((hermitianScalarExtension ξ hS hL hξ).dual_norm_eq_sSup x _).symm
  congr 1
  apply congrArg Set.range
  funext y
  exact congrArg (fun d : ℝ ↦
    ‖dualBaseChangeEquiv L x.abv.Completion (L ⊗[K] E)
      ((dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion z) y‖ / d)
    (hermitianScalarExtension_norm_of_finite ξ hS hL hξ x hx y).symm

/-- Hermitian scalar extension commutes with duality at every place,
under the canonical completed scalar extension of the algebraic dual map. -/
theorem hermitianScalarExtension_dual (x : S.ParameterSpaceExtension L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] Module.Dual K E)) :
    (hermitianScalarExtension ξ.dual hS hL hξ.dual).norm x z =
      (hermitianScalarExtension ξ hS hL hξ).dual.norm x
        ((dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion z) := by
  by_cases hx : x ∈ (S.algebraicExtension L).Ωfin
  · exact hermitianScalarExtension_dual_of_finite ξ hS hL hξ x hx z
  · exact hermitianScalarExtension_dual_of_infinite ξ hS hL hξ x hx z

end ArakelovGeometry.NormFamily

end
