/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HermitianScalarExtension
public import ArakelovGeometry.Analysis.HermitianScalarExtensionTensor

/-!
# The orthogonal tensor description of Hermitian scalar extension

At each infinite extending place the actual completed-fibre norm is the
Hilbert tensor norm with the given absolute value on the completed field.
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

/-- The actual infinite-place Hermitian scalar-extension norm is the
orthogonal tensor norm of the original completed fibre and the extended
absolute-value field, under the canonical completed-fibre identification. -/
theorem hermitianScalarExtension_norm_eq_tensor_norm (x : S.ParameterSpaceExtension L)
    (hx : x ∈ (S.algebraicExtension L).Ωinf)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    let := hS x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
    let := IsRCLikeNormedField.rclike (S.ϕ x.base).Completion
    let : IsRCLikeNormedField x.abv.Completion := hL x hx
    let := IsRCLikeNormedField.rclike x.abv.Completion
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    let := ξ.fibreNormedAddCommGroup x.base
    let := ξ.fibreNormedSpace x.base
    let := hξ.fibreInnerProductSpace x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
    let := normedAlgebraInnerProductSpace
      (k := (S.ϕ x.base).Completion) (L := x.abv.Completion)
    (hermitianScalarExtension ξ hS hL hξ).norm x z =
      ‖completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq z‖ := by
  intro hV rV hW rW aVW nV nsV iV iW
  let := hV
  let := rV
  let := hW
  let := rW
  let := aVW
  let := nV
  let := nsV
  let := iV
  let := iW
  rw [hermitianScalarExtension_norm_of_infinite ξ hS hL hξ x hx z]
  change hermitianScalarExtensionSeminorm
      (stdOrthonormalBasis (S.ϕ x.base).Completion ((S.ϕ x.base).Completion ⊗[K] E))
      (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq z) = _
  exact hermitianScalarExtensionSeminorm_eq_tensor_norm _ _

end ArakelovGeometry.NormFamily

end
