/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Hermitian.Basic

import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Exact sequences of norm families

The algebraic sequence is short exact and the two end norms are exactly
the actual completed restriction and quotient norms of the middle family.
This is the convention preceding source Proposition 4.3.13.
-/

@[expose] public section

namespace ArakelovGeometry.NormFamily

noncomputable section

universe u v w wF wG

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type wF} [AddCommGroup F] [Module K F]
  {G : Type wG} [AddCommGroup G] [Module K G]

/-- Source short exactness together with the prescribed actual completed
restriction and quotient norm families. -/
structure IsExactSequence (η : NormFamily S F) (ξ : NormFamily S E)
    (ζ : NormFamily S G) (i : F →ₗ[K] E) (p : E →ₗ[K] G) : Prop where
  i_injective : Function.Injective i
  p_surjective : Function.Surjective p
  exact : Function.Exact i p
  left_norm : η = ξ.pullback i i_injective
  right_norm : ζ = ξ.pushforward p p_surjective

/-- Every actual rational restriction and quotient give an exact sequence
of norm families, including the zero and total subspaces. -/
theorem isExactSequence_restrict_quotient (ξ : NormFamily S E) (W : Submodule K E) :
    IsExactSequence (ξ.restrict W) ξ (ξ.quotient W) W.subtype W.mkQ where
  i_injective := W.subtype_injective
  p_surjective := W.mkQ_surjective
  exact := LinearMap.exact_subtype_mkQ W
  left_norm := rfl
  right_norm := rfl

/-- The actual left end of a norm-family exact sequence is Hermitian
when its middle family is Hermitian. -/
theorem IsExactSequence.isHermitian_left
    {η : NormFamily S F} {ξ : NormFamily S E} {ζ : NormFamily S G}
    {i : F →ₗ[K] E} {p : E →ₗ[K] G} (h : IsExactSequence η ξ ζ i p)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] : η.IsHermitian := by
  rw [h.left_norm]
  exact hξ.pullback i h.i_injective

/-- The actual quotient end of a norm-family exact sequence is Hermitian
when its middle family is Hermitian. -/
theorem IsExactSequence.isHermitian_right
    {η : NormFamily S F} {ξ : NormFamily S E} {ζ : NormFamily S G}
    {i : F →ₗ[K] E} {p : E →ₗ[K] G} (h : IsExactSequence η ξ ζ i p)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] : ζ.IsHermitian := by
  rw [h.right_norm]
  exact hξ.pushforward p h.p_surjective

end

end ArakelovGeometry.NormFamily
