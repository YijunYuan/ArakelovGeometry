/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.TensorDomination
import ArakelovGeometry.AdelicVectorBundle.StrongSubquotient
import ArakelovGeometry.AdelicVectorBundle.Determinant

/-!
# Domination of exterior powers and determinants

Source Proposition 4.1.19(6) follows from the actual mixed tensor norm and
strong quotient construction. Degree zero and powers above dimension are
included by the same canonical quotient construction.
-/

namespace ArakelovGeometry.NormFamily

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ξ : NormFamily S E}

/-- Every actual exterior-power family of a dominated family is strongly dominated. -/
theorem IsDominated.strong_exteriorPower (hξ : ξ.IsDominated) (n : ℕ)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (ξ.exteriorPower n).IsStronglyDominated :=
  (IsDominated.strong_mixedTensor (fun _ : Fin n ↦ ξ) (fun _ ↦ hξ)
    (S.v_Ωinf_lt_top_of_isRCLike hS)).pushforward
      (tensorToExterior K E n) (tensorToExterior_surjective K E n) hS

/-- Exterior-power domination, for arbitrary nonnegative degree. -/
theorem IsDominated.exteriorPower (hξ : ξ.IsDominated) (n : ℕ)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (ξ.exteriorPower n).IsDominated := (hξ.strong_exteriorPower n hS).isDominated

/-- The actual projective determinant quotient is strongly dominated, also in rank zero. -/
theorem IsDominated.strong_determinant (hξ : ξ.IsDominated)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ξ.determinant.IsStronglyDominated := by
  rw [ξ.determinant_eq_exteriorPower]
  exact hξ.strong_exteriorPower (Module.finrank K E) hS

/-- Domination of the genuine determinant line norm family. -/
theorem IsDominated.determinant (hξ : ξ.IsDominated)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ξ.determinant.IsDominated := (hξ.strong_determinant hS).isDominated

end ArakelovGeometry.NormFamily
