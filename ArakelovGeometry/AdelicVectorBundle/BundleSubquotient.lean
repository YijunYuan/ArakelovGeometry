/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Basic
public import ArakelovGeometry.AdelicVectorBundle.StrongSubquotient

/-!
# Strong and Hermitian adelic subquotients

These are the strong clauses of Proposition 4.1.32(1)–(2), with precisely the
source's additional measurability assumptions. They act on the existing
adelic-bundle constructors and the actual completed restriction and quotient
norms. Hermitian preservation uses the same completed scalar action.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- A rational subspace of a strongly adelic bundle is strongly adelic
under the source's additional dual measurability hypothesis. -/
theorem IsStronglyAdelic.pullback {V : AdelicVectorBundle S E} (hV : V.IsStronglyAdelic)
    (f : F →ₗ[K] E) (hf : Function.Injective f)
    (hm : (V.toNormFamily.pullback f hf).dual.IsMeasurable)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.pullback f hf hm).IsStronglyAdelic :=
  NormFamily.IsStronglyDominated.pullback hV f hf hS

/-- The source strong subbundle assertion, including the zero subspace. -/
theorem IsStronglyAdelic.restrict {V : AdelicVectorBundle S E} (hV : V.IsStronglyAdelic)
    (F : Submodule K E) (hm : (V.toNormFamily.restrict F).dual.IsMeasurable)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.restrict F hm).IsStronglyAdelic :=
  hV.pullback F.subtype F.subtype_injective hm hS

/-- A quotient of a strongly adelic bundle is strongly adelic under the
source's additional quotient measurability hypothesis. -/
theorem IsStronglyAdelic.pushforward {V : AdelicVectorBundle S E} (hV : V.IsStronglyAdelic)
    (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (hm : (V.toNormFamily.pushforward π hπ).IsMeasurable)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.pushforward π hπ hm).IsStronglyAdelic :=
  NormFamily.IsStronglyDominated.pushforward hV π hπ hS

/-- Quotient by a specified rational subspace, using the existing canonical
surjective bundle constructor and its actual quotient norm. -/
noncomputable def quotient (V : AdelicVectorBundle S E) (F : Submodule K E)
    (hm : (V.toNormFamily.quotient F).IsMeasurable) : AdelicVectorBundle S (E ⧸ F) :=
  V.pushforward F.mkQ F.mkQ_surjective hm

@[simp]
theorem quotient_toNormFamily (V : AdelicVectorBundle S E) (F : Submodule K E)
    (hm : (V.toNormFamily.quotient F).IsMeasurable) :
    (V.quotient F hm).toNormFamily = V.toNormFamily.quotient F := rfl

/-- The source strong quotient assertion, including quotient by the full space. -/
theorem IsStronglyAdelic.quotient {V : AdelicVectorBundle S E} (hV : V.IsStronglyAdelic)
    (F : Submodule K E) (hm : (V.toNormFamily.quotient F).IsMeasurable)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.quotient F hm).IsStronglyAdelic :=
  hV.pushforward F.mkQ F.mkQ_surjective hm hS

/-- The same canonical subbundle preserves Hermitianity on the completed fibres. -/
theorem IsHermitian.pullback {V : AdelicVectorBundle S E}
    {hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion} (hV : V.IsHermitian hS)
    (f : F →ₗ[K] E) (hf : Function.Injective f)
    (hm : (V.toNormFamily.pullback f hf).dual.IsMeasurable) :
    (V.pullback f hf hm).IsHermitian hS :=
  NormFamily.IsHermitian.pullback hV f hf

theorem IsHermitian.restrict {V : AdelicVectorBundle S E}
    {hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion} (hV : V.IsHermitian hS)
    (F : Submodule K E) (hm : (V.toNormFamily.restrict F).dual.IsMeasurable) :
    (V.restrict F hm).IsHermitian hS :=
  hV.pullback F.subtype F.subtype_injective hm

/-- The actual quotient adelic bundle preserves the completed Hermitian norm. -/
theorem IsHermitian.pushforward {V : AdelicVectorBundle S E}
    {hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion} (hV : V.IsHermitian hS)
    (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (hm : (V.toNormFamily.pushforward π hπ).IsMeasurable) :
    (V.pushforward π hπ hm).IsHermitian hS :=
  NormFamily.IsHermitian.pushforward hV π hπ

theorem IsHermitian.quotient {V : AdelicVectorBundle S E}
    {hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion} (hV : V.IsHermitian hS)
    (F : Submodule K E) (hm : (V.toNormFamily.quotient F).IsMeasurable) :
    (V.quotient F hm).IsHermitian hS :=
  hV.pushforward F.mkQ F.mkQ_surjective hm

end ArakelovGeometry.AdelicVectorBundle
