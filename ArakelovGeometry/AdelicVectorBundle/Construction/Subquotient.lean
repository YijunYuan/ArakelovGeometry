/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Basic

import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Subquotient
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

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
    (_hm : (V.toNormFamily.pullback f hf).dual.IsMeasurable)
    [hS : S.IsArchimedeanNormalized] :
    (V.pullback f hf).IsStronglyAdelic :=
  NormFamily.IsStronglyDominated.pullback hV f hf

/-- The source strong subbundle assertion, including the zero subspace. -/
theorem IsStronglyAdelic.restrict {V : AdelicVectorBundle S E} (hV : V.IsStronglyAdelic)
    (F : Submodule K E) (hm : (V.toNormFamily.restrict F).dual.IsMeasurable)
    [hS : S.IsArchimedeanNormalized] :
    (V.restrict F).IsStronglyAdelic :=
  hV.pullback F.subtype F.subtype_injective hm

/-- A quotient of a strongly adelic bundle is strongly adelic under the
source's additional quotient measurability hypothesis. -/
theorem IsStronglyAdelic.pushforward {V : AdelicVectorBundle S E} (hV : V.IsStronglyAdelic)
    (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (_hm : (V.toNormFamily.pushforward π hπ).IsMeasurable)
    [hS : S.IsArchimedeanNormalized] :
    (V.pushforward π hπ).IsStronglyAdelic :=
  NormFamily.IsStronglyDominated.pushforward hV π hπ

/-- Quotient by a specified rational subspace, with its canonical quotient norm. -/
noncomputable def quotient (V : AdelicVectorBundle S E) (F : Submodule K E)
    [hm : (V.toNormFamily.quotient F).IsMeasurable] : AdelicVectorBundle S (E ⧸ F) := by
  letI := V.toIsAdelic.quotient F hm
  exact (V.toNormFamily.quotient F).toAdelicVectorBundle

@[simp]
theorem quotient_toNormFamily (V : AdelicVectorBundle S E) (F : Submodule K E)
    [hm : (V.toNormFamily.quotient F).IsMeasurable] :
    (V.quotient F).toNormFamily = V.toNormFamily.quotient F := rfl

/-- The source strong quotient assertion, including quotient by the full space. -/
theorem IsStronglyAdelic.quotient {V : AdelicVectorBundle S E} (hV : V.IsStronglyAdelic)
    (F : Submodule K E) (hm : (V.toNormFamily.quotient F).IsMeasurable)
    [hS : S.IsArchimedeanNormalized] :
    (V.quotient F).IsStronglyAdelic :=
  hV.pushforward F.mkQ F.mkQ_surjective hm

/-- The same canonical subbundle preserves Hermitianity on the completed fibres. -/
theorem IsHermitian.pullback {V : AdelicVectorBundle S E}
    [hS : S.IsArchimedeanNormalized] (hV : V.IsHermitian)
    (f : F →ₗ[K] E) (hf : Function.Injective f)
    (_hm : (V.toNormFamily.pullback f hf).dual.IsMeasurable) :
    (V.pullback f hf).IsHermitian :=
  NormFamily.IsHermitian.pullback hV f hf

theorem IsHermitian.restrict {V : AdelicVectorBundle S E}
    [hS : S.IsArchimedeanNormalized] (hV : V.IsHermitian)
    (F : Submodule K E) (hm : (V.toNormFamily.restrict F).dual.IsMeasurable) :
    (V.restrict F).IsHermitian :=
  hV.pullback F.subtype F.subtype_injective hm

/-- The actual quotient adelic bundle preserves the completed Hermitian norm. -/
theorem IsHermitian.pushforward {V : AdelicVectorBundle S E}
    [hS : S.IsArchimedeanNormalized] (hV : V.IsHermitian)
    (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (_hm : (V.toNormFamily.pushforward π hπ).IsMeasurable) :
    (V.pushforward π hπ).IsHermitian :=
  NormFamily.IsHermitian.pushforward hV π hπ

theorem IsHermitian.quotient {V : AdelicVectorBundle S E}
    [hS : S.IsArchimedeanNormalized] (hV : V.IsHermitian)
    (F : Submodule K E) (hm : (V.toNormFamily.quotient F).IsMeasurable) :
    (V.quotient F).IsHermitian :=
  hV.pushforward F.mkQ F.mkQ_surjective hm

end ArakelovGeometry.AdelicVectorBundle
