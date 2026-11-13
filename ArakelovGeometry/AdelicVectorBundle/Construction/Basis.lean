/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Basic
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Hermitian.Basis

import ArakelovGeometry.AdelicVectorBundle.NormFamily.BasisComparison
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Adelic bundles from completed basis norms

The mixed and Hermitian basis constructions supply both source measurability
clauses and domination for actual adelic vector bundles. Their underlying
norm families are definitionally the previously constructed completed norms.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

universe u w

variable {K : Type u} [Field K] (S : AdelicStructure K)
  (E : Type w) [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ι : Type*} [Fintype ι] (b : Module.Basis ι K E)

/-- The source mixed completed-basis norm defines an adelic vector bundle
whenever the Archimedean locus has finite measure. -/
abbrev ofBasisMixed (hfin : S.v S.Ωinf < ⊤) : AdelicVectorBundle S where
  carrier := E
  toNormFamily := NormFamily.ofBasisMixed S E b
  toIsAdelic := {
    isMeasurable := NormFamily.ofBasisMixed_isMeasurable b
    dual_isMeasurable := NormFamily.ofBasisMixed_dual_isMeasurable b
    isDominated := NormFamily.ofBasisMixed_isDominated_of_measure_lt_top b hfin
  }

/-- The bundle retains the exact previously constructed completed norm family. -/
@[simp]
theorem ofBasisMixed_toNormFamily (hfin : S.v S.Ωinf < ⊤) :
    (ofBasisMixed S E b hfin).toNormFamily = NormFamily.ofBasisMixed S E b := rfl

/-- The mixed basis bundle satisfies the actual bidual strong-domination criterion. -/
theorem ofBasisMixed_isStronglyAdelic (hfin : S.v S.Ωinf < ⊤) :
    (ofBasisMixed S E b hfin).IsStronglyAdelic :=
  NormFamily.ofBasisMixed_isStronglyDominated_of_measure_lt_top b hfin

/-- The Euclidean-infinite, maximum-finite construction defines an actual
adelic vector bundle. Dual measurability uses its exact dual-basis identity. -/
abbrev ofBasisHermitian
    [hS : S.IsArchimedeanNormalized] : AdelicVectorBundle S where
  carrier := E
  toNormFamily := NormFamily.ofBasisHermitian S E b
  toIsAdelic := {
    isMeasurable := NormFamily.ofBasisHermitian_isMeasurable b
    dual_isMeasurable := NormFamily.ofBasisHermitian_dual_isMeasurable b
    isDominated := NormFamily.ofBasisHermitian_isDominated b
  }

/-- The Hermitian bundle retains the actual completed Euclidean coordinate norms. -/
@[simp]
theorem ofBasisHermitian_toNormFamily
    [hS : S.IsArchimedeanNormalized] :
    (ofBasisHermitian S E b).toNormFamily = NormFamily.ofBasisHermitian S E b := rfl

/-- The constructed adelic bundle is Hermitian on its original completed scalar action. -/
theorem ofBasisHermitian_isHermitian
    [hS : S.IsArchimedeanNormalized] :
    (ofBasisHermitian S E b).IsHermitian :=
  NormFamily.ofBasisHermitian_isHermitian b

/-- The Hermitian basis bundle is strongly adelic. -/
theorem ofBasisHermitian_isStronglyAdelic
    [hS : S.IsArchimedeanNormalized] :
    (ofBasisHermitian S E b).IsStronglyAdelic :=
  (ofBasisHermitian_isHermitian S E b).isStronglyAdelic

/-- Every finite-dimensional rational space admits an adelic vector bundle
under finite Archimedean measure, including the zero-dimensional space. -/
theorem nonempty_of_measure_lt_top (hfin : S.v S.Ωinf < ⊤) :
    ∃ ξ : NormFamily S E, ξ.IsAdelic :=
  ⟨(ofBasisMixed S E (Module.finBasis K E) hfin).toNormFamily,
    (ofBasisMixed S E (Module.finBasis K E) hfin).toIsAdelic⟩

/-- Dominated Hermitian existence produces a genuine adelic bundle, with
both measurability fields proved, in every finite dimension. -/
theorem exists_hermitian
    [hS : S.IsArchimedeanNormalized] :
    ∃ ξ : NormFamily S E, ξ.IsAdelic ∧ ξ.IsHermitian :=
  ⟨(ofBasisHermitian S E (Module.finBasis K E)).toNormFamily,
    (ofBasisHermitian S E (Module.finBasis K E)).toIsAdelic,
    ofBasisHermitian_isHermitian S E (Module.finBasis K E)⟩

end ArakelovGeometry.AdelicVectorBundle
