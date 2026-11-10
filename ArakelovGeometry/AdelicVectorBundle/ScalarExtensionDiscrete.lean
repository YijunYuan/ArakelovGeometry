/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionBundle
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-!
# Scalar extension over a countable discrete parameter space

Finite extending parameter spaces are countable with their actual evaluation
sigma algebra discrete. Finite-stage norm identities then prove measurability
without a target common dense field assumption.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

universe u v w wE

variable {K : Type u} [Field K] {L : Type w} [Field L] [Algebra K L]
  {S : AdelicStructure.{u, v} K}

namespace AdelicStructure.ParameterSpaceExtension

/-- A finite extension has a countable actual parameter space over a countable base. -/
theorem countable_of_finiteDimensional [FiniteDimensional K L] [Countable S.Ω] :
    Countable (S.ParameterSpaceExtension L) := by
  let _ (ω : S.Ω) : Finite (AdelicStructure.ExtensionFiber S L ω) :=
    finite_extensionFiber S L ω
  exact Countable.of_equiv (Σ ω : S.Ω, AdelicStructure.ExtensionFiber S L ω)
    (Equiv.sigmaFiberEquiv (proj (AS := S) (L := L)))

/-- Projection and absolute-value evaluations separate the actual extending places. -/
theorem separatesPoints_of_discrete [DiscreteMeasurableSpace S.Ω] :
    MeasurableSpace.SeparatesPoints (S.ParameterSpaceExtension L) := by
  rw [MeasurableSpace.separatesPoints_iff]
  intro x y h
  have hb : x.base = y.base := by
    have hm := (measurable_proj S L) (measurableSet_singleton x.base)
    exact ((h _ hm).mp rfl).symm
  apply ext S L hb
  ext a
  have hm := (measurable_eval S L a) (measurableSet_singleton (x.abv a))
  exact ((h _ hm).mp rfl).symm

/-- A finite extension's evaluation sigma algebra is discrete over a countable discrete base. -/
theorem discreteMeasurableSpace_of_finiteDimensional [FiniteDimensional K L]
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] :
    DiscreteMeasurableSpace (S.ParameterSpaceExtension L) := by
  let := countable_of_finiteDimensional (S := S) (L := L)
  let := separatesPoints_of_discrete (S := S) (L := L)
  infer_instance

end AdelicStructure.ParameterSpaceExtension

/-- The actual algebraic extension sigma algebra is discrete for a finite extension. -/
theorem AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
    [FiniteDimensional K L] [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] :
    DiscreteMeasurableSpace (S.algebraicExtension L).Ω := by
  change @DiscreteMeasurableSpace (S.ParameterSpaceExtension L)
    (AdelicStructure.Algebraic.projectiveMeasurableSpace S L)
  rw [AdelicStructure.Algebraic.projectiveMeasurableSpace_eq]
  exact ParameterSpaceExtension.discreteMeasurableSpace_of_finiteDimensional
    (S := S) (L := L)

namespace NormFamily

variable {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Algebra.IsAlgebraic K L] (ξ : NormFamily S E)

/-- Every actual finite scalar extension is measurable over a countable discrete base. -/
theorem scalarExtension_isMeasurable_of_finiteDimensional_of_countable_discrete
    [FiniteDimensional K L] [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] :
    (ξ.scalarExtension (L := L)).IsMeasurable := by
  let := AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
    (S := S) (L := L)
  exact (ξ.scalarExtension (L := L)).isMeasurable_of_discrete

/-- The actual dual family is measurable on each finite extension of a countable discrete base. -/
theorem scalarExtension_dual_isMeasurable_of_finiteDimensional_of_countable_discrete
    [FiniteDimensional K L] [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] :
    (ξ.scalarExtension (L := L)).dual.IsMeasurable := by
  let := AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
    (S := S) (L := L)
  exact (ξ.scalarExtension (L := L)).dual.isMeasurable_of_discrete

/-- Countable discreteness of the original base proves ordinary scalar measurability
for every algebraic extension by actual finite-coordinate descent. -/
theorem scalarExtension_isMeasurable_of_countable_discrete
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (ξ.scalarExtension (L := L)).IsMeasurable := by
  intro z
  obtain ⟨F, y, hy⟩ := exists_finiteStage_tensor_lift z
  have hm := ξ.scalarExtension_isMeasurable_of_finiteDimensional_of_countable_discrete
    (L := F)
  have hr : @Measurable (S.algebraicExtension L).Ω (S.algebraicExtension F).Ω
      (S.algebraicExtension L).instMeasurableSpaceΩ
      (S.algebraicExtension F).instMeasurableSpaceΩ
      (fun x => AdelicStructure.ParameterSpaceExtension.restrict S L x F) := by
    change @Measurable _ _ (AdelicStructure.Algebraic.projectiveMeasurableSpace S L)
      (AdelicStructure.Algebraic.projectiveMeasurableSpace S F) _
    rw [AdelicStructure.Algebraic.projectiveMeasurableSpace_eq,
      AdelicStructure.Algebraic.projectiveMeasurableSpace_eq]
    exact AdelicStructure.ParameterSpaceExtension.measurable_restrict S L F.1
  have he : (fun x : (S.algebraicExtension L).Ω =>
      (ξ.scalarExtension (L := L)).norm x
        ((1 : ((S.algebraicExtension L).ϕ x).Completion) ⊗ₜ[L] z)) =
      (fun x : (S.algebraicExtension L).Ω =>
        (ξ.scalarExtension (L := F)).norm
          (AdelicStructure.ParameterSpaceExtension.restrict S L x F)
          ((1 : (x.abv.restriction F).Completion) ⊗ₜ[F] y)) := by
    funext x
    rw [← hy]
    exact ξ.scalarExtension_norm_finiteStage F
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN) x y
  rw [he]
  exact (hm y).comp hr

end NormFamily

namespace AdelicVectorBundle

variable {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [FiniteDimensional K L] [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]

/-- Actual finite scalar extension over a countable discrete base, with both
measurability clauses and domination produced. -/
def scalarExtensionOfCountableDiscrete (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    AdelicVectorBundle (S.algebraicExtension L) (L ⊗[K] E) where
  toNormFamily := V.toNormFamily.scalarExtension (L := L)
  isMeasurable :=
    V.toNormFamily.scalarExtension_isMeasurable_of_finiteDimensional_of_countable_discrete
  dual_isMeasurable :=
    V.toNormFamily.scalarExtension_dual_isMeasurable_of_finiteDimensional_of_countable_discrete
  isDominated := (NormFamily.IsDominated.scalarExtension_isStronglyDominated
    V.toNormFamily V.isDominated (S.v_Ωinf_lt_top_of_isRCLike hN)).isDominated

@[simp]
theorem scalarExtensionOfCountableDiscrete_toNormFamily (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.scalarExtensionOfCountableDiscrete (L := L) hN).toNormFamily =
      V.toNormFamily.scalarExtension (L := L) := rfl

/-- The constructed finite extended bundle is strongly adelic. -/
theorem scalarExtensionOfCountableDiscrete_isStronglyAdelic (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.scalarExtensionOfCountableDiscrete (L := L) hN).IsStronglyAdelic :=
  NormFamily.IsDominated.scalarExtension_isStronglyDominated
    V.toNormFamily V.isDominated (S.v_Ωinf_lt_top_of_isRCLike hN)

/-- The construction preserves rank, including zero. -/
theorem scalarExtensionOfCountableDiscrete_rank (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.scalarExtensionOfCountableDiscrete (L := L) hN).rank = V.rank :=
  Module.finrank_baseChange

/-- On overlapping hypotheses the finite discrete and common-density constructors agree. -/
theorem scalarExtensionOfCountableDiscrete_eq_scalarExtension
    (V : AdelicVectorBundle S E) (hS : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.scalarExtensionOfCountableDiscrete (L := L) hN =
      V.scalarExtension (L := L) hS hN := by
  apply AdelicVectorBundle.ext
  rfl

/-- The actual finite extended bundle preserves degree with extended discreteness
and extended Archimedean normalization both derived. -/
theorem degree_scalarExtensionOfCountableDiscrete [S.IsProper]
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.scalarExtensionOfCountableDiscrete (L := L) hN).degree
      (Or.inl (AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
        (S := S) (L := L)))
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) =
        V.degree (Or.inl inferInstance) hN := by
  intro hp
  let := hp
  let hLS := AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
    (S := S) (L := L)
  let hNL := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
  have he : (V.scalarExtensionOfCountableDiscrete (L := L) hN).determinantOfMeasurableBase
      (Or.inl hLS) hNL =
        V.scalarExtensionDeterminant (L := L) (Or.inl inferInstance) hN := by
    apply AdelicVectorBundle.ext
    rfl
  change (V.scalarExtensionOfCountableDiscrete (L := L) hN).degree (Or.inl hLS) hNL = _
  rw [degree, he]
  exact V.lineDegree_scalarExtensionDeterminant (L := L) (Or.inl inferInstance) hN

end AdelicVectorBundle

end ArakelovGeometry

end
