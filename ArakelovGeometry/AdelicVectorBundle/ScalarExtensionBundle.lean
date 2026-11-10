/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDegree
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionFiniteStage

/-!
# Actual ordinary scalar-extended adelic bundles

The actual mixed dual is measurable by pasting the canonical injective dual
transport at finite places with the countable projective-dual formula at
infinite places. Both measurability clauses and strong domination therefore
construct the ordinary extended bundle under original common countable density
and usual Archimedean normalization. No target common dense field is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

universe u v w wL

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

namespace NormFamily

/-- At a finite place the actual mixed dual is the canonical pullback of
the injective extension of the original dual, on every completed vector. -/
theorem scalarExtension_dual_norm_of_mem_Ωfin (ξ : NormFamily S E)
    (x : S.ParameterSpaceExtension L) (hx : x.base ∈ S.Ωfin)
    (z : x.abv.Completion ⊗[L] Module.Dual L (L ⊗[K] E)) :
    (ξ.scalarExtension (L := L)).dual.norm x z =
      (ξ.dual.injectiveScalarExtension (L := L)).norm x
        ((dualBaseChangeEquiv K L E).symm.toLinearMap.baseChange x.abv.Completion z) := by
  have he : (ξ.scalarExtension (L := L)).dual.norm x z =
      (ξ.injectiveScalarExtension (L := L)).dual.norm x z := by
    change (S.algebraicExtension L).Ω at x
    change ((S.algebraicExtension L).ϕ x).Completion ⊗[L]
      Module.Dual L (L ⊗[K] E) at z
    rw [dual_norm_eq_sSup, dual_norm_eq_sSup]
    apply congrArg sSup
    apply congrArg Set.range
    funext y
    exact congrArg (fun a : ℝ =>
      ‖dualBaseChangeEquiv L ((S.algebraicExtension L).ϕ x).Completion
        (L ⊗[K] E) z y‖ / a) (ξ.scalarExtension_norm_of_mem_Ωfin x hx y)
  let d := dualBaseChangeEquiv K L E
  have h := ξ.injectiveScalarExtension_dual x ((scalarExtension_mem_Ωfin_iff x).mpr hx)
    (d.symm.toLinearMap.baseChange x.abv.Completion z)
  have hc : d.toLinearMap.baseChange x.abv.Completion
      (d.symm.toLinearMap.baseChange x.abv.Completion z) = z :=
    (LinearEquiv.baseChange L x.abv.Completion _ _ d).apply_symm_apply z
  rw [hc] at h
  exact he.trans h.symm

/-- At an infinite place the actual mixed dual agrees with the projective
extended dual on every completed vector, without a normalization premise. -/
theorem scalarExtension_dual_norm_of_not_mem_Ωfin (ξ : NormFamily S E)
    (x : S.ParameterSpaceExtension L) (hx : x.base ∉ S.Ωfin)
    (z : x.abv.Completion ⊗[L] Module.Dual L (L ⊗[K] E)) :
    (ξ.scalarExtension (L := L)).dual.norm x z =
      (ξ.projectiveScalarExtension (L := L)).dual.norm x z := by
  change (S.algebraicExtension L).Ω at x
  change ((S.algebraicExtension L).ϕ x).Completion ⊗[L]
    Module.Dual L (L ⊗[K] E) at z
  rw [dual_norm_eq_sSup, dual_norm_eq_sSup]
  apply congrArg sSup
  apply congrArg Set.range
  funext y
  exact congrArg (fun a : ℝ =>
    ‖dualBaseChangeEquiv L ((S.algebraicExtension L).ϕ x).Completion
      (L ⊗[K] E) z y‖ / a) (ξ.scalarExtension_norm_of_not_mem_Ωfin x hx y)

/-- Common countable density in the original curve proves measurability of
the actual mixed scalar-extended dual for every algebraic extension. -/
theorem IsMeasurable.scalarExtension_dual_of_common_countable_dense_subfield
    {ξ : NormFamily S E} (hξ : ξ.IsMeasurable)
    (hS : S.HasCommonCountableDenseSubfield) :
    (ξ.scalarExtension (L := L)).dual.IsMeasurable := by
  classical
  let d := dualBaseChangeEquiv K L E
  let η := (ξ.dual.injectiveScalarExtension (L := L)).pullback
    d.symm.toLinearMap d.symm.injective
  have hmdual := hξ.dual_of_common_countable_dense_subfield hS
  have hi0 := hmdual.injectiveScalarExtension_of_common_countable_dense_subfield (L := L) hS
  have hi : η.IsMeasurable :=
    hi0.pullback d.symm.toLinearMap d.symm.injective
  have hp := hξ.projectiveScalarExtension_dual_of_common_countable_dense_subfield
    (L := L) hS
  have hfin : MeasurableSet (S.algebraicExtension L).Ωfin := by
    have he : (S.algebraicExtension L).Ωfin = ((S.algebraicExtension L).Ωinf)ᶜ := by
      ext x
      simp only [AdelicStructure.Ωfin, AdelicStructure.Ωinf, Set.mem_ofPred_eq,
        Set.mem_compl_iff, not_not]
    rw [he]
    exact (S.algebraicExtension L).measurableSet_Ωinf.compl
  intro ℓ
  have he : (fun x : (S.algebraicExtension L).Ω =>
      (ξ.scalarExtension (L := L)).dual.norm x
        ((1 : x.abv.Completion) ⊗ₜ[L] ℓ)) =
      Set.piecewise (S.algebraicExtension L).Ωfin
        (fun x => η.norm x ((1 : x.abv.Completion) ⊗ₜ[L] ℓ))
        (fun x => (ξ.projectiveScalarExtension (L := L)).dual.norm x
          ((1 : x.abv.Completion) ⊗ₜ[L] ℓ)) := by
    funext x
    by_cases hx : x ∈ (S.algebraicExtension L).Ωfin
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
      exact ξ.scalarExtension_dual_norm_of_mem_Ωfin x
        ((scalarExtension_mem_Ωfin_iff x).mp hx) _
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
      exact ξ.scalarExtension_dual_norm_of_not_mem_Ωfin x
        (fun h => hx ((scalarExtension_mem_Ωfin_iff x).mpr h)) _
  change Measurable (fun x : (S.algebraicExtension L).Ω =>
    (ξ.scalarExtension (L := L)).dual.norm x ((1 : x.abv.Completion) ⊗ₜ[L] ℓ))
  rw [he]
  exact Measurable.piecewise hfin (hi ℓ) (hp ℓ)

end NormFamily

namespace AdelicVectorBundle

/-- The actual ordinary scalar extension, with primal and dual measurability
and domination proved from the original bundle rather than assumed. -/
def scalarExtension (V : AdelicVectorBundle S E)
    (hS : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    AdelicVectorBundle (S.algebraicExtension L) (L ⊗[K] E) where
  toNormFamily := V.toNormFamily.scalarExtension (L := L)
  isMeasurable := V.isMeasurable.scalarExtension_of_common_countable_dense_subfield hS hN
  dual_isMeasurable :=
    V.isMeasurable.scalarExtension_dual_of_common_countable_dense_subfield hS
  isDominated := (NormFamily.IsDominated.scalarExtension_isStronglyDominated
    V.toNormFamily V.isDominated (S.v_Ωinf_lt_top_of_isRCLike hN)).isDominated

@[simp]
theorem scalarExtension_toNormFamily (V : AdelicVectorBundle S E)
    (hS : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.scalarExtension (L := L) hS hN).toNormFamily =
      V.toNormFamily.scalarExtension (L := L) := rfl

/-- Ordinary scalar extension is strongly adelic even for arbitrary original
finite-place vector norms. -/
theorem scalarExtension_isStronglyAdelic (V : AdelicVectorBundle S E)
    (hS : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.scalarExtension (L := L) hS hN).IsStronglyAdelic :=
  NormFamily.IsDominated.scalarExtension_isStronglyDominated
    V.toNormFamily V.isDominated (S.v_Ωinf_lt_top_of_isRCLike hN)

/-- The finite-place norms of the actual extended bundle are ultrametric. -/
theorem scalarExtension_isUltrametric (V : AdelicVectorBundle S E)
    (hS : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.scalarExtension (L := L) hS hN).toNormFamily.IsUltrametric :=
  V.toNormFamily.scalarExtension_isUltrametric

/-- Extension preserves the actual rational rank, including zero. -/
theorem scalarExtension_rank (V : AdelicVectorBundle S E)
    (hS : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.scalarExtension (L := L) hS hN).rank = V.rank := Module.finrank_baseChange

/-- The canonical arbitrary-rank and existing line constructions agree. -/
theorem scalarExtension_eq_scalarExtensionLine (V : AdelicVectorBundle S E)
    (hV : V.IsLine) (hS : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.scalarExtension (L := L) hS hN = V.scalarExtensionLine (L := L) hV := by
  apply AdelicVectorBundle.ext
  rfl

/-- The actual finite scalar-extended bundle has the original vector degree.
Both extended normalization and extended common density are produced. -/
theorem degree_scalarExtension_of_finiteDimensional [S.IsProper] [FiniteDimensional K L]
    (V : AdelicVectorBundle S E) (hS : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.scalarExtension (L := L) hS hN).degree
      (Or.inr (hS.algebraicExtension_of_finiteDimensional (L := L)))
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) =
        V.degree (Or.inr hS) hN := by
  intro hp
  let := hp
  let hLS := hS.algebraicExtension_of_finiteDimensional (L := L)
  let hNL := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
  have he : (V.scalarExtension (L := L) hS hN).determinantOfMeasurableBase
      (Or.inr hLS) hNL = V.scalarExtensionDeterminant (L := L) (Or.inr hS) hN := by
    apply AdelicVectorBundle.ext
    rfl
  change (V.scalarExtension (L := L) hS hN).degree (Or.inr hLS) hNL = _
  rw [degree, he]
  exact V.lineDegree_scalarExtensionDeterminant (L := L) (Or.inr hS) hN

end AdelicVectorBundle

end ArakelovGeometry

end
