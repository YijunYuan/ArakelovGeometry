/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.GeometricAlgebraicScalarBundle
import ArakelovGeometry.AdelicVectorBundle.GeometricFinitePositiveAtoms
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDiscreteRestriction
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionTowerTransport
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionTowerDeterminantDegree
import ArakelovGeometry.AdelicVectorBundle.AlgebraicClosureApproximation
import ArakelovGeometry.AdelicVectorBundle.DegreeIsometryDual

/-!
# Actual geometric native restriction bundles

Produced finite stages give dual measurability of every actual native
restriction over an algebraic closure. The resulting strongly adelic bundle
lives on the subspace itself and agrees with the existing common-density and
countable-discrete constructions wherever those are defined.
-/

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [MeasurableSingletonClass S.Ω]

namespace NormFamily

omit [MeasurableSingletonClass S.Ω] in
private theorem geometricRestriction_allFinite_normalization
    (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion := by
  intro ω hω
  exact False.elim (hω (hS ω))

/-- Actual restricted dual measurability, produced by finite descent and
positive finite-extension atoms, with no original regularity assumption. -/
theorem IsDominated.scalarExtension_restrict_dual_isMeasurable_of_positive_atoms_of_isAlgClosed
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (A : Submodule L (L ⊗[K] E)) :
    ((ξ.scalarExtension (L := L)).restrict A).dual.IsMeasurable := by
  let hN := geometricRestriction_allFinite_normalization hS
  obtain ⟨F, _, B, _, _, he⟩ := ξ.exists_complexFiniteStage_restriction_isometries hN
    (fun _ : Fin 1 => A)
  obtain ⟨e, he⟩ := he 0
  let η₀ := (ξ.scalarExtension (L := F)).restrict (B 0)
  let η := η₀.scalarExtension (L := L)
  let θ := (ξ.scalarExtension (L := L)).restrict A
  let θt := θ.towerPullback F.toIntermediateField
  let : MeasurableSingletonClass (S.algebraicExtension F).Ω :=
    AdelicStructure.measurableSingletonClass_algebraicExtension_of_finiteDimensional
      (S := S) (L := F)
  have hFpos (x : (S.algebraicExtension F).Ω) :
      0 < (S.algebraicExtension F).v {x} :=
    AdelicStructure.Algebraic.singleton_pos_algebraicExtension_of_finiteDimensional S hpos x
  have hFS (x : (S.algebraicExtension F).Ω) : x ∈ (S.algebraicExtension F).Ωfin :=
    (scalarExtension_mem_Ωfin_iff x).mpr (hS x.base)
  have hd₀ : η₀.IsDominated :=
    (hξ.scalarExtension_isStronglyDominated ξ
      (S.v_Ωinf_lt_top_of_isRCLike hN)).isDominated.restrict (B 0)
  have hm : η.dual.IsMeasurable :=
    hd₀.scalarExtension_dual_isMeasurable_of_positive_atoms_of_isAlgebraic η₀ hFpos hFS
  have ht : θt.dual.IsMeasurable := by
    intro ℓ
    have hn (x : ((S.algebraicExtension F).algebraicExtension L).Ω) :
        θt.dual.norm x ((1 : (((S.algebraicExtension F).algebraicExtension L).ϕ x).Completion)
          ⊗ₜ[L] ℓ) =
        η.dual.norm x ((1 : (((S.algebraicExtension F).algebraicExtension L).ϕ x).Completion)
          ⊗ₜ[L] e.dualMap ℓ) := by
      symm
      simpa only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe] using
        η.dualEquiv_norm_eq_of_completed_isometry θt x e (he x)
          ((1 : (((S.algebraicExtension F).algebraicExtension L).ϕ x).Completion) ⊗ₜ[L] ℓ)
    change Measurable (fun x : ((S.algebraicExtension F).algebraicExtension L).Ω =>
      θt.dual.norm x
        ((1 : (((S.algebraicExtension F).algebraicExtension L).ϕ x).Completion) ⊗ₜ[L] ℓ))
    rw [funext hn]
    exact hm (e.dualMap ℓ)
  change (θ.towerPullback F.toIntermediateField).dual.IsMeasurable at ht
  rw [towerPullback_dual] at ht
  exact (θ.dual.isMeasurable_towerPullback_iff F.toIntermediateField).mp ht

/-- The genuine native restriction on the actual subspace, with its produced
regularities and the existing canonical adelic-bundle structure. -/
def nativeAlgebraicRestrictionOfPositiveAtoms (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (A : Submodule L (L ⊗[K] E)) : AdelicVectorBundle (S.algebraicExtension L) A :=
  (ξ.algebraicScalarBundleOfPositiveAtoms (L := L) hξ hpos hS).restrict A
    (hξ.scalarExtension_restrict_dual_isMeasurable_of_positive_atoms_of_isAlgClosed ξ hpos hS A)

@[simp]
theorem nativeAlgebraicRestrictionOfPositiveAtoms_toNormFamily
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (A : Submodule L (L ⊗[K] E)) :
    (ξ.nativeAlgebraicRestrictionOfPositiveAtoms hξ hpos hS A).toNormFamily =
      (ξ.scalarExtension (L := L)).restrict A := rfl

/-- Restriction retains actual strong domination, including the zero subspace. -/
theorem nativeAlgebraicRestrictionOfPositiveAtoms_isStronglyAdelic
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (A : Submodule L (L ⊗[K] E)) :
    (ξ.nativeAlgebraicRestrictionOfPositiveAtoms hξ hpos hS A).IsStronglyAdelic :=
  IsStronglyDominated.restrict
    (ξ.algebraicScalarBundleOfPositiveAtoms_isStronglyAdelic (L := L) hξ hpos hS) A
    (AdelicStructure.isRCLikeNormedField_algebraicExtension
      (L := L) (geometricRestriction_allFinite_normalization hS))

end NormFamily
namespace AdelicVectorBundle

/-- The geometric and common-density restrictions have literally the same
completed norm family, hence the same canonical adelic bundle. -/
theorem nativeAlgebraicRestrictionOfPositiveAtoms_eq_common
    (V : AdelicVectorBundle S E)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule L (L ⊗[K] E)) :
    V.toNormFamily.nativeAlgebraicRestrictionOfPositiveAtoms V.isDominated hpos hS A =
      (V.scalarExtension (L := L) hcount hN).restrictOfMeasurableBase A
        (Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))) :=
  AdelicVectorBundle.ext rfl

/-- The geometric and countable-discrete native restrictions coincide on
their common domain, without a new extension regularity assumption. -/
theorem nativeAlgebraicRestrictionOfPositiveAtoms_eq_countable_discrete
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]
    (V : AdelicVectorBundle S E)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule L (L ⊗[K] E)) :
    V.toNormFamily.nativeAlgebraicRestrictionOfPositiveAtoms V.isDominated hpos hS A =
      V.scalarExtensionRestrictionOfCountableDiscreteBase (L := L) hN A :=
  AdelicVectorBundle.ext rfl

end AdelicVectorBundle
end ArakelovGeometry
