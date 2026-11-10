/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Countable
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Algebraic.ClosureApproximation
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Discrete.Restriction
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.Algebraic.ScalarBundle
import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Subquotient
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Domination.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.FiniteStage.RestrictionIsometry
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.Algebraic.ScalarExtensionMeasurable
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.FinitePositiveAtoms
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.ScalarExtensionMeasurable
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Tower.Transport

/-!
# Actual geometric native restriction bundles

Produced finite stages give dual measurability of every actual native
restriction over an algebraic closure. The resulting strongly adelic bundle
lives on the subspace itself and agrees with the existing common-density and
countable-discrete constructions wherever those are defined.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [MeasurableSingletonClass S.Ω]

namespace NormFamily

/-- Actual restricted dual measurability, produced by finite descent and
positive finite-extension atoms, with no original regularity assumption. -/
theorem IsDominated.scalarExtension_restrict_dual_isMeasurable_of_positive_atoms_of_isAlgClosed
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (A : Submodule L (L ⊗[K] E)) :
    ((ξ.scalarExtension (L := L)).restrict A).dual.IsMeasurable := by
  let hN := AdelicStructure.isRCLikeNormedField_of_forall_mem_Ωfin hS
  obtain ⟨F, _, B, _, _, he⟩ := ξ.exists_complexFiniteStage_restriction_isometries hN
    (fun _ : Fin 1 => A)
  obtain ⟨e, he⟩ := he 0
  let η₀ := (ξ.scalarExtension (L := F)).restrict (B 0)
  let η := η₀.scalarExtension (L := L)
  let θ := (ξ.scalarExtension (L := L)).restrict A
  let : MeasurableSingletonClass (S.algebraicExtension F).Ω :=
    AdelicStructure.measurableSingletonClass_algebraicExtension_of_finiteDimensional
      (S := S) (L := F)
  have hFpos (x : (S.algebraicExtension F).Ω) :
      0 < (S.algebraicExtension F).v {x} :=
    AdelicStructure.Algebraic.singleton_pos_algebraicExtension_of_finiteDimensional S hpos x
  have hFS (x : (S.algebraicExtension F).Ω) : x ∈ (S.algebraicExtension F).Ωfin :=
    (AdelicStructure.mem_Ωfin_algebraicExtension_iff x).mpr (hS x.base)
  have hd₀ : η₀.IsDominated :=
    (hξ.scalarExtension_isStronglyDominated ξ
      (S.v_Ωinf_lt_top_of_isRCLike hN)).isDominated.restrict (B 0)
  have hm : η.dual.IsMeasurable :=
    hd₀.scalarExtension_dual_isMeasurable_of_positive_atoms_of_isAlgebraic η₀ hFpos hFS
  exact IsMeasurable.dual_of_tower_completed_isometry F η θ e he hm

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
      (L := L) (AdelicStructure.isRCLikeNormedField_of_forall_mem_Ωfin hS))

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
