/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.CompatibleTowerDeterminantDegree
public import ArakelovGeometry.AdelicVectorBundle.GeometricAlgebraicRestrictionDegree
public import ArakelovGeometry.AdelicVectorBundle.Slopes

/-!
# Actual native restrictions through external algebraic towers

The associator restricts to each literal native subspace. Direct native
bundles produce ordinary iterated native bundles, determinant measurability
and canonical degrees, with no regularity premise on the intermediate curve.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry

section EquivalencePullback
variable {M : Type*} [Field M] {T : AdelicStructure M}
  {X Y : Type*} [AddCommGroup X] [Module M X] [FiniteDimensional M X]
  [AddCommGroup Y] [Module M Y] [FiniteDimensional M Y]

/-- Pull back an adelic bundle along a linear equivalence. -/
def nativeEquivalencePullback (V : AdelicVectorBundle T Y) (e : X ≃ₗ[M] Y) :
    AdelicVectorBundle T X := by
  apply V.pullback e.toLinearMap e.injective
  apply NormFamily.IsMeasurable.of_completed_isometry V.toNormFamily.dual
    (V.toNormFamily.pullback e.toLinearMap e.injective).dual e.dualMap
  · intro ω z
    let η := V.toNormFamily.pullback e.toLinearMap e.injective
    exact η.dualEquiv_norm_eq_of_completed_isometry V.toNormFamily ω e (fun _ => rfl) z
  · exact V.dual_isMeasurable

private theorem nativeEquivalencePullback_inverse_norm
    (V : AdelicVectorBundle T Y) (e : X ≃ₗ[M] Y) (ω : T.Ω)
    (z : (T.ϕ ω).Completion ⊗[M] Y) :
    (nativeEquivalencePullback V e).toNormFamily.norm ω
      (e.symm.toLinearMap.baseChange (T.ϕ ω).Completion z) = V.toNormFamily.norm ω z := by
  let eω := e.baseChange M (T.ϕ ω).Completion X Y
  change V.toNormFamily.norm ω (eω (eω.symm z)) = V.toNormFamily.norm ω z
  rw [eω.apply_symm_apply]

end EquivalencePullback

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic L M] [Algebra.IsAlgebraic K M]
  {S : AdelicStructure K}
  {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace NormFamily

private theorem nativeRestrictionTower_pullback
    {X Y : Type*} [AddCommGroup X] [Module M X] [AddCommGroup Y] [Module M Y]
    (η : NormFamily ((S.algebraicExtension L).algebraicExtension M) X)
    (θ : NormFamily (S.algebraicExtension M) Y) (e : X ≃ₗ[M] Y) (A : Submodule M X)
    (he : ∀ x z, θ.norm (scalarExtensionTowerPlace x)
      (e.toLinearMap.baseChange
        (((S.algebraicExtension L).algebraicExtension M).ϕ x).Completion z) = η.norm x z) :
    ((θ.restrict (A.map e.toLinearMap)).compatibleTowerPullback (L := L)).pullback
      (e.submoduleMap A).toLinearMap (e.submoduleMap A).injective = η.restrict A := by
  ext x z
  exact η.restrict_map_equiv_norm_eq (θ.compatibleTowerPullback (L := L)) e A x (he x) z

/-- The canonical associator identifies every actual restricted completed
norm, on the literal subspaces rather than quotient presentations. -/
theorem scalarExtension_compatibleTower_restrict_pullback (ξ : NormFamily S E)
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E
    (((ξ.scalarExtension (L := M)).restrict (A.map c.toLinearMap)).compatibleTowerPullback
      (L := L)).pullback (c.submoduleMap A).toLinearMap (c.submoduleMap A).injective =
        ((ξ.scalarExtension (L := L)).scalarExtension (L := M)).restrict A := by
  intro c
  exact nativeRestrictionTower_pullback _ _ c A (fun x z => (ξ.scalarExtension_trans x z).symm)

variable [IsAlgClosed M] [MeasurableSingletonClass S.Ω]

/-- Transport the direct native restriction to its iterated tensor-product subspace. -/
def nativeRestrictionTowerBundle (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    AdelicVectorBundle ((S.algebraicExtension L).algebraicExtension M) A :=
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E
  let R := ξ.nativeAlgebraicRestrictionOfPositiveAtoms hξ hpos hS (A.map c.toLinearMap)
  nativeEquivalencePullback (R.compatibleTowerPullback (L := L)) (c.submoduleMap A)

/-- Tower transport recovers the literal iterated restriction norm family. -/
theorem nativeRestrictionTowerBundle_normFamily (ξ : NormFamily S E)
    (hξ : ξ.IsDominated) (hpos : ∀ ω : S.Ω, 0 < S.v {ω})
    (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    (nativeRestrictionTowerBundle ξ hξ hpos hS A).toNormFamily =
      ((ξ.scalarExtension (L := L)).scalarExtension (L := M)).restrict A :=
  ξ.scalarExtension_compatibleTower_restrict_pullback A

/-- A genuine ordinary adelic bundle on each actual iterated native subspace,
with all fields produced from original positive finite atoms. -/
def nativeCompatibleTowerRestrictionOfPositiveAtoms (ξ : NormFamily S E)
    (hξ : ξ.IsDominated) (hpos : ∀ ω : S.Ω, 0 < S.v {ω})
    (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    AdelicVectorBundle ((S.algebraicExtension L).algebraicExtension M) A where
  toNormFamily := ((ξ.scalarExtension (L := L)).scalarExtension (L := M)).restrict A
  isMeasurable := by
    rw [← nativeRestrictionTowerBundle_normFamily ξ hξ hpos hS A]
    exact (nativeRestrictionTowerBundle ξ hξ hpos hS A).isMeasurable
  dual_isMeasurable := by
    rw [← nativeRestrictionTowerBundle_normFamily ξ hξ hpos hS A]
    exact (nativeRestrictionTowerBundle ξ hξ hpos hS A).dual_isMeasurable
  isDominated := by
    rw [← nativeRestrictionTowerBundle_normFamily ξ hξ hpos hS A]
    exact (nativeRestrictionTowerBundle ξ hξ hpos hS A).isDominated

@[simp]
theorem nativeCompatibleTowerRestrictionOfPositiveAtoms_toNormFamily (ξ : NormFamily S E)
    (hξ : ξ.IsDominated) (hpos : ∀ ω : S.Ω, 0 < S.v {ω})
    (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    (ξ.nativeCompatibleTowerRestrictionOfPositiveAtoms hξ hpos hS A).toNormFamily =
      ((ξ.scalarExtension (L := L)).scalarExtension (L := M)).restrict A := rfl

/-- Finite descent and the actual restricted associator produce determinant
measurability on the iterated curve without target regularity. -/
theorem IsDominated.compatibleTower_restrict_determinant_isMeasurable_of_positive_atoms
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    (((ξ.scalarExtension (L := L)).scalarExtension (L := M)).restrict A).determinant.IsMeasurable :=
    by
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E
  let R := ξ.nativeAlgebraicRestrictionOfPositiveAtoms hξ hpos hS (A.map c.toLinearMap)
  let T := R.compatibleTowerPullback (L := L)
  have hdet : T.toNormFamily.determinant.IsMeasurable :=
    R.toNormFamily.determinant_isMeasurable_compatibleTowerPullback
      (hξ.scalarExtension_restrict_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
        ξ hpos hS (A.map c.toLinearMap))
  rw [← nativeRestrictionTowerBundle_normFamily ξ hξ hpos hS A]
  exact T.toNormFamily.determinant_isMeasurable_of_completed_isometry
    (nativeEquivalencePullback T (c.submoduleMap A)).toNormFamily
    (c.submoduleMap A).symm (nativeEquivalencePullback_inverse_norm T (c.submoduleMap A)) hdet

variable [S.IsProper]

omit [MeasurableSingletonClass S.Ω] [S.IsProper] in
/-- An adelic structure with only finite places has no archimedean normalization conditions. -/
theorem nativeRestrictionTower_normalization (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion :=
  fun ω hω => False.elim (hω (hS ω))

/-- Canonical measurable-determinant degree of the literal iterated native
restriction; determinant measurability and normalization are produced. -/
def nativeCompatibleTowerRestrictionDegreeOfPositiveAtoms (ξ : NormFamily S E)
    (hξ : ξ.IsDominated) (hpos : ∀ ω : S.Ω, 0 < S.v {ω})
    (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) (A : Submodule M (M ⊗[L] (L ⊗[K] E))) : ℝ :=
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension L) M
  (ξ.nativeCompatibleTowerRestrictionOfPositiveAtoms hξ hpos hS A).degreeOfMeasurableDeterminant
    (hξ.compatibleTower_restrict_determinant_isMeasurable_of_positive_atoms
      ξ hpos hS A)
    (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M)
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L)
        (nativeRestrictionTower_normalization hS)))

/-- Every actual iterated native degree equals the actual direct native
degree of its associator image, without hypotheses on the intermediate curve. -/
theorem nativeCompatibleTowerRestrictionDegreeOfPositiveAtoms_eq_direct (ξ : NormFamily S E)
    (hξ : ξ.IsDominated) (hpos : ∀ ω : S.Ω, 0 < S.v {ω})
    (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    ξ.nativeCompatibleTowerRestrictionDegreeOfPositiveAtoms hξ hpos hS A =
      ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms hξ hpos hS
        (A.map (TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E).toLinearMap) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension L) M
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E
  let R := ξ.nativeAlgebraicRestrictionOfPositiveAtoms hξ hpos hS (A.map c.toLinearMap)
  let T := R.compatibleTowerPullback (L := L)
  let W := ξ.nativeCompatibleTowerRestrictionOfPositiveAtoms hξ hpos hS A
  let hdet := hξ.compatibleTower_restrict_determinant_isMeasurable_of_positive_atoms
    ξ hpos hS A
  let hN := nativeRestrictionTower_normalization hS
  let hNT := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M)
    (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN)
  have he : ∀ x z, T.toNormFamily.norm x
      ((c.submoduleMap A).toLinearMap.baseChange
        (((S.algebraicExtension L).algebraicExtension M).ϕ x).Completion z) =
        W.toNormFamily.norm x z := by
    intro x z
    exact DFunLike.congr_fun (congrArg (fun η => η.norm x)
      (ξ.scalarExtension_compatibleTower_restrict_pullback A)) z
  have hd := W.degreeOfMeasurableDeterminant_eq_of_completed_isometry
    T (c.submoduleMap A) hdet hNT he
  change W.degreeOfMeasurableDeterminant hdet hNT = _
  rw [hd]
  exact R.degreeOfMeasurableDeterminant_compatibleTowerPullback
    (hξ.scalarExtension_restrict_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
      ξ hpos hS (A.map c.toLinearMap)) hN

/-- Rank zero keeps the genuine empty-determinant degree zero. -/
theorem nativeCompatibleTowerRestrictionDegreeOfPositiveAtoms_eq_zero_of_finrank_eq_zero
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) (hr : Module.finrank M A = 0) :
    ξ.nativeCompatibleTowerRestrictionDegreeOfPositiveAtoms hξ hpos hS A = 0 := by
  rw [ξ.nativeCompatibleTowerRestrictionDegreeOfPositiveAtoms_eq_direct hξ hpos hS A]
  apply ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms_eq_zero_of_finrank_eq_zero
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E
  rw [← (c.submoduleMap A).finrank_eq, hr]

end NormFamily
end ArakelovGeometry
