/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.AbsoluteLogarithmicMinima
public import ArakelovGeometry.AdelicVectorBundle.DegreeDeterminantIsometry
public import ArakelovGeometry.AdelicVectorBundle.DegreeIsometryDual
public import ArakelovGeometry.AdelicVectorBundle.TowerLogarithmicMinima

/-!
# Actual nested scalar bundles and rational sections through the associator

The direct ordinary scalar bundle produces the genuine nested scalar bundle
through tower transport and the canonical tensor associator. Its norm family
is fixed to the actual nested scalar extension. Intermediate place regularity
is not assumed. Canonical closure-field identification remains separate.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry
universe u v wL wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace NormFamily

/-- The actual nested scalar family is exactly the canonical associator
pullback of the direct scalar family's genuine tower transport. -/
theorem scalarExtension_tower_pullback (ξ : NormFamily S E) (F : IntermediateField K L) :
    ((ξ.scalarExtension (L := L)).towerPullback F).pullback
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).injective =
    (ξ.scalarExtension (L := F)).scalarExtension (L := L) := by
  ext x z
  exact (ξ.scalarExtension_trans x z).symm

/-- The canonical associator sends an actual nonzero nested rational section
to an actual nonzero direct rational section. -/
def scalarExtensionTowerNonzeroVector (F : IntermediateField K L)
    (s : {x : L ⊗[F] (F ⊗[K] E) // x ≠ 0}) : {x : L ⊗[K] E // x ≠ 0} :=
  ⟨TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E s.val,
    (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).map_eq_zero_iff.not.mpr
      s.property⟩

end NormFamily
namespace AdelicVectorBundle

private def associatorBundle (W : AdelicVectorBundle (S.algebraicExtension L) (L ⊗[K] E))
    (F : IntermediateField K L) :
    AdelicVectorBundle ((S.algebraicExtension F).algebraicExtension L)
      (L ⊗[F] (F ⊗[K] E)) := by
  let T := W.towerPullback F
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
  apply T.pullback c.toLinearMap c.injective
  apply NormFamily.IsMeasurable.of_completed_isometry T.toNormFamily.dual
    (T.toNormFamily.pullback c.toLinearMap c.injective).dual c.dualMap
  · intro ω z
    let η := T.toNormFamily.pullback c.toLinearMap c.injective
    exact η.dualEquiv_norm_eq_of_completed_isometry T.toNormFamily ω c (fun _ => rfl) z
  · exact T.dual_isMeasurable

/-- The genuine nested scalar bundle has the prescribed actual nested norm
family; all analytic fields are produced from the original direct bundle. -/
def scalarExtensionTower (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (F : IntermediateField K L) :
    AdelicVectorBundle ((S.algebraicExtension F).algebraicExtension L)
      (L ⊗[F] (F ⊗[K] E)) where
  toNormFamily := (V.toNormFamily.scalarExtension (L := F)).scalarExtension (L := L)
  isMeasurable := by
    rw [← V.toNormFamily.scalarExtension_tower_pullback F]
    exact (associatorBundle (V.ordinaryScalarExtension (L := L) hreg hN) F).isMeasurable
  dual_isMeasurable := by
    rw [← V.toNormFamily.scalarExtension_tower_pullback F]
    exact (associatorBundle (V.ordinaryScalarExtension (L := L) hreg hN) F).dual_isMeasurable
  isDominated := by
    rw [← V.toNormFamily.scalarExtension_tower_pullback F]
    exact (associatorBundle (V.ordinaryScalarExtension (L := L) hreg hN) F).isDominated

variable (V : AdelicVectorBundle S E)
  (hreg : S.HasCommonCountableDenseSubfield ∨
    (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
    (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (F : IntermediateField K L)

/-- Canonical coherence fixes the actual nested scalar family definitionally. -/
theorem scalarExtensionTower_toNormFamily :
    (V.scalarExtensionTower hreg hN F).toNormFamily =
      (V.toNormFamily.scalarExtension (L := F)).scalarExtension (L := L) := rfl

/-- The genuine canonical associator preserves actual rational vector degree
through the true tower measure, without regularity assumptions on S_F. -/
theorem scalarExtensionTower_vectorDegree
    (s : {x : L ⊗[F] (F ⊗[K] E) // x ≠ 0}) :
    (V.scalarExtensionTower hreg hN F).vectorDegree s =
      (V.ordinaryScalarExtension (L := L) hreg hN).vectorDegree
        (NormFamily.scalarExtensionTowerNonzeroVector F s) := by
  rw [vectorDegree, vectorDegree, NormFamily.vectorDegree_eq_neg_integral,
    NormFamily.vectorDegree_eq_neg_integral]
  have hn : ((V.toNormFamily.scalarExtension (L := F)).scalarExtension (L := L)).logNorm s.val =
      (V.toNormFamily.scalarExtension (L := L)).logNorm
        (NormFamily.scalarExtensionTowerNonzeroVector F s).val ∘
          AdelicStructure.Algebraic.towerMeasurableEquiv S F := by
    funext x
    exact congrArg Real.log (by
      change ((V.toNormFamily.scalarExtension (L := F)).scalarExtension (L := L)).norm x
        ((1 : x.abv.Completion) ⊗ₜ[L] s.val) =
          (V.toNormFamily.scalarExtension (L := L)).norm (scalarExtensionTowerPlace x)
            ((1 : x.abv.Completion) ⊗ₜ[L]
              (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E s.val))
      apply (V.toNormFamily.scalarExtension_trans x
        ((1 : x.abv.Completion) ⊗ₜ[L] s.val)).trans
      apply congrArg ((V.toNormFamily.scalarExtension (L := L)).norm (scalarExtensionTowerPlace x))
      exact LinearMap.baseChange_tmul _ _ _)
  change -(∫ x, ((V.toNormFamily.scalarExtension (L := F)).scalarExtension (L := L)).logNorm
    s.val x ∂((S.algebraicExtension F).algebraicExtension L).v) = _
  rw [hn]
  exact congrArg (fun t : ℝ => -t)
    ((measurePreserving_scalarExtensionTowerPlace (S := S) F).integral_comp
      (AdelicStructure.Algebraic.towerMeasurableEquiv S F).measurableEmbedding _)

/-- The canonical associator maps the actual nested threshold span onto the
actual direct threshold span, with equality of generating section degrees. -/
theorem scalarExtensionTower_degreeThresholdSpan_map (t : ℝ) :
    ((V.scalarExtensionTower hreg hN F).degreeThresholdSpan t).map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap =
      (V.ordinaryScalarExtension (L := L) hreg hN).degreeThresholdSpan t := by
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
  unfold degreeThresholdSpan
  rw [← Submodule.span_image]
  apply congrArg (Submodule.span L)
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hd⟩, rfl⟩
    refine ⟨c.map_eq_zero_iff.not.mpr hx, ?_⟩
    exact (V.scalarExtensionTower_vectorDegree hreg hN F ⟨x, hx⟩) ▸ hd
  · rintro ⟨hy, hd⟩
    let s : {x : L ⊗[F] (F ⊗[K] E) // x ≠ 0} :=
      ⟨c.symm y, c.symm.map_eq_zero_iff.not.mpr hy⟩
    refine ⟨s.val, ⟨s.property, ?_⟩, c.apply_symm_apply y⟩
    change t ≤ (V.scalarExtensionTower hreg hN F).vectorDegree s
    rw [V.scalarExtensionTower_vectorDegree hreg hN F s]
    have hs : NormFamily.scalarExtensionTowerNonzeroVector F s = ⟨y, hy⟩ :=
      Subtype.ext (c.apply_symm_apply y)
    rw [hs]
    exact hd

/-- Attained independent high-degree families exist on one side exactly when
they exist on the other. This statement does not assert supremum attainment. -/
theorem scalarExtensionTower_independent_degree_ge_iff (i : ℕ) (t : ℝ) :
    (∃ s : Fin i → {x : L ⊗[F] (F ⊗[K] E) // x ≠ 0},
      LinearIndependent L (fun j => (s j).val) ∧
        ∀ j, t ≤ (V.scalarExtensionTower hreg hN F).vectorDegree (s j)) ↔
    (∃ s : Fin i → {x : L ⊗[K] E // x ≠ 0},
      LinearIndependent L (fun j => (s j).val) ∧
        ∀ j, t ≤ (V.ordinaryScalarExtension (L := L) hreg hN).vectorDegree (s j)) := by
  rw [← le_finrank_degreeThresholdSpan_iff, ← le_finrank_degreeThresholdSpan_iff]
  have hr := (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).finrank_map_eq
    ((V.scalarExtensionTower hreg hN F).degreeThresholdSpan t)
  rw [V.scalarExtensionTower_degreeThresholdSpan_map hreg hN F t] at hr
  rw [hr]

/-- Exact all-index logarithmic-minimum transport, with empty and unbounded
cuts retained and no regularity hypothesis on the intermediate place space. -/
theorem scalarExtensionTower_logarithmicMinimum (i : ℕ) :
    (V.scalarExtensionTower hreg hN F).logarithmicMinimum i =
      (V.ordinaryScalarExtension (L := L) hreg hN).logarithmicMinimum i := by
  unfold logarithmicMinimum
  apply iSup_congr
  intro t
  have hr := (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).finrank_map_eq
    ((V.scalarExtensionTower hreg hN F).degreeThresholdSpan t)
  rw [V.scalarExtensionTower_degreeThresholdSpan_map hreg hN F t] at hr
  rw [hr]

/-- The actual first minimum is preserved, including rank-zero bottom. -/
theorem scalarExtensionTower_maximalLogarithmicMinimum :
    (V.scalarExtensionTower hreg hN F).maximalLogarithmicMinimum =
      (V.ordinaryScalarExtension (L := L) hreg hN).maximalLogarithmicMinimum :=
  V.scalarExtensionTower_logarithmicMinimum hreg hN F 1

/-- The actual last minimum is preserved because the canonical associator
also preserves actual ambient rank, including the rank-zero top convention. -/
theorem scalarExtensionTower_minimalLogarithmicMinimum :
    (V.scalarExtensionTower hreg hN F).minimalLogarithmicMinimum =
      (V.ordinaryScalarExtension (L := L) hreg hN).minimalLogarithmicMinimum := by
  unfold minimalLogarithmicMinimum
  rw [V.scalarExtensionTower_logarithmicMinimum hreg hN F]
  rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).finrank_eq]

end AdelicVectorBundle
end ArakelovGeometry
