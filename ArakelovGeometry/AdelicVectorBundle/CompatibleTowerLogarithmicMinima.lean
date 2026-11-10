/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.CompatibleTowerMeasure
public import ArakelovGeometry.AdelicVectorBundle.AbsoluteLogarithmicMinima
public import ArakelovGeometry.AdelicVectorBundle.DegreeDeterminantIsometry
public import ArakelovGeometry.AdelicVectorBundle.DegreeIsometryDual
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionTowerTransport

/-!
# Genuine nested scalar bundles in compatible external algebraic towers

All analytic fields are produced from the original ordinary direct scalar
bundle and the actual compatible-tower measure. Intermediate regularity is not
assumed; the resulting norm family is the real nested scalar-extension family.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
universe u v wL wM wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {M : Type wM} [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Algebra.IsAlgebraic L M] [Algebra.IsAlgebraic K M]

section Pullback
variable {X : Type*} [AddCommGroup X] [Module M X]

namespace NormFamily

/-- The actual completed family composed with the compatible external tower map. -/
def compatibleTowerPullback (ξ : NormFamily (S.algebraicExtension M) X) :
    NormFamily ((S.algebraicExtension L).algebraicExtension M) X where
  norm x := ξ.norm (scalarExtensionTowerPlace x)
  norm_eq_zero_iff x := ξ.norm_eq_zero_iff (scalarExtensionTowerPlace x)

/-- The transported completed norm is the original norm at the actual tower place. -/
@[simp] theorem compatibleTowerPullback_norm (ξ : NormFamily (S.algebraicExtension M) X)
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension L) M)
    (z : x.abv.Completion ⊗[M] X) :
    (ξ.compatibleTowerPullback (L := L)).norm x z =
      ξ.norm (scalarExtensionTowerPlace x) z := rfl

/-- Actual rational logarithmic norms compose with the genuine place equivalence. -/
@[simp] theorem compatibleTowerPullback_logNorm (ξ : NormFamily (S.algebraicExtension M) X)
    (z : X) :
    (ξ.compatibleTowerPullback (L := L)).logNorm z =
      ξ.logNorm z ∘ AdelicStructure.Algebraic.compatibleTowerMeasurableEquiv (L := L) S := rfl

/-- Actual operator dual norms commute with external tower pullback. -/
@[simp] theorem compatibleTowerPullback_dual [FiniteDimensional M X]
    (ξ : NormFamily (S.algebraicExtension M) X) :
    (ξ.compatibleTowerPullback (L := L)).dual = ξ.dual.compatibleTowerPullback (L := L) := by
  ext x z
  rfl

/-- Rational primal measurability transports by the actual measurable place map. -/
theorem IsMeasurable.compatibleTowerPullback {ξ : NormFamily (S.algebraicExtension M) X}
    (hξ : ξ.IsMeasurable) : (ξ.compatibleTowerPullback (L := L)).IsMeasurable := by
  intro z
  exact (hξ z).comp
    (AdelicStructure.Algebraic.compatibleTowerMeasurableEquiv (L := L) S).measurable

/-- Integrable envelopes transport through the produced actual measure identity. -/
theorem IsUpperDominated.compatibleTowerPullback {ξ : NormFamily (S.algebraicExtension M) X}
    (hξ : ξ.IsUpperDominated) : (ξ.compatibleTowerPullback (L := L)).IsUpperDominated := by
  intro z hz
  rw [compatibleTowerPullback_logNorm]
  exact (hξ z hz).comp_measurePreserving
    (AdelicStructure.Algebraic.measurePreserving_compatibleTowerMeasurableEquiv (L := L) S)

/-- Both actual dual upper envelopes transport, producing domination. -/
theorem IsDominated.compatibleTowerPullback [FiniteDimensional M X]
    {ξ : NormFamily (S.algebraicExtension M) X} (hξ : ξ.IsDominated) :
    (ξ.compatibleTowerPullback (L := L)).IsDominated := by
  refine ⟨hξ.1.compatibleTowerPullback, ?_⟩
  rw [compatibleTowerPullback_dual]
  exact hξ.2.compatibleTowerPullback

end NormFamily
namespace AdelicVectorBundle
variable [FiniteDimensional M X]

/-- A genuine direct bundle gives a genuine bundle on the actual iterated curve. -/
def compatibleTowerPullback (V : AdelicVectorBundle (S.algebraicExtension M) X) :
    AdelicVectorBundle ((S.algebraicExtension L).algebraicExtension M) X where
  toNormFamily := V.toNormFamily.compatibleTowerPullback (L := L)
  isMeasurable := V.isMeasurable.compatibleTowerPullback
  dual_isMeasurable := by
    rw [NormFamily.compatibleTowerPullback_dual]
    exact V.dual_isMeasurable.compatibleTowerPullback
  isDominated := V.isDominated.compatibleTowerPullback

/-- The actual norm family of the genuine bundle is definitionally the transported family. -/
@[simp] theorem compatibleTowerPullback_toNormFamily
    (V : AdelicVectorBundle (S.algebraicExtension M) X) :
    (V.compatibleTowerPullback (L := L)).toNormFamily =
      V.toNormFamily.compatibleTowerPullback (L := L) := rfl

end AdelicVectorBundle
end Pullback

variable {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace NormFamily

/-- The actual nested scalar family is exactly the canonical associator
pullback of the direct scalar family's genuine tower transport. -/
theorem scalarExtension_compatibleTower_pullback (ξ : NormFamily S E) :
    ((ξ.scalarExtension (L := M)).compatibleTowerPullback (L := L)).pullback
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E).toLinearMap
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E).injective =
    (ξ.scalarExtension (L := L)).scalarExtension (L := M) := by
  ext x z
  exact (ξ.scalarExtension_trans x z).symm

/-- The canonical associator sends an actual nonzero nested rational section
to an actual nonzero direct rational section. -/
def compatibleTowerNonzeroVector
    (s : {x : M ⊗[L] (L ⊗[K] E) // x ≠ 0}) : {x : M ⊗[K] E // x ≠ 0} :=
  ⟨TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E s.val,
    (TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E).map_eq_zero_iff.not.mpr
      s.property⟩

end NormFamily
namespace AdelicVectorBundle

private def compatibleAssociatorBundle
    (W : AdelicVectorBundle (S.algebraicExtension M) (M ⊗[K] E)) :
    AdelicVectorBundle ((S.algebraicExtension L).algebraicExtension M)
      (M ⊗[L] (L ⊗[K] E)) := by
  let T := W.compatibleTowerPullback (L := L)
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E
  apply T.pullback c.toLinearMap c.injective
  apply NormFamily.IsMeasurable.of_completed_isometry T.toNormFamily.dual
    (T.toNormFamily.pullback c.toLinearMap c.injective).dual c.dualMap
  · intro ω z
    let η := T.toNormFamily.pullback c.toLinearMap c.injective
    exact η.dualEquiv_norm_eq_of_completed_isometry T.toNormFamily ω c (fun _ => rfl) z
  · exact T.dual_isMeasurable

/-- The genuine nested scalar bundle has the prescribed actual nested norm
family; all analytic fields are produced from the original direct bundle. -/
def ordinaryCompatibleTower (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    AdelicVectorBundle ((S.algebraicExtension L).algebraicExtension M)
      (M ⊗[L] (L ⊗[K] E)) where
  toNormFamily := (V.toNormFamily.scalarExtension (L := L)).scalarExtension (L := M)
  isMeasurable := by
    rw [← V.toNormFamily.scalarExtension_compatibleTower_pullback (L := L)]
    exact (compatibleAssociatorBundle (L := L)
      (V.ordinaryScalarExtension (L := M) hreg hN)).isMeasurable
  dual_isMeasurable := by
    rw [← V.toNormFamily.scalarExtension_compatibleTower_pullback (L := L)]
    exact (compatibleAssociatorBundle (L := L)
      (V.ordinaryScalarExtension (L := M) hreg hN)).dual_isMeasurable
  isDominated := by
    rw [← V.toNormFamily.scalarExtension_compatibleTower_pullback (L := L)]
    exact (compatibleAssociatorBundle (L := L)
      (V.ordinaryScalarExtension (L := M) hreg hN)).isDominated

variable (V : AdelicVectorBundle S E)
  (hreg : S.HasCommonCountableDenseSubfield ∨
    (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
    (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)


/-- Canonical coherence fixes the actual nested scalar family definitionally. -/
theorem ordinaryCompatibleTower_toNormFamily :
    (V.ordinaryCompatibleTower (L := L) (M := M) hreg hN).toNormFamily =
      (V.toNormFamily.scalarExtension (L := L)).scalarExtension (L := M) := rfl

/-- The genuine canonical associator preserves actual rational vector degree
through the true tower measure, without regularity assumptions on S_L. -/
theorem ordinaryCompatibleTower_vectorDegree
    (s : {x : M ⊗[L] (L ⊗[K] E) // x ≠ 0}) :
    (V.ordinaryCompatibleTower (L := L) (M := M) hreg hN).vectorDegree s =
      (V.ordinaryScalarExtension (L := M) hreg hN).vectorDegree
        (NormFamily.compatibleTowerNonzeroVector (L := L) s) := by
  rw [vectorDegree, vectorDegree, NormFamily.vectorDegree_eq_neg_integral,
    NormFamily.vectorDegree_eq_neg_integral]
  have hn : ((V.toNormFamily.scalarExtension (L := L)).scalarExtension (L := M)).logNorm s.val =
      (V.toNormFamily.scalarExtension (L := M)).logNorm
        (NormFamily.compatibleTowerNonzeroVector (L := L) s).val ∘
          AdelicStructure.Algebraic.compatibleTowerMeasurableEquiv (L := L) (M := M) S := by
    funext x
    exact congrArg Real.log (by
      change ((V.toNormFamily.scalarExtension (L := L)).scalarExtension (L := M)).norm x
        ((1 : x.abv.Completion) ⊗ₜ[M] s.val) =
          (V.toNormFamily.scalarExtension (L := M)).norm (scalarExtensionTowerPlace x)
            ((1 : x.abv.Completion) ⊗ₜ[M]
              (TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E s.val))
      apply (V.toNormFamily.scalarExtension_trans x
        ((1 : x.abv.Completion) ⊗ₜ[M] s.val)).trans
      apply congrArg ((V.toNormFamily.scalarExtension (L := M)).norm (scalarExtensionTowerPlace x))
      exact LinearMap.baseChange_tmul _ _ _)
  change -(∫ x, ((V.toNormFamily.scalarExtension (L := L)).scalarExtension (L := M)).logNorm
    s.val x ∂((S.algebraicExtension L).algebraicExtension M).v) = _
  rw [hn]
  exact congrArg (fun t : ℝ => -t)
    (AdelicStructure.Algebraic.integral_comp_compatibleTowerMeasurableEquiv
      (L := L) (M := M) S _)

/-- The canonical associator maps the actual nested threshold span onto the
actual direct threshold span, with equality of generating section degrees. -/
theorem ordinaryCompatibleTower_degreeThresholdSpan_map (t : ℝ) :
    ((V.ordinaryCompatibleTower (L := L) (M := M) hreg hN).degreeThresholdSpan t).map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E).toLinearMap =
      (V.ordinaryScalarExtension (L := M) hreg hN).degreeThresholdSpan t := by
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E
  unfold degreeThresholdSpan
  rw [← Submodule.span_image]
  apply congrArg (Submodule.span M)
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hd⟩, rfl⟩
    refine ⟨c.map_eq_zero_iff.not.mpr hx, ?_⟩
    exact (V.ordinaryCompatibleTower_vectorDegree (L := L) (M := M) hreg hN ⟨x, hx⟩) ▸ hd
  · rintro ⟨hy, hd⟩
    let s : {x : M ⊗[L] (L ⊗[K] E) // x ≠ 0} :=
      ⟨c.symm y, c.symm.map_eq_zero_iff.not.mpr hy⟩
    refine ⟨s.val, ⟨s.property, ?_⟩, c.apply_symm_apply y⟩
    change t ≤ (V.ordinaryCompatibleTower (L := L) (M := M) hreg hN).vectorDegree s
    rw [V.ordinaryCompatibleTower_vectorDegree (L := L) (M := M) hreg hN s]
    have hs : NormFamily.compatibleTowerNonzeroVector (L := L) s = ⟨y, hy⟩ :=
      Subtype.ext (c.apply_symm_apply y)
    rw [hs]
    exact hd

/-- Attained independent high-degree families exist on one side exactly when
they exist on the other. This statement does not assert supremum attainment. -/
theorem ordinaryCompatibleTower_independent_degree_ge_iff (i : ℕ) (t : ℝ) :
    (∃ s : Fin i → {x : M ⊗[L] (L ⊗[K] E) // x ≠ 0},
      LinearIndependent M (fun j => (s j).val) ∧
        ∀ j, t ≤ (V.ordinaryCompatibleTower (L := L) (M := M) hreg hN).vectorDegree (s j)) ↔
    (∃ s : Fin i → {x : M ⊗[K] E // x ≠ 0},
      LinearIndependent M (fun j => (s j).val) ∧
        ∀ j, t ≤ (V.ordinaryScalarExtension (L := M) hreg hN).vectorDegree (s j)) := by
  rw [← le_finrank_degreeThresholdSpan_iff, ← le_finrank_degreeThresholdSpan_iff]
  have hr := (TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E).finrank_map_eq
    ((V.ordinaryCompatibleTower (L := L) (M := M) hreg hN).degreeThresholdSpan t)
  rw [V.ordinaryCompatibleTower_degreeThresholdSpan_map (L := L) (M := M) hreg hN t] at hr
  rw [hr]

/-- Exact all-index logarithmic-minimum transport, with empty and unbounded
cuts retained and no regularity hypothesis on the intermediate place space. -/
theorem ordinaryCompatibleTower_logarithmicMinimum (i : ℕ) :
    (V.ordinaryCompatibleTower (L := L) (M := M) hreg hN).logarithmicMinimum i =
      (V.ordinaryScalarExtension (L := M) hreg hN).logarithmicMinimum i := by
  unfold logarithmicMinimum
  apply iSup_congr
  intro t
  have hr := (TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E).finrank_map_eq
    ((V.ordinaryCompatibleTower (L := L) (M := M) hreg hN).degreeThresholdSpan t)
  rw [V.ordinaryCompatibleTower_degreeThresholdSpan_map (L := L) (M := M) hreg hN t] at hr
  rw [hr]

/-- The actual first minimum is preserved, including rank-zero bottom. -/
theorem ordinaryCompatibleTower_maximalLogarithmicMinimum :
    (V.ordinaryCompatibleTower (L := L) (M := M) hreg hN).maximalLogarithmicMinimum =
      (V.ordinaryScalarExtension (L := M) hreg hN).maximalLogarithmicMinimum :=
  V.ordinaryCompatibleTower_logarithmicMinimum (L := L) (M := M) hreg hN 1

/-- The actual last minimum is preserved because the canonical associator
also preserves actual ambient rank, including the rank-zero top convention. -/
theorem ordinaryCompatibleTower_minimalLogarithmicMinimum :
    (V.ordinaryCompatibleTower (L := L) (M := M) hreg hN).minimalLogarithmicMinimum =
      (V.ordinaryScalarExtension (L := M) hreg hN).minimalLogarithmicMinimum := by
  unfold minimalLogarithmicMinimum
  rw [V.ordinaryCompatibleTower_logarithmicMinimum (L := L) (M := M) hreg hN]
  rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E).finrank_eq]

end AdelicVectorBundle
end ArakelovGeometry
