/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Minima.Absolute.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Isomorphism.Subspace

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.EquivMeasure
import ArakelovGeometry.AdelicVectorBundle.Minima.Basis
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Algebraic.CommonClosure
import Mathlib.CategoryTheory.Category.Init

/-!
# Rational section degrees and minima under coefficient-field isomorphisms

The actual scalar semilinear tensor equivalence preserves rational logarithmic
norm profiles through the genuine place equivalence. Its integral identity
needs no analytic hypothesis. Genuine original-produced ordinary scalar bundles
then supply all analytic fields required for their actual vector degrees and
logarithmic minima, without regularity assumptions on an extension place space.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry
universe u v wL wM wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type wL} [Field L] {M : Type wM} [Field M] [Algebra K L] [Algebra K M]
  [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K M]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace NormFamily
open AdelicStructure.ParameterSpaceExtension

/-- The actual coefficient-field tensor equivalence preserves nonzero rational sections. -/
def scalarExtensionIsomorphismNonzeroVector (σ : L ≃ₐ[K] M)
    (s : {x : L ⊗[K] E // x ≠ 0}) : {x : M ⊗[K] E // x ≠ 0} := by
  let := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  exact ⟨scalarExtensionSemilinearEquiv (E := E) σ s.val,
    (scalarExtensionSemilinearEquiv (E := E) σ).map_eq_zero_iff.not.mpr s.property⟩

/-- Equality of actual logarithmic norm profiles after the genuine place transport. -/
theorem scalarExtension_logNorm_algEquiv (ξ : NormFamily S E) (σ : L ≃ₐ[K] M)
    (z : L ⊗[K] E) :
    (ξ.scalarExtension (L := M)).logNorm (scalarExtensionSemilinearEquiv (E := E) σ z) =
      (ξ.scalarExtension (L := L)).logNorm z ∘ algEquivMeasurableEquiv S σ := by
  funext x
  exact congrArg Real.log (ξ.scalarExtension_norm_rational_algEquiv σ x z)

/-- The genuine invertible measure transport identifies actual log integrals;
no domination, measurability or integrability premise is added here. -/
theorem scalarExtension_integral_logNorm_algEquiv (ξ : NormFamily S E) (σ : L ≃ₐ[K] M)
    (z : L ⊗[K] E) :
    (∫ x, (ξ.scalarExtension (L := M)).logNorm
      (scalarExtensionSemilinearEquiv (E := E) σ z) x ∂(S.algebraicExtension M).v) =
      ∫ x, (ξ.scalarExtension (L := L)).logNorm z x ∂(S.algebraicExtension L).v := by
  rw [ξ.scalarExtension_logNorm_algEquiv σ z]
  exact (AdelicStructure.Algebraic.measurePreserving_algEquivMeasurableEquiv S σ).integral_comp
    (algEquivMeasurableEquiv S σ).measurableEmbedding _

/-- Equality of actual vector degrees whenever their genuine vector divisors
are defined; the norm and measure identities are proved, not assumed. -/
theorem scalarExtension_vectorDegree_algEquiv (ξ : NormFamily S E) (σ : L ≃ₐ[K] M)
    [hdL : (ξ.scalarExtension (L := L)).IsDominated]
    [hmL : (ξ.scalarExtension (L := L)).IsMeasurable]
    [hdM : (ξ.scalarExtension (L := M)).IsDominated]
    [hmM : (ξ.scalarExtension (L := M)).IsMeasurable]
    (s : {x : L ⊗[K] E // x ≠ 0}) :
    (ξ.scalarExtension (L := M)).vectorDegree
      (scalarExtensionIsomorphismNonzeroVector σ s) =
      (ξ.scalarExtension (L := L)).vectorDegree s := by
  rw [vectorDegree_eq_neg_integral, vectorDegree_eq_neg_integral]
  exact congrArg (fun a : ℝ => -a) (ξ.scalarExtension_integral_logNorm_algEquiv σ s.val)

end NormFamily

private theorem independent_semilinear_iff
    {A B U W : Type*} [Field A] [Field B] [AddCommGroup U] [AddCommGroup W]
    [Module A U] [Module B W] (σ : A ≃+* B) :
    letI := RingHomInvPair.of_ringEquiv σ
    letI := RingHomInvPair.of_ringEquiv_symm σ
    ∀ (c : U ≃ₛₗ[(σ : A →+* B)] W) {ι : Type*} (s : ι → U),
      LinearIndependent B (fun j => c (s j)) ↔ LinearIndependent A s := by
  let := RingHomInvPair.of_ringEquiv σ
  let := RingHomInvPair.of_ringEquiv_symm σ
  intro c ι s
  constructor
  · intro h
    have hb := h.map_of_surjective_injectiveₛ σ.symm c.symm.toAddEquiv.toAddMonoidHom
      σ.symm.surjective c.symm.injective (fun r m => c.symm.map_smulₛₗ r m)
    change LinearIndependent A (fun j => c.symm (c (s j))) at hb
    simpa only [c.symm_apply_apply] using hb
  · intro h
    exact h.map_of_surjective_injectiveₛ σ c.toAddEquiv.toAddMonoidHom
      σ.surjective c.injective (fun r m => c.map_smulₛₗ r m)

omit [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K M] [FiniteDimensional K E] in
/-- The actual coefficient-field tensor equivalence preserves and reflects
independence over the literal extension fields. -/
theorem scalarExtension_linearIndependent_algEquiv (σ : L ≃ₐ[K] M)
    {ι : Type*} (s : ι → L ⊗[K] E) :
    LinearIndependent M (fun j => scalarExtensionSemilinearEquiv (E := E) σ (s j)) ↔
      LinearIndependent L s :=
  independent_semilinear_iff σ.toRingEquiv (scalarExtensionSemilinearEquiv (E := E) σ) s

namespace AdelicVectorBundle
variable (V : AdelicVectorBundle.{wE} S)
  [hreg : S.HasRegularBase]
  [hN : S.IsArchimedeanNormalized]
  (σ : L ≃ₐ[K] M)

/-- Original-produced genuine scalar bundles have equal actual section degrees
under coefficient transport, with no regularity premise on S_L or S_M. -/
theorem ordinaryScalarExtension_vectorDegree_algEquiv
    (s : {x : L ⊗[K] V // x ≠ 0}) :
    (V.ordinaryScalarExtension (L := M)).vectorDegree
      (NormFamily.scalarExtensionIsomorphismNonzeroVector σ s) =
      (V.ordinaryScalarExtension (L := L)).vectorDegree s :=
  V.toNormFamily.scalarExtension_vectorDegree_algEquiv σ
    (hdL := (V.ordinaryScalarExtension).isDominated)
    (hmL := (V.ordinaryScalarExtension).isMeasurable)
    (hdM := (V.ordinaryScalarExtension).isDominated)
    (hmM := (V.ordinaryScalarExtension).isMeasurable) s

/-- The actual semilinear subspace map sends each genuine degree-threshold
span exactly onto its counterpart over the transported coefficient field. -/
theorem ordinaryScalarExtension_degreeThresholdSpan_algEquiv (t : ℝ) :
    scalarExtensionSubspaceOrderIso (E := V) σ
      ((V.ordinaryScalarExtension (L := L)).degreeThresholdSpan t) =
      (V.ordinaryScalarExtension (L := M)).degreeThresholdSpan t := by
  let := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  let c := scalarExtensionSemilinearEquiv (E := V) σ
  change Submodule.map c.toLinearMap _ = _
  unfold degreeThresholdSpan
  rw [← Submodule.span_image]
  apply congrArg (Submodule.span M)
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hd⟩, rfl⟩
    refine ⟨c.map_eq_zero_iff.not.mpr hx, ?_⟩
    change t ≤ (V.ordinaryScalarExtension (L := M)).vectorDegree
      (NormFamily.scalarExtensionIsomorphismNonzeroVector σ ⟨x, hx⟩)
    rw [V.ordinaryScalarExtension_vectorDegree_algEquiv σ]
    exact hd
  · rintro ⟨hy, hd⟩
    let s : {x : L ⊗[K] V // x ≠ 0} :=
      ⟨c.symm y, c.symm.map_eq_zero_iff.not.mpr hy⟩
    refine ⟨s.val, ⟨s.property, ?_⟩, c.apply_symm_apply y⟩
    change t ≤ (V.ordinaryScalarExtension (L := L)).vectorDegree s
    rw [← V.ordinaryScalarExtension_vectorDegree_algEquiv σ s]
    have hs : NormFamily.scalarExtensionIsomorphismNonzeroVector σ s = ⟨y, hy⟩ :=
      Subtype.ext (c.apply_symm_apply y)
    rw [hs]
    exact hd

include σ

/-- Exact attained independent thresholds transport in both directions;
supremum attainment is not assumed or concluded. -/
theorem ordinaryScalarExtension_independent_degree_ge_algEquiv (i : ℕ) (t : ℝ) :
    (∃ s : Fin i → {x : M ⊗[K] V // x ≠ 0},
      LinearIndependent M (fun j => (s j).val) ∧
        ∀ j, t ≤ (V.ordinaryScalarExtension (L := M)).vectorDegree (s j)) ↔
    (∃ s : Fin i → {x : L ⊗[K] V // x ≠ 0},
      LinearIndependent L (fun j => (s j).val) ∧
        ∀ j, t ≤ (V.ordinaryScalarExtension (L := L)).vectorDegree (s j)) := by
  rw [← (V.ordinaryScalarExtension (L := M)).le_finrank_degreeThresholdSpan_iff,
    ← (V.ordinaryScalarExtension (L := L)).le_finrank_degreeThresholdSpan_iff]
  have hr := scalarExtensionSubspaceOrderIso_finrank σ
    ((V.ordinaryScalarExtension (L := L)).degreeThresholdSpan t)
  rw [V.ordinaryScalarExtension_degreeThresholdSpan_algEquiv σ t] at hr
  rw [hr]

/-- Equality of all extended logarithmic minima through the genuine field
isomorphism, retaining empty and unbounded cuts. -/
theorem ordinaryScalarExtension_logarithmicMinimum_algEquiv (i : ℕ) :
    (V.ordinaryScalarExtension (L := M)).logarithmicMinimum i =
      (V.ordinaryScalarExtension (L := L)).logarithmicMinimum i := by
  unfold logarithmicMinimum
  apply iSup_congr
  intro t
  have hr := scalarExtensionSubspaceOrderIso_finrank σ
    ((V.ordinaryScalarExtension (L := L)).degreeThresholdSpan t)
  rw [V.ordinaryScalarExtension_degreeThresholdSpan_algEquiv σ t] at hr
  rw [hr]

/-- The first ordinary minimum agrees, including the rank-zero bottom convention. -/
theorem ordinaryScalarExtension_maximalLogarithmicMinimum_algEquiv :
    (V.ordinaryScalarExtension (L := M)).maximalLogarithmicMinimum =
      (V.ordinaryScalarExtension (L := L)).maximalLogarithmicMinimum :=
  V.ordinaryScalarExtension_logarithmicMinimum_algEquiv σ 1

/-- The last ordinary minimum agrees because both actual scalar ranks equal
the original rank, including the rank-zero top convention. -/
theorem ordinaryScalarExtension_minimalLogarithmicMinimum_algEquiv :
    (V.ordinaryScalarExtension (L := M)).minimalLogarithmicMinimum =
      (V.ordinaryScalarExtension (L := L)).minimalLogarithmicMinimum := by
  unfold minimalLogarithmicMinimum
  rw [V.ordinaryScalarExtension_logarithmicMinimum_algEquiv σ]
  simp only [Module.finrank_baseChange]

omit σ [Algebra K M] [Algebra.IsAlgebraic K M] in
/-- The actual absolute minimum may be evaluated in the compatible canonical
closure of any algebraic L/K via a direct genuine K-scalar bundle. -/
theorem absoluteLogarithmicMinimum_eq_commonClosure (i : ℕ) :
    V.absoluteLogarithmicMinimum i =
      (V.ordinaryScalarExtension (L := AlgebraicClosure L)).logarithmicMinimum i :=
  (V.ordinaryScalarExtension_logarithmicMinimum_algEquiv
    (commonAlgebraicClosureEquiv K L) i).symm

end AdelicVectorBundle
end ArakelovGeometry
