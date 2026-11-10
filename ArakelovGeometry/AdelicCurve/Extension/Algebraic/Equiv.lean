/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
public import ArakelovGeometry.AdelicCurve.Extension.Automorphism
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual algebraic extension places under base-field isomorphisms

Field isomorphisms transport the actual extension evaluations and projective
sigma algebras. The same-field restriction agrees with the existing action.
-/

@[expose] public section

open MeasureTheory
namespace ArakelovGeometry.AdelicStructure.ParameterSpaceExtension
universe u v wL wM wN
variable {K : Type u} [Field K] (S : AdelicStructure.{u, v} K)
  {L : Type wL} [Field L] [Algebra K L]
  {M : Type wM} [Field M] [Algebra K M]

/-- Pull back an actual extension place along a base-field isomorphism. -/
def pullbackAlgEquiv (σ : L ≃ₐ[K] M) (x : ParameterSpaceExtension S M) :
    ParameterSpaceExtension S L where
  base := x.base
  abv := x.abv.comp σ.toRingHom.injective
  restrict_eq := by
    ext a
    change x.abv (σ (algebraMap K L a)) = S.ϕ x.base a
    rw [σ.commutes]
    exact congrArg (fun z : AbsoluteValue K ℝ ↦ z a) x.restrict_eq

/-- Place transport fixes the actual original parameter. -/
@[simp]
theorem pullbackAlgEquiv_proj (σ : L ≃ₐ[K] M) (x : ParameterSpaceExtension S M) :
    (pullbackAlgEquiv S σ x).proj = x.proj := rfl

/-- Every transported evaluation is the original evaluation at the image. -/
@[simp]
theorem pullbackAlgEquiv_eval (σ : L ≃ₐ[K] M)
    (x : ParameterSpaceExtension S M) (a : L) :
    (pullbackAlgEquiv S σ x).ϕ a = x.ϕ (σ a) := rfl

/-- The same-field transport is the existing actual automorphism action. -/
theorem pullbackAlgEquiv_eq_aut (σ : L ≃ₐ[K] L) :
    pullbackAlgEquiv S σ = aut S L σ := rfl

/-- Identity field transport fixes every actual place. -/
@[simp]
theorem pullbackAlgEquiv_refl (x : ParameterSpaceExtension S L) :
    pullbackAlgEquiv S (AlgEquiv.refl : L ≃ₐ[K] L) x = x := by
  apply ext S L rfl
  ext a
  rfl

/-- Place pullback reverses composition of field isomorphisms. -/
theorem pullbackAlgEquiv_trans
    {N : Type wN} [Field N] [Algebra K N]
    (σ : L ≃ₐ[K] M) (τ : M ≃ₐ[K] N) (x : ParameterSpaceExtension S N) :
    pullbackAlgEquiv S (σ.trans τ) x =
      pullbackAlgEquiv S σ (pullbackAlgEquiv S τ x) := by
  apply ext S L rfl
  ext a
  rfl

/-- Field transport followed by its inverse fixes an actual source place. -/
@[simp]
theorem pullbackAlgEquiv_symm_pullback (σ : L ≃ₐ[K] M)
    (x : ParameterSpaceExtension S M) :
    pullbackAlgEquiv S σ.symm (pullbackAlgEquiv S σ x) = x := by
  refine ext S M ?_ ?_
  · rfl
  · ext a
    change x.abv (σ (σ.symm a)) = x.abv a
    rw [σ.apply_symm_apply]

/-- The inverse followed by field transport fixes an actual target place. -/
@[simp]
theorem pullbackAlgEquiv_pullback_symm (σ : L ≃ₐ[K] M)
    (x : ParameterSpaceExtension S L) :
    pullbackAlgEquiv S σ (pullbackAlgEquiv S σ.symm x) = x :=
  pullbackAlgEquiv_symm_pullback S σ.symm x

/-- Field isomorphism pullback is measurable for the actual evaluation generators. -/
theorem measurable_pullbackAlgEquiv (σ : L ≃ₐ[K] M) :
    Measurable (pullbackAlgEquiv S σ) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap _ (_ ⊔ ⨆ a : L, _) ≤ _
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
  refine sup_le ?_ (iSup_le fun a ↦ ?_)
  · rw [MeasurableSpace.comap_comp]
    exact (measurable_proj S M).comap_le
  · rw [MeasurableSpace.comap_comp]
    exact (measurable_eval S M (σ a)).comap_le

/-- Isomorphisms preserve and reflect the actual non-Archimedean triangle inequality. -/
theorem isNonarchimedean_pullbackAlgEquiv_iff (σ : L ≃ₐ[K] M)
    (x : ParameterSpaceExtension S M) :
    IsNonarchimedean (pullbackAlgEquiv S σ x).abv ↔ IsNonarchimedean x.abv := by
  constructor
  · intro h a b
    have hab := h (σ.symm a) (σ.symm b)
    change x.abv (σ (σ.symm a + σ.symm b)) ≤
      max (x.abv (σ (σ.symm a))) (x.abv (σ (σ.symm b))) at hab
    simpa only [map_add, σ.apply_symm_apply] using hab
  · intro h a b
    change x.abv (σ (a + b)) ≤ max (x.abv (σ a)) (x.abv (σ b))
    rw [map_add]
    exact h (σ a) (σ b)

variable [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K M]

/-- The canonical measurable equivalence uses the actual projective sigma
algebras of both algebraic extension adelic structures. -/
def algEquivMeasurableEquiv (σ : L ≃ₐ[K] M) :
    (S.algebraicExtension M).Ω ≃ᵐ (S.algebraicExtension L).Ω where
  toFun := pullbackAlgEquiv S σ
  invFun := pullbackAlgEquiv S σ.symm
  left_inv := pullbackAlgEquiv_symm_pullback S σ
  right_inv := pullbackAlgEquiv_pullback_symm S σ
  measurable_toFun := by
    change @Measurable (ParameterSpaceExtension S M) (ParameterSpaceExtension S L)
      (Algebraic.projectiveMeasurableSpace S M) (Algebraic.projectiveMeasurableSpace S L) _
    rw [Algebraic.projectiveMeasurableSpace_eq, Algebraic.projectiveMeasurableSpace_eq]
    exact measurable_pullbackAlgEquiv S σ
  measurable_invFun := by
    change @Measurable (ParameterSpaceExtension S L) (ParameterSpaceExtension S M)
      (Algebraic.projectiveMeasurableSpace S L) (Algebraic.projectiveMeasurableSpace S M) _
    rw [Algebraic.projectiveMeasurableSpace_eq, Algebraic.projectiveMeasurableSpace_eq]
    exact measurable_pullbackAlgEquiv S σ.symm

/-- The actual finite loci are preserved, and hence so are their infinite complements. -/
theorem pullbackAlgEquiv_mem_Ωfin_iff (σ : L ≃ₐ[K] M)
    (x : (S.algebraicExtension M).Ω) :
    pullbackAlgEquiv S σ x ∈ (S.algebraicExtension L).Ωfin ↔
      x ∈ (S.algebraicExtension M).Ωfin :=
  isNonarchimedean_pullbackAlgEquiv_iff S σ x

end ArakelovGeometry.AdelicStructure.ParameterSpaceExtension
