/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicStructure.TrivialPlace
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Semistability

import ArakelovGeometry.AdelicVectorBundle.Construction.Rescaling
import ArakelovGeometry.AdelicVectorBundle.Determinant.HermitianBasis
import ArakelovGeometry.AdelicVectorBundle.Slope.Quotient
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Arbitrary actual norms at the single trivial place

Norms are transported to the genuine completed tensor fibre. Every norm
family at the mass-one point is measurable, dual-measurable and dominated,
without imposing ultrametricity.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u w

variable {K : Type u} [Field K] {E : Type w} [AddCommGroup E] [Module K E]

namespace NormFamily

open AdelicStructure

open Classical in
/-- Transport any separating trivial-valued seminorm to the genuine
completed tensor fibre at the mass-one place. Ultrametricity is not assumed. -/
def ofTrivialNorm (p : Seminorm (WithAbs (AbsoluteValue.trivial : AbsoluteValue K ℝ)) E)
    (hp : ∀ x, p x = 0 ↔ x = 0) : NormFamily (singleTrivialPlace K) E where
  norm _ := by
    change Seminorm (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
      ((AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion ⊗[K] E)
    exact Seminorm.of (fun z ↦ p (trivialCompletedTensorEquiv K E z))
      (by
        intro x y
        rw [map_add]
        exact map_add_le_add p _ _)
      (fun a z ↦ by
        rw [trivialCompletedTensorEquiv_smul]
        change p (WithAbs.toAbs (AbsoluteValue.trivial : AbsoluteValue K ℝ)
          (trivialCompletionAlgEquiv K a) • trivialCompletedTensorEquiv K E z) = _
        rw [map_smul_eq_mul, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_toAbs,
          ← norm_trivialCompletion K a])
  norm_eq_zero_iff _ z := by
    change (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion ⊗[K] E at z
    change p (trivialCompletedTensorEquiv K E z) = 0 ↔ z = 0
    rw [hp, LinearEquiv.map_eq_zero_iff]

open Classical in
/-- The exact norm formula holds on every actual completed vector. -/
theorem ofTrivialNorm_norm
    (p : Seminorm (WithAbs (AbsoluteValue.trivial : AbsoluteValue K ℝ)) E)
    (hp : ∀ x, p x = 0 ↔ x = 0) (ω : (singleTrivialPlace K).Ω)
    (z : ((singleTrivialPlace K).ϕ ω).Completion ⊗[K] E) :
    (ofTrivialNorm p hp).norm ω z = p (trivialCompletedTensorEquiv K E z) := rfl

open Classical in
@[simp]
theorem ofTrivialNorm_norm_rational
    (p : Seminorm (WithAbs (AbsoluteValue.trivial : AbsoluteValue K ℝ)) E)
    (hp : ∀ x, p x = 0 ↔ x = 0) (ω : (singleTrivialPlace K).Ω) (x : E) :
    (ofTrivialNorm p hp).norm ω ((1 : ((singleTrivialPlace K).ϕ ω).Completion) ⊗ₜ[K] x) =
      p x := by
  change p (trivialCompletedTensorEquiv K E
    ((1 : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion) ⊗ₜ[K] x)) = p x
  rw [trivialCompletedTensorEquiv_one_tmul]

/-- Every actual norm family at the mass-one point is measurable. -/
theorem isMeasurable_singleTrivialPlace (ξ : NormFamily (singleTrivialPlace K) E) :
    ξ.IsMeasurable := ξ.isMeasurable_of_discrete

/-- Every real rational logarithmic norm is integrable at the mass-one point. -/
theorem integrable_logNorm_singleTrivialPlace (ξ : NormFamily (singleTrivialPlace K) E)
    (x : E) : Integrable (ξ.logNorm x) (singleTrivialPlace K).v := by
  apply integrable_dirac
  exact enorm_lt_top

/-- Actual upper domination at the one-point place uses the genuine
rational log norm itself as its integrable envelope. -/
theorem isUpperDominated_singleTrivialPlace (ξ : NormFamily (singleTrivialPlace K) E) :
    ξ.IsUpperDominated := by
  constructor
  intro x _
  exact ⟨ξ.logNorm x, ξ.integrable_logNorm_singleTrivialPlace x,
    Filter.Eventually.of_forall fun _ ↦ le_rfl⟩

open Classical in
/-- Extract the original rational norm from the actual completed fibre
through the canonical inverse tensor equivalence. -/
def trivialSeminorm (ξ : NormFamily (singleTrivialPlace K) E) :
    Seminorm (WithAbs (AbsoluteValue.trivial : AbsoluteValue K ℝ)) E := by
  let q : Seminorm (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
    ((AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion ⊗[K] E) := ξ.norm PUnit.unit
  exact Seminorm.of (fun x ↦ q ((trivialCompletedTensorEquiv K E).symm x))
    (by
      intro x y
      rw [map_add]
      exact map_add_le_add q _ _)
    (by
      intro a x
      have he : (trivialCompletedTensorEquiv K E).symm (a • x) =
          algebraMap K (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion a.ofAbs •
            (trivialCompletedTensorEquiv K E).symm x := by
        apply (trivialCompletedTensorEquiv K E).injective
        rw [trivialCompletedTensorEquiv_smul, LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply, trivialCompletionAlgEquiv_algebraMap]
        rfl
      rw [he, map_smul_eq_mul, UniformSpace.Completion.algebraMap_def,
        UniformSpace.Completion.norm_coe, WithAbs.algebraMap_right_apply,
        Algebra.algebraMap_self_apply, WithAbs.toAbs_ofAbs])

open Classical in
@[simp]
theorem trivialSeminorm_apply (ξ : NormFamily (singleTrivialPlace K) E) (x : E) :
    ξ.trivialSeminorm x = ξ.norm PUnit.unit
      ((1 : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion) ⊗ₜ[K] x) := by
  change ξ.norm PUnit.unit ((trivialCompletedTensorEquiv K E).symm x) = _
  congr 1

open Classical in
theorem trivialSeminorm_eq_zero_iff (ξ : NormFamily (singleTrivialPlace K) E) (x : E) :
    ξ.trivialSeminorm x = 0 ↔ x = 0 := by
  change ξ.norm PUnit.unit ((trivialCompletedTensorEquiv K E).symm x) = 0 ↔ x = 0
  exact (ξ.norm_eq_zero_iff PUnit.unit _).trans
    ((trivialCompletedTensorEquiv K E).symm.map_eq_zero_iff)

open Classical in
@[simp]
theorem trivialSeminorm_ofTrivialNorm
    (p : Seminorm (WithAbs (AbsoluteValue.trivial : AbsoluteValue K ℝ)) E)
    (hp : ∀ x, p x = 0 ↔ x = 0) : (ofTrivialNorm p hp).trivialSeminorm = p := by
  ext x
  change p (trivialCompletedTensorEquiv K E
    ((trivialCompletedTensorEquiv K E).symm x)) = p x
  exact congrArg p ((trivialCompletedTensorEquiv K E).apply_symm_apply x)

open Classical in
@[simp]
theorem ofTrivialNorm_trivialSeminorm (ξ : NormFamily (singleTrivialPlace K) E) :
    ofTrivialNorm ξ.trivialSeminorm ξ.trivialSeminorm_eq_zero_iff = ξ := by
  ext ω z
  cases ω
  change (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion ⊗[K] E at z
  change ξ.norm PUnit.unit ((trivialCompletedTensorEquiv K E).symm
    (trivialCompletedTensorEquiv K E z)) = ξ.norm PUnit.unit z
  exact congrArg (ξ.norm PUnit.unit) ((trivialCompletedTensorEquiv K E).symm_apply_apply z)

open Classical in
/-- Ultrametricity of the transported actual family is exactly the
ultrametric inequality on its original rational norm. -/
theorem ofTrivialNorm_isUltrametric_iff
    (p : Seminorm (WithAbs (AbsoluteValue.trivial : AbsoluteValue K ℝ)) E)
    (hp : ∀ x, p x = 0 ↔ x = 0) :
    (ofTrivialNorm p hp).IsUltrametric ↔ ∀ x y, p (x + y) ≤ max (p x) (p y) := by
  constructor
  · intro h x y
    have hω : (PUnit.unit : (singleTrivialPlace K).Ω) ∈ (singleTrivialPlace K).Ωfin := by
      rw [singleTrivialPlace_Ωfin]
      exact Set.mem_univ _
    have he := h PUnit.unit hω
      ((1 : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion) ⊗ₜ[K] x)
      ((1 : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion) ⊗ₜ[K] y)
    change p (trivialCompletedTensorEquiv K E
      (((1 : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion) ⊗ₜ[K] x) +
        ((1 : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion) ⊗ₜ[K] y))) ≤
      max (p (trivialCompletedTensorEquiv K E
        ((1 : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion) ⊗ₜ[K] x)))
        (p (trivialCompletedTensorEquiv K E
          ((1 : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion) ⊗ₜ[K] y))) at he
    simpa only [map_add, trivialCompletedTensorEquiv_one_tmul] using he
  · intro h
    constructor
    intro ω _ z t
    change (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion ⊗[K] E at z t
    change p (trivialCompletedTensorEquiv K E (z + t)) ≤
      max (p (trivialCompletedTensorEquiv K E z)) (p (trivialCompletedTensorEquiv K E t))
    simpa only [map_add] using h (trivialCompletedTensorEquiv K E z)
      (trivialCompletedTensorEquiv K E t)

variable [FiniteDimensional K E]

/-- Every actual norm family and its actual dual are dominated, without
ultrametricity or Hermitianity. -/
theorem isDominated_singleTrivialPlace (ξ : NormFamily (singleTrivialPlace K) E) :
    ξ.IsDominated :=
  ⟨ξ.isUpperDominated_singleTrivialPlace, ξ.dual.isUpperDominated_singleTrivialPlace⟩

end NormFamily

namespace AdelicVectorBundle

open AdelicStructure

variable [FiniteDimensional K E]

/-- An arbitrary actual norm family at the single trivial place is
adelic, including its actual completed dual measurability. -/
abbrev ofSingleTrivialPlace (ξ : NormFamily (singleTrivialPlace K) E) :
    AdelicVectorBundle (singleTrivialPlace K) where
  carrier := E
  toNormFamily := ξ
  toIsAdelic := {
    isMeasurable := ξ.isMeasurable_singleTrivialPlace
    dual_isMeasurable := ξ.dual.isMeasurable_singleTrivialPlace
    isDominated := ξ.isDominated_singleTrivialPlace
  }

@[simp]
theorem ofSingleTrivialPlace_toNormFamily (ξ : NormFamily (singleTrivialPlace K) E) :
    (ofSingleTrivialPlace ξ).toNormFamily = ξ := rfl

open Classical in
/-- Every finite-dimensional normed space over a trivially valued field
is an actual adelic bundle on the mass-one curve, without ultrametricity. -/
abbrev ofTrivialNorm (p : Seminorm (WithAbs (AbsoluteValue.trivial : AbsoluteValue K ℝ)) E)
    (hp : ∀ x, p x = 0 ↔ x = 0) : AdelicVectorBundle (singleTrivialPlace K) :=
  ofSingleTrivialPlace (NormFamily.ofTrivialNorm p hp)

open Classical in
@[simp]
theorem ofTrivialNorm_toNormFamily
    (p : Seminorm (WithAbs (AbsoluteValue.trivial : AbsoluteValue K ℝ)) E)
    (hp : ∀ x, p x = 0 ↔ x = 0) :
    (ofTrivialNorm p hp).toNormFamily = NormFamily.ofTrivialNorm p hp := rfl

end AdelicVectorBundle

namespace NormFamily

open AdelicStructure

open Classical in
/-- A constant rational norm is constant on every nonzero actual
completed vector, through the canonical trivial tensor equivalence. -/
theorem norm_eq_const_of_trivialSeminorm_eq_const
    (ξ : NormFamily (singleTrivialPlace K) E) {c : ℝ}
    (h : ∀ x, x ≠ 0 → ξ.trivialSeminorm x = c)
    (ω : (singleTrivialPlace K).Ω)
    (z : ((singleTrivialPlace K).ϕ ω).Completion ⊗[K] E) (hz : z ≠ 0) :
    ξ.norm ω z = c := by
  cases ω
  change (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion ⊗[K] E at z
  have ht : trivialCompletedTensorEquiv K E z ≠ 0 :=
    (trivialCompletedTensorEquiv K E).map_eq_zero_iff.not.mpr hz
  have hc := h _ ht
  change ξ.norm PUnit.unit ((trivialCompletedTensorEquiv K E).symm
    (trivialCompletedTensorEquiv K E z)) = c at hc
  simpa only [LinearEquiv.symm_apply_apply] using hc

open Classical in
/-- Constant nonzero norms satisfy the ultrametric inequality on the
whole actual completed fibre. -/
theorem isUltrametric_of_trivialSeminorm_eq_const
    (ξ : NormFamily (singleTrivialPlace K) E) {c : ℝ}
    (h : ∀ x, x ≠ 0 → ξ.trivialSeminorm x = c) : ξ.IsUltrametric := by
  constructor
  intro ω _ x y
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  by_cases hs : x + y = 0
  · rw [hs, map_zero]
    exact le_max_of_le_left (ξ.norm_nonneg ω x)
  rw [ξ.norm_eq_const_of_trivialSeminorm_eq_const h ω _ hs,
    ξ.norm_eq_const_of_trivialSeminorm_eq_const h ω _ hx,
    ξ.norm_eq_const_of_trivialSeminorm_eq_const h ω _ hy, max_self]

end NormFamily

namespace AdelicVectorBundle

open AdelicStructure

variable [FiniteDimensional K E]

open Classical in
/-- The unit constant norm has genuine determinant volume one and
therefore actual degree zero, including the empty determinant wedge. -/
theorem degree_eq_zero_of_trivialSeminorm_eq_one
    (V : AdelicVectorBundle (singleTrivialPlace K))
    [hS : (singleTrivialPlace K).HasMeasurableBase]
    [hN : (singleTrivialPlace K).IsArchimedeanNormalized]
    (h : ∀ x, x ≠ 0 → V.toNormFamily.trivialSeminorm x = 1) :
    V.degree = 0 := by
  let C := (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
  let b := Module.finBasis K V
  let B := b.baseChange C
  let q : Seminorm C (C ⊗[K] V) := V.toNormFamily.norm PUnit.unit
  let qd : Seminorm C (C ⊗[K] (⋀[K]^(Module.finrank K V) V)) :=
    V.toNormFamily.determinant.norm PUnit.unit
  have hH : V.toNormFamily.IsHermitian := by
    refine ⟨V.toNormFamily.isUltrametric_of_trivialSeminorm_eq_const h, ?_⟩
    intro ω hω
    simp only [singleTrivialPlace_Ωinf, Set.mem_empty_iff_false] at hω
  have hb : ∀ i, V.toNormFamily.norm PUnit.unit (B i) ≤ 1 := by
    intro i
    exact (V.toNormFamily.norm_eq_const_of_trivialSeminorm_eq_const h _ _
      (B.ne_zero i)).le
  have hf : ∀ i, V.toNormFamily.dual.norm PUnit.unit
      ((dualBaseChangeEquiv K C V).symm (B.coord i)) ≤ 1 := by
    intro i
    apply V.toNormFamily.dual_norm_le PUnit.unit _ zero_le_one
    intro x
    change C ⊗[K] V at x
    change ‖(dualBaseChangeEquiv K C V
      ((dualBaseChangeEquiv K C V).symm (B.coord i))) x‖ ≤ 1 * q x
    rw [LinearEquiv.apply_symm_apply]
    by_cases hx : x = 0
    · simp [hx]
    have hq : q x = 1 :=
      V.toNormFamily.norm_eq_const_of_trivialSeminorm_eq_const h _ _ hx
    rw [hq, one_mul]
    change ‖(B.coord i) x‖ ≤ 1
    rw [norm_trivialCompletion K]
    by_cases ha : trivialCompletionAlgEquiv K (B.coord i x) = 0
    · rw [ha, map_zero]
      exact zero_le_one
    · simp only [AbsoluteValue.trivial_apply ha, le_refl]
  have hw := hH.determinant_norm_completedBasis_eq_one V.toNormFamily PUnit.unit B hb hf
  change qd ((exteriorBaseChangeEquiv K C V _).symm
    (_root_.exteriorPower.ιMulti C _ B)) = 1 at hw
  have he : (exteriorBaseChangeEquiv K C V _).symm
      (_root_.exteriorPower.ιMulti C _ B) =
      (1 : C) ⊗ₜ[K] _root_.exteriorPower.ιMulti K _ b := by
    have hB : (B : Fin (Module.finrank K V) → C ⊗[K] V) =
        (fun i ↦ (1 : C) ⊗ₜ[K] b i) := funext (b.baseChange_apply C)
    rw [hB]
    simpa only [Finset.prod_const_one] using
      exteriorBaseChangeEquiv_symm_ιMulti_tmul K C V _ (fun _ ↦ (1 : C)) b
  rw [he] at hw
  have hn : _root_.exteriorPower.ιMulti K (Module.finrank K V) b ≠ 0 := by
    intro hz
    rw [hz, TensorProduct.tmul_zero,
      show qd 0 = 0 from V.toNormFamily.determinant.norm_zero PUnit.unit] at hw
    exact zero_ne_one hw
  rw [V.degree_eq_neg_integral ⟨_, hn⟩, integral_singleTrivialPlace]
  change -Real.log (qd ((1 : C) ⊗ₜ[K] _root_.exteriorPower.ιMulti K _ b)) = 0
  rw [hw, Real.log_one, neg_zero]

open Classical in
/-- Rescaling the genuine constant norm gives its actual determinant
degree, in every rank. -/
theorem degree_eq_neg_finrank_mul_log_of_trivialSeminorm_eq_const
    (V : AdelicVectorBundle (singleTrivialPlace K))
    [hS : (singleTrivialPlace K).HasMeasurableBase]
    [hN : (singleTrivialPlace K).IsArchimedeanNormalized]
    {c : ℝ} (hc : 0 < c)
    (h : ∀ x, x ≠ 0 → V.toNormFamily.trivialSeminorm x = c) :
    V.degree = -(Module.finrank K V : ℝ) * Real.log c := by
  let φ : (singleTrivialPlace K).Ω → ℝ := fun _ ↦ -Real.log c
  have hm : Measurable φ := measurable_const
  have hi : Integrable φ (singleTrivialPlace K).v := integrable_const _
  have hu : ∀ x, x ≠ 0 →
      (V.scaleExp φ hm hi).toNormFamily.trivialSeminorm x = 1 := by
    intro x hx
    rw [NormFamily.trivialSeminorm_apply]
    change Real.exp (-Real.log c) * V.toNormFamily.norm PUnit.unit
      ((1 : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion) ⊗ₜ[K] x) = 1
    rw [← NormFamily.trivialSeminorm_apply, h x hx, Real.exp_neg,
      Real.exp_log hc, inv_mul_cancel₀ hc.ne']
  have he := (V.scaleExp φ hm hi).degree_eq_zero_of_trivialSeminorm_eq_one hu
  rw [V.degree_scaleExp φ hm hi, integral_singleTrivialPlace] at he
  dsimp only [φ] at he
  linarith

end AdelicVectorBundle

namespace NormFamily

open AdelicStructure

open Classical in
/-- Every lift of a nonzero quotient vector has the same constant norm;
the actual quotient infimum therefore equals that constant. -/
theorem trivialSeminorm_pushforward_eq_const
    [FiniteDimensional K E]
    (ξ : NormFamily (singleTrivialPlace K) E) {c : ℝ}
    (h : ∀ x, x ≠ 0 → ξ.trivialSeminorm x = c)
    {G : Type*} [AddCommGroup G] [Module K G]
    (π : E →ₗ[K] G) (hπ : Function.Surjective π)
    (y : G) (hy : y ≠ 0) : (ξ.pushforward π hπ).trivialSeminorm y = c := by
  let C := (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
  let z : C ⊗[K] G := (1 : C) ⊗ₜ[K] y
  let q : Seminorm C (C ⊗[K] E) := ξ.norm PUnit.unit
  let qG : Seminorm C (C ⊗[K] G) := (ξ.pushforward π hπ).norm PUnit.unit
  have hz : z ≠ 0 := by
    intro hz
    have he := congrArg (trivialCompletedTensorEquiv K G) hz
    change trivialCompletedTensorEquiv K G ((1 : C) ⊗ₜ[K] y) =
      trivialCompletedTensorEquiv K G 0 at he
    rw [trivialCompletedTensorEquiv_one_tmul, map_zero] at he
    exact hy he
  change qG z = c
  apply le_antisymm
  · obtain ⟨x, hx⟩ := LinearMap.baseChange_surjective C hπ z
    have hn : x ≠ 0 := by
      intro hx0
      exact hz (by simpa only [hx0, map_zero] using hx.symm)
    calc
      _ ≤ q x := by
        have hl := ξ.pushforward_norm_le π hπ PUnit.unit x
        change qG (π.baseChange C x) ≤ q x at hl
        rw [hx] at hl
        exact hl
      _ = c := ξ.norm_eq_const_of_trivialSeminorm_eq_const h _ _ hn
  · apply (ξ.le_quotientSeminorm_iff π hπ PUnit.unit z c).mpr
    intro x hx
    change C ⊗[K] E at x
    change π.baseChange C x = z at hx
    have hn : x ≠ 0 := by
      intro hx0
      exact hz (by simpa only [hx0, map_zero] using hx.symm)
    exact (ξ.norm_eq_const_of_trivialSeminorm_eq_const h _ _ hn).ge

open Classical in
/-- Canonical restriction preserves the constant rational norm without
any supplied completed-isometry hypothesis. -/
theorem trivialSeminorm_restrict_eq_const
    (ξ : NormFamily (singleTrivialPlace K) E) {c : ℝ}
    (h : ∀ x, x ≠ 0 → ξ.trivialSeminorm x = c)
    (U : Submodule K E) (x : U) (hx : x ≠ 0) :
    (ξ.restrict U).trivialSeminorm x = c := by
  have hn : (x : E) ≠ 0 := fun hz ↦ hx (Subtype.ext hz)
  have he := h x hn
  rw [trivialSeminorm_apply] at he ⊢
  let C := (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
  let q : Seminorm C (C ⊗[K] E) := ξ.norm PUnit.unit
  change q ((1 : C) ⊗ₜ[K] (x : E)) = c at he
  change q
    (U.subtype.baseChange (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
      ((1 : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion) ⊗ₜ[K] x)) = c
  rw [LinearMap.baseChange_tmul]
  exact he

end NormFamily

namespace AdelicVectorBundle

open AdelicStructure

variable [FiniteDimensional K E]
  (V : AdelicVectorBundle.{w} (singleTrivialPlace K))
  [hS : (singleTrivialPlace K).HasMeasurableBase]
  [hN : (singleTrivialPlace K).IsArchimedeanNormalized]

open Classical in
/-- The positive-rank ordinary mean of an actual constant norm is its
negative logarithm. Rank zero keeps the source zero-mean convention. -/
theorem slope_eq_neg_log_of_trivialSeminorm_eq_const
    {c : ℝ} (hc : 0 < c)
    (h : ∀ x, x ≠ 0 → V.toNormFamily.trivialSeminorm x = c)
    (hr : 0 < Module.finrank K V) : V.slope = -Real.log c := by
  have hn : (Module.finrank K V : ℝ) ≠ 0 := (Nat.cast_pos.mpr hr).ne'
  rw [slope, V.degree_eq_neg_finrank_mul_log_of_trivialSeminorm_eq_const hc h]
  apply (div_eq_iff hn).mpr
  ring

open Classical in
/-- The actual infimum of quotient means evaluates to the constant
norm's negative logarithm, without assumed slope finiteness. -/
theorem minimalSlope_eq_neg_log_of_trivialSeminorm_eq_const
    {c : ℝ} (hc : 0 < c)
    (h : ∀ x, x ≠ 0 → V.toNormFamily.trivialSeminorm x = c)
    (hr : 0 < Module.finrank K V) :
    V.minimalSlope = (-Real.log c : ℝ) := by
  apply le_antisymm
  · have he := V.minimalSlope_le_slope hr
    rw [V.slope_eq_neg_log_of_trivialSeminorm_eq_const hc h hr] at he
    exact he
  · rw [V.minimalSlope_eq_iInf_slope_quotient]
    apply le_iInf
    intro U
    have hq : ∀ x, x ≠ 0 →
        (V.quotientOfMeasurableBase U.val).toNormFamily.trivialSeminorm x = c := by
      intro x hx
      exact V.toNormFamily.trivialSeminorm_pushforward_eq_const h
        U.val.mkQ U.val.mkQ_surjective x hx
    rw [(V.quotientOfMeasurableBase U.val).slope_eq_neg_log_of_trivialSeminorm_eq_const
      hc hq U.property]

open Classical in
/-- True general semistability of a positive-rank actual constant norm
follows from the minimum slope of every genuine restriction. -/
theorem isSemistable_of_trivialSeminorm_eq_const
    {c : ℝ} (hc : 0 < c)
    (h : ∀ x, x ≠ 0 → V.toNormFamily.trivialSeminorm x = c)
    (hr : 0 < Module.finrank K V) : V.IsSemistable := by
  apply (V.isSemistable_iff_minimalSlope_restrict_le hr).mpr
  intro U hU
  have hUr : 0 < Module.finrank K U :=
    Nat.pos_of_ne_zero (fun hz ↦ hU (Submodule.finrank_eq_zero.mp hz))
  have hu : ∀ x, x ≠ 0 →
      (V.restrictOfMeasurableBase U).toNormFamily.trivialSeminorm x = c := by
    intro x hx
    exact V.toNormFamily.trivialSeminorm_restrict_eq_const h U x hx
  rw [V.minimalSlope_eq_neg_log_of_trivialSeminorm_eq_const hc h hr,
    (V.restrictOfMeasurableBase U).minimalSlope_eq_neg_log_of_trivialSeminorm_eq_const
      hc hu hUr]

end AdelicVectorBundle

end

end ArakelovGeometry
