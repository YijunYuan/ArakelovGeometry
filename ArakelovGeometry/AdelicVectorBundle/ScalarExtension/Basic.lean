/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basic
public import ArakelovGeometry.Analysis.ScalarExtension.Basic
import Mathlib.CategoryTheory.Category.Init

/-!
# Scalar extension of norm families

Completion and tensor-product identifications transport the local projective and
injective scalar-extension norms to fibres over an algebraic extension of the
adelic curve. `NormFamily.scalarExtension` uses the injective construction at
non-Archimedean places and the projective construction at Archimedean places.

This module constructs the norm families and proves their fibrewise properties.
Measurability, domination and the associated adelic-bundle constructors are proved
in the corresponding scalar-extension modules under their stated hypotheses.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u v w wE

variable {K : Type u} [Field K] {L : Type w} [Field L] [Algebra K L]
  (E : Type wE) [AddCommGroup E] [Module K E]

/-- Both completed scalar extensions identify canonically with
`w.Completion ⊗[K] E`. -/
def completedScalarExtensionEquiv (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ)
    (h : w.under K = v) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq v w h
    w.Completion ⊗[L] (L ⊗[K] E) ≃ₗ[w.Completion]
      w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E) := by
  letI := AbsoluteValue.normedAlgebraCompletionOfEq v w h
  letI := AbsoluteValue.isScalarTower_completionOfEq v w h
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange K L w.Completion w.Completion E)
    ≪≫ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange
      K v.Completion w.Completion w.Completion E).symm

/-- Exact formula on decomposable vectors in the extended completed fibre. -/
@[simp]
theorem completedScalarExtensionEquiv_tmul (v : AbsoluteValue K ℝ)
    (w : AbsoluteValue L ℝ) (h : w.under K = v)
    (a : w.Completion) (b : L) (x : E) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq v w h
    completedScalarExtensionEquiv E v w h (a ⊗ₜ[L] (b ⊗ₜ[K] x)) =
      (algebraMap L w.Completion b * a) ⊗ₜ[v.Completion] ((1 : v.Completion) ⊗ₜ[K] x) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq v w h
  simp only [completedScalarExtensionEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, Algebra.smul_def]

/-- Exact inverse formula on decomposable vectors over the base completion. -/
@[simp]
theorem completedScalarExtensionEquiv_symm_tmul (v : AbsoluteValue K ℝ)
    (w : AbsoluteValue L ℝ) (h : w.under K = v)
    (a : w.Completion) (b : v.Completion) (x : E) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq v w h
    (completedScalarExtensionEquiv E v w h).symm (a ⊗ₜ[v.Completion] (b ⊗ₜ[K] x)) =
      (algebraMap v.Completion w.Completion b * a) ⊗ₜ[L] ((1 : L) ⊗ₜ[K] x) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq v w h
  simp only [completedScalarExtensionEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearEquiv.symm_symm, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, Algebra.smul_def]

/-- Completed-fibre scalar extension commutes with a successive extension.
Both paths use the canonical tensor reassociation and the canonical
completed-field embeddings. -/
theorem completedScalarExtensionEquiv_tower {M : Type*} [Field M]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) (u : AbsoluteValue M ℝ)
    (hvw : w.under K = v) (hwu : u.under L = w)
    (hvu : u.under K = v)
    (z : u.Completion ⊗[M] (M ⊗[L] (L ⊗[K] E))) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq v w hvw
    letI := AbsoluteValue.normedAlgebraCompletionOfEq w u hwu
    letI := AbsoluteValue.normedAlgebraCompletionOfEq v u hvu
    letI := AbsoluteValue.isScalarTower_completionOfEq_tower v w u hvw hwu hvu
    TensorProduct.AlgebraTensorModule.cancelBaseChange
        v.Completion w.Completion u.Completion u.Completion (v.Completion ⊗[K] E)
      (LinearEquiv.baseChange w.Completion u.Completion _ _
        (completedScalarExtensionEquiv E v w hvw)
        (completedScalarExtensionEquiv (L ⊗[K] E) w u hwu z)) =
      completedScalarExtensionEquiv E v u hvu
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E).toLinearMap.baseChange
          u.Completion z) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq v w hvw
  let := AbsoluteValue.normedAlgebraCompletionOfEq w u hwu
  let := AbsoluteValue.normedAlgebraCompletionOfEq v u hvu
  let := AbsoluteValue.isScalarTower_completionOfEq_tower v w u hvw hwu hvu
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simp only [map_add, hz, ht]
  | tmul a y =>
    induction y using TensorProduct.inductionOn with
    | add y t hy ht => simp only [TensorProduct.tmul_add, map_add, hy, ht]
    | tmul b t =>
      induction t using TensorProduct.inductionOn with
      | add t s ht hs => simp only [TensorProduct.tmul_add, map_add, ht, hs]
      | tmul c x =>
        simp only [completedScalarExtensionEquiv_tmul, LinearEquiv.baseChange_tmul,
          LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
          Algebra.smul_def, mul_one, map_mul,
          AbsoluteValue.algebraMap_normedAlgebraCompletionOfEq_coe, mul_assoc]

namespace NormFamily

variable {E}
variable {S : AdelicStructure.{u, v} K} [FiniteDimensional K E]
  (ξ : NormFamily S E)

/-- Projective extension of a fibre norm, transported to the actual fibre
over an extending place. -/
def projectiveScalarExtensionSeminorm (x : AdelicStructure.ParameterSpaceExtension S L) :
    Seminorm x.abv.Completion (x.abv.Completion ⊗[L] (L ⊗[K] E)) := by
  letI := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  letI := ξ.fibreNormedAddCommGroup x.base
  letI := ξ.fibreNormedSpace x.base
  exact scalarExtensionProjectiveSeminorm.comp
    (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).toLinearMap

/-- Injective extension of a fibre norm, using exactly the rational dual
evaluations in the local scalar-extension construction. -/
def injectiveScalarExtensionSeminorm (x : AdelicStructure.ParameterSpaceExtension S L) :
    Seminorm x.abv.Completion (x.abv.Completion ⊗[L] (L ⊗[K] E)) := by
  letI := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  letI := ξ.fibreNormedAddCommGroup x.base
  letI := ξ.fibreNormedSpace x.base
  exact scalarExtensionInjectiveSeminorm.comp
    (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).toLinearMap

/-- The transported projective scalar-extension seminorm separates zero. -/
theorem projectiveScalarExtensionSeminorm_eq_zero_iff
    (x : AdelicStructure.ParameterSpaceExtension S L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    ξ.projectiveScalarExtensionSeminorm x z = 0 ↔ z = 0 := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  change scalarExtensionProjectiveSeminorm
    (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq z) = 0 ↔ _
  rw [scalarExtensionProjectiveSeminorm_eq_zero_iff, LinearEquiv.map_eq_zero_iff]

/-- The transported injective scalar-extension seminorm separates zero. -/
theorem injectiveScalarExtensionSeminorm_eq_zero_iff
    (x : AdelicStructure.ParameterSpaceExtension S L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    ξ.injectiveScalarExtensionSeminorm x z = 0 ↔ z = 0 := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  change scalarExtensionInjectiveSeminorm
    (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq z) = 0 ↔ _
  rw [scalarExtensionInjectiveSeminorm_eq_zero_iff, LinearEquiv.map_eq_zero_iff]

variable [Algebra.IsAlgebraic K L]

/-- Projective scalar extension at all places of the actual algebraically
extended adelic curve. -/
def projectiveScalarExtension : NormFamily (S.algebraicExtension L) (L ⊗[K] E) where
  norm := ξ.projectiveScalarExtensionSeminorm
  norm_eq_zero_iff := ξ.projectiveScalarExtensionSeminorm_eq_zero_iff

/-- Injective scalar extension at all places of the actual algebraically
extended adelic curve. -/
def injectiveScalarExtension : NormFamily (S.algebraicExtension L) (L ⊗[K] E) where
  norm := ξ.injectiveScalarExtensionSeminorm
  norm_eq_zero_iff := ξ.injectiveScalarExtensionSeminorm_eq_zero_iff

/-- The source's scalar-extension norm family uses the injective construction
at non-Archimedean places and the projective construction otherwise. -/
def scalarExtension : NormFamily (S.algebraicExtension L) (L ⊗[K] E) := by
  classical
  exact {
    norm := fun x ↦ if x.base ∈ S.Ωfin then
      ξ.injectiveScalarExtensionSeminorm x else ξ.projectiveScalarExtensionSeminorm x
    norm_eq_zero_iff := fun x z ↦ by
      change AdelicStructure.ParameterSpaceExtension S L at x
      change x.abv.Completion ⊗[L] (L ⊗[K] E) at z
      change (if x.base ∈ S.Ωfin then ξ.injectiveScalarExtensionSeminorm x else
        ξ.projectiveScalarExtensionSeminorm x) z = 0 ↔ z = 0
      by_cases hx : x.base ∈ S.Ωfin
      · rw [ite_eq_left hx]
        exact ξ.injectiveScalarExtensionSeminorm_eq_zero_iff x z
      · rw [ite_eq_right hx]
        exact ξ.projectiveScalarExtensionSeminorm_eq_zero_iff x z }

/-- Exact non-Archimedean branch of scalar extension. -/
@[simp]
theorem scalarExtension_norm_of_mem_Ωfin (x : AdelicStructure.ParameterSpaceExtension S L)
    (hx : x.base ∈ S.Ωfin) (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    (ξ.scalarExtension (L := L)).norm x z =
      (ξ.injectiveScalarExtension (L := L)).norm x z := by
  simp [scalarExtension, injectiveScalarExtension, hx]

/-- Exact Archimedean branch of scalar extension. -/
@[simp]
theorem scalarExtension_norm_of_not_mem_Ωfin (x : AdelicStructure.ParameterSpaceExtension S L)
    (hx : x.base ∉ S.Ωfin) (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    (ξ.scalarExtension (L := L)).norm x z =
      (ξ.projectiveScalarExtension (L := L)).norm x z := by
  simp [scalarExtension, projectiveScalarExtension, hx]

/-- Every injectively extended family is ultrametric at the non-Archimedean
places, regardless of ultrametricity of the original family. -/
theorem injectiveScalarExtension_isUltrametric :
    (ξ.injectiveScalarExtension (L := L)).IsUltrametric := by
  intro x hx z t
  change AdelicStructure.ParameterSpaceExtension S L at x
  change x.abv.Completion ⊗[L] (L ⊗[K] E) at z t
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  have hL (a b : x.abv.Completion) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
    refine UniformSpace.Completion.induction_on₂ a b ?_ ?_
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · intro c d
      simpa only [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe]
        using (show ‖c + d‖ ≤ max ‖c‖ ‖d‖ from hx c.ofAbs d.ofAbs)
  change scalarExtensionInjectiveSeminorm
    (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq (z + t)) ≤
      max (scalarExtensionInjectiveSeminorm
        (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq z))
        (scalarExtensionInjectiveSeminorm
          (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq t))
  rw [map_add]
  exact scalarExtensionInjectiveSeminorm_add_le_max hL _ _

/-- The source's scalar extension is always ultrametric at finite places. -/
theorem scalarExtension_isUltrametric :
    (ξ.scalarExtension (L := L)).IsUltrametric := by
  intro x hx z t
  change AdelicStructure.ParameterSpaceExtension S L at x
  change x.abv.Completion ⊗[L] (L ⊗[K] E) at z t
  have hbase := (AdelicStructure.mem_Ωfin_algebraicExtension_iff x).mp hx
  change (ξ.scalarExtension (L := L)).norm x (z + t) ≤
    max ((ξ.scalarExtension (L := L)).norm x z) ((ξ.scalarExtension (L := L)).norm x t)
  rw [scalarExtension_norm_of_mem_Ωfin ξ x hbase (z + t),
    scalarExtension_norm_of_mem_Ωfin ξ x hbase z,
    scalarExtension_norm_of_mem_Ωfin ξ x hbase t]
  exact ξ.injectiveScalarExtension_isUltrametric x hx z t

/-- The transported projective norm is the source's infimum over finite sums
in the scalar extension of the original completed fibre. -/
theorem projectiveScalarExtension_norm_eq_sInf
    (x : AdelicStructure.ParameterSpaceExtension S L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    (ξ.projectiveScalarExtension (L := L)).norm x z =
      sInf {c : ℝ | ∃ p : List (x.abv.Completion × ((S.ϕ x.base).Completion ⊗[K] E)),
        (p.map fun q ↦ q.1 ⊗ₜ[(S.ϕ x.base).Completion] q.2).sum =
          completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq z ∧
        (p.map fun q ↦ ‖q.1‖ * ξ.norm x.base q.2).sum = c} := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  exact scalarExtensionProjectiveSeminorm_eq_sInf _

/-- The transported injective norm is the source's supremum over nonzero
linear functionals on the original completed fibre. -/
theorem injectiveScalarExtension_norm_eq_sSup
    (x : AdelicStructure.ParameterSpaceExtension S L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    letI := ξ.fibreNormedAddCommGroup x.base
    letI := ξ.fibreNormedSpace x.base
    (ξ.injectiveScalarExtension (L := L)).norm x z =
      sSup {c : ℝ | ∃ f : ((S.ϕ x.base).Completion ⊗[K] E) →ₗ[(S.ϕ x.base).Completion]
          (S.ϕ x.base).Completion, f ≠ 0 ∧
        ‖scalarExtensionDualEval f
          (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq z)‖ /
          linearMapOperatorSeminorm f = c} := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  exact scalarExtensionInjectiveSeminorm_eq_sSup_nonzero _

/-- Injective scalar extension is bounded by projective scalar extension on
every actual completed fibre. -/
theorem injectiveScalarExtension_norm_le_projectiveScalarExtension_norm
    (x : AdelicStructure.ParameterSpaceExtension S L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    (ξ.injectiveScalarExtension (L := L)).norm x z ≤
      (ξ.projectiveScalarExtension (L := L)).norm x z := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  exact scalarExtensionInjectiveSeminorm_le_projective _

/-- Original rational vectors have no larger norm after scalar extension. -/
theorem scalarExtension_norm_one_tmul_le (x : AdelicStructure.ParameterSpaceExtension S L)
    (e : E) :
    (ξ.scalarExtension (L := L)).norm x
      ((1 : x.abv.Completion) ⊗ₜ[L] ((1 : L) ⊗ₜ[K] e)) ≤
      ξ.norm x.base ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] e) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  have hπ : (ξ.projectiveScalarExtension (L := L)).norm x
      ((1 : x.abv.Completion) ⊗ₜ[L] ((1 : L) ⊗ₜ[K] e)) ≤
      ξ.norm x.base ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] e) := by
    have ht := completedScalarExtensionEquiv_tmul E (S.ϕ x.base) x.abv x.restrict_eq
      (1 : x.abv.Completion) (1 : L) e
    simp only [map_one, one_mul] at ht
    exact (congrArg scalarExtensionProjectiveSeminorm ht).trans_le
      (scalarExtensionProjectiveSeminorm_one_tmul_le _)
  by_cases hx : x.base ∈ S.Ωfin
  · exact (scalarExtension_norm_of_mem_Ωfin ξ x hx _).trans_le
      ((ξ.injectiveScalarExtension_norm_le_projectiveScalarExtension_norm x _).trans hπ)
  · exact (scalarExtension_norm_of_not_mem_Ωfin ξ x hx _).trans_le hπ

/-- Scalar extension retains the zero-space convention on all completed
fibres. -/
theorem scalarExtension_norm_eq_zero_of_subsingleton [Subsingleton E]
    (x : AdelicStructure.ParameterSpaceExtension S L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    (ξ.scalarExtension (L := L)).norm x z = 0 :=
  (ξ.scalarExtension (L := L)).norm_eq_zero_of_subsingleton x z

end NormFamily

end

end ArakelovGeometry
