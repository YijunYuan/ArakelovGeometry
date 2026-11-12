/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Measurability.Hermitian
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Hermitian.Basic

import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicVectorBundle.Measurability.Archimedean
import ArakelovGeometry.AdelicVectorBundle.Measurability.Density.FiniteExtension
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.FiniteStage.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Measurable
import ArakelovGeometry.Analysis.Hermitian.ComplexPolarization
import Mathlib.CategoryTheory.Category.Init

/-!
# Measurability of actual Hermitian scalar-extension norms

The defining completed pairing expands into the original completed Hermitian
pairings. Compatible measurable embeddings retain both real and imaginary
Gram entries, and their real diagonal recovers the actual extended norm.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

universe u v w wE

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E)
  [hS : S.IsArchimedeanNormalized]
  [hL : (S.algebraicExtension L).IsArchimedeanNormalized]
  [hH : ξ.IsHermitian]

/-- The defining sesquilinear pairing of the existing Hermitian extension,
on its actual completed fibre. -/
def hermitianScalarExtensionArchInner (x : (S.algebraicExtension L).Ωinf)
    (z t : x.val.abv.Completion ⊗[L] (L ⊗[K] E)) : x.val.abv.Completion := by
  let := hS x.val.base ((scalarExtension_mem_Ωinf_iff x.val).mp x.property)
  let := IsRCLikeNormedField.rclike (S.ϕ x.val.base).Completion
  let : IsRCLikeNormedField x.val.abv.Completion := hL x.val x.property
  let := IsRCLikeNormedField.rclike x.val.abv.Completion
  let := AbsoluteValue.normedAlgebraCompletionOfEq
    (S.ϕ x.val.base) x.val.abv x.val.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.val.base
  let := ξ.fibreNormedSpace x.val.base
  let := ξ.fiberInnerProductSpace x.val.base ((scalarExtension_mem_Ωinf_iff x.val).mp x.property)
  let b := stdOrthonormalBasis (S.ϕ x.val.base).Completion
    ((S.ϕ x.val.base).Completion ⊗[K] E)
  let f := completedScalarExtensionEquiv E (S.ϕ x.val.base) x.val.abv x.val.restrict_eq
  exact (ArakelovGeometry.hermitianScalarExtensionCore b).inner (f z) (f t)

/-- The actual extended pairing is additive in its first variable. -/
theorem hermitianScalarExtensionArchInner_add_left (x : (S.algebraicExtension L).Ωinf)
    (z t q : x.val.abv.Completion ⊗[L] (L ⊗[K] E)) :
    hermitianScalarExtensionArchInner ξ x (z + t) q =
      hermitianScalarExtensionArchInner ξ x z q +
        hermitianScalarExtensionArchInner ξ x t q := by
  let : IsRCLikeNormedField x.val.abv.Completion := hL x.val x.property
  let := IsRCLikeNormedField.rclike x.val.abv.Completion
  simp only [hermitianScalarExtensionArchInner, map_add,
    InnerProductSpace.Core.inner_add_left]

/-- The actual extended pairing is additive in its second variable. -/
theorem hermitianScalarExtensionArchInner_add_right (x : (S.algebraicExtension L).Ωinf)
    (z t q : x.val.abv.Completion ⊗[L] (L ⊗[K] E)) :
    hermitianScalarExtensionArchInner ξ x z (t + q) =
      hermitianScalarExtensionArchInner ξ x z t +
        hermitianScalarExtensionArchInner ξ x z q := by
  let : IsRCLikeNormedField x.val.abv.Completion := hL x.val x.property
  let := IsRCLikeNormedField.rclike x.val.abv.Completion
  simp only [hermitianScalarExtensionArchInner, map_add,
    InnerProductSpace.Core.inner_add_right]

/-- Rational pure tensors have the exact original pairing with their
conjugate-first extending scalar factors. -/
theorem hermitianScalarExtensionArchInner_rational_tmul
    (x : (S.algebraicExtension L).Ωinf)
    (τ : x.val.abv.Completion →+* ℂ) (hτ : ∀ a, ‖τ a‖ = ‖a‖)
    (a c : L) (e f : E) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq
      (S.ϕ x.val.base) x.val.abv x.val.restrict_eq
    τ (hermitianScalarExtensionArchInner ξ x
      ((1 : x.val.abv.Completion) ⊗ₜ[L] (a ⊗ₜ[K] e))
      ((1 : x.val.abv.Completion) ⊗ₜ[L] (c ⊗ₜ[K] f))) =
      starRingEnd ℂ (τ (algebraMap L x.val.abv.Completion a)) *
        τ (algebraMap L x.val.abv.Completion c) *
        τ (algebraMap (S.ϕ x.val.base).Completion x.val.abv.Completion
          (ξ.archimedeanInner
            ⟨x.val.base, (scalarExtension_mem_Ωinf_iff x.val).mp x.property⟩
            ((1 : (S.ϕ x.val.base).Completion) ⊗ₜ[K] e)
            ((1 : (S.ϕ x.val.base).Completion) ⊗ₜ[K] f))) := by
  intro aVW
  let := aVW
  let := hS x.val.base ((scalarExtension_mem_Ωinf_iff x.val).mp x.property)
  let := IsRCLikeNormedField.rclike (S.ϕ x.val.base).Completion
  let : IsRCLikeNormedField x.val.abv.Completion := hL x.val x.property
  let := IsRCLikeNormedField.rclike x.val.abv.Completion
  let := AbsoluteValue.normedAlgebraCompletionOfEq
    (S.ϕ x.val.base) x.val.abv x.val.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.val.base
  let := ξ.fibreNormedSpace x.val.base
  let := ξ.fiberInnerProductSpace x.val.base ((scalarExtension_mem_Ωinf_iff x.val).mp x.property)
  simp only [hermitianScalarExtensionArchInner, completedScalarExtensionEquiv_tmul,
    mul_one, ArakelovGeometry.hermitianScalarExtensionCore_tmul, map_mul,
    complexEmbedding_map_conj τ hτ]
  rfl

/-- The real diagonal of the embedded defining pairing is exactly the
square of the existing Hermitian scalar-extension norm. -/
theorem hermitianScalarExtension_norm_sq_eq_re_archInner
    (x : (S.algebraicExtension L).Ωinf)
    (τ : x.val.abv.Completion →+* ℂ) (hτ : ∀ a, ‖τ a‖ = ‖a‖)
    (z : x.val.abv.Completion ⊗[L] (L ⊗[K] E)) :
    (hermitianScalarExtension ξ).norm x.val z ^ 2 =
      (τ (hermitianScalarExtensionArchInner ξ x z z)).re := by
  let := hS x.val.base ((scalarExtension_mem_Ωinf_iff x.val).mp x.property)
  let := IsRCLikeNormedField.rclike (S.ϕ x.val.base).Completion
  let : IsRCLikeNormedField x.val.abv.Completion := hL x.val x.property
  let := IsRCLikeNormedField.rclike x.val.abv.Completion
  let := AbsoluteValue.normedAlgebraCompletionOfEq
    (S.ϕ x.val.base) x.val.abv x.val.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.val.base
  let := ξ.fibreNormedSpace x.val.base
  let := ξ.fiberInnerProductSpace x.val.base ((scalarExtension_mem_Ωinf_iff x.val).mp x.property)
  rw [hermitianScalarExtension_norm_of_infinite ξ x.val x.property,
    complexEmbedding_re τ hτ]
  exact ArakelovGeometry.hermitianScalarExtensionSeminorm_sq _ _

/-- Expanding the actual completed pairing gives measurable rational
evaluations whenever the extending complex embeddings are measurable. -/
theorem measurable_hermitianScalarExtensionArchInner
    [hξ : ξ.IsMeasurable]
    (τ : ∀ x : (S.algebraicExtension L).Ωinf, x.val.abv.Completion →+* ℂ)
    (hτ : ∀ x a, ‖τ x a‖ = ‖a‖)
    (hm : ∀ a : L, Measurable (fun x : (S.algebraicExtension L).Ωinf =>
      τ x (algebraMap L x.val.abv.Completion a)))
    (K₀ : Subfield K) [Countable K₀]
    (hK₀ : ∀ ω ∈ S.Ωinf, S.IsDenseSubfieldAt K₀ ω) (z t : L ⊗[K] E) :
    Measurable (fun x : (S.algebraicExtension L).Ωinf =>
      τ x (hermitianScalarExtensionArchInner ξ x
        ((1 : x.val.abv.Completion) ⊗ₜ[L] z)
        ((1 : x.val.abv.Completion) ⊗ₜ[L] t))) := by
  classical
  let p : (S.algebraicExtension L).Ωinf → S.Ωinf := fun x =>
    ⟨x.val.base, (scalarExtension_mem_Ωinf_iff x.val).mp x.property⟩
  have hp₀ : Measurable (fun x : (S.algebraicExtension L).Ω => x.base) :=
    AdelicStructure.Algebraic.measurable_proj_projective S L
  have hp : Measurable p :=
    (hp₀.comp measurable_subtype_coe).subtype_mk
  let σ : ∀ x : (S.algebraicExtension L).Ωinf,
      (S.ϕ (p x).val).Completion →+* ℂ := fun x => by
    let := AbsoluteValue.normedAlgebraCompletionOfEq
      (S.ϕ x.val.base) x.val.abv x.val.restrict_eq
    exact (τ x).comp (algebraMap (S.ϕ x.val.base).Completion x.val.abv.Completion)
  have hσ (x) (a : (S.ϕ (p x).val).Completion) : ‖σ x a‖ = ‖a‖ := by
    let := AbsoluteValue.normedAlgebraCompletionOfEq
      (S.ϕ x.val.base) x.val.abv x.val.restrict_eq
    change ‖τ x (algebraMap (S.ϕ x.val.base).Completion x.val.abv.Completion a)‖ = ‖a‖
    rw [hτ, norm_algebraMap']
  have hmσ (a : K) : Measurable (fun x =>
      σ x (algebraMap K (S.ϕ (p x).val).Completion a)) := by
    convert hm (algebraMap K L a) using 1
    funext x
    let := AbsoluteValue.normedAlgebraCompletionOfEq
      (S.ϕ x.val.base) x.val.abv x.val.restrict_eq
    change τ x (algebraMap (S.ϕ x.val.base).Completion x.val.abv.Completion
      (algebraMap K (S.ϕ x.val.base).Completion a)) = _
    rw [AbsoluteValue.algebraMap_normedAlgebraCompletionOfEq_coe]
  have hpair (e f : E) : Measurable (fun x =>
      σ x (ξ.archimedeanInner (p x)
        ((1 : (S.ϕ (p x).val).Completion) ⊗ₜ[K] e)
        ((1 : (S.ϕ (p x).val).Completion) ⊗ₜ[K] f))) := by
    apply hξ.archimedeanInner_of_measurable_coordinates (Module.finBasis K E)
      p hp σ hσ hmσ K₀ (fun x => hK₀ (p x).val (p x).property)
    all_goals
      intro i
      simpa only [Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul,
        Algebra.smul_def, mul_one] using hmσ _
  induction z using TensorProduct.inductionOn with
  | tmul a e =>
      induction t using TensorProduct.inductionOn with
      | tmul c f =>
          convert (((Complex.continuous_conj.measurable).comp (hm a)).mul
            (hm c)).mul (hpair e f) using 1
          funext x
          exact hermitianScalarExtensionArchInner_rational_tmul ξ
            x (τ x) (hτ x) a c e f
      | add t q ht hq =>
          convert ht.add hq using 1
          funext x
          simp only [TensorProduct.tmul_add, hermitianScalarExtensionArchInner_add_right,
            map_add, Pi.add_apply]
  | add z q hz hq =>
      convert hz.add hq using 1
      funext x
      simp only [TensorProduct.tmul_add, hermitianScalarExtensionArchInner_add_left,
        map_add, Pi.add_apply]

/-- In a finite extension, the actual Archimedean Hermitian norm is the
square root of the measurable real diagonal of its defining pairing. -/
theorem measurable_hermitianScalarExtension_norm_infinite_of_finiteDimensional
    [FiniteDimensional K L] [hξ : ξ.IsMeasurable]
    [hcount : S.HasCommonCountableDenseSubfield] (z : L ⊗[K] E) :
    Measurable (fun x : (S.algebraicExtension L).Ωinf =>
      (hermitianScalarExtension ξ).norm x.val
        ((1 : x.val.abv.Completion) ⊗ₜ[L] z)) := by
  obtain ⟨L₀, hcL, hdL⟩ := hcount.algebraicExtension_of_finiteDimensional (L := L)
  let : Countable L₀ := hcL
  obtain ⟨K₀, hc, hd⟩ := hcount
  let : Countable K₀ := hc
  obtain ⟨τ, hτ, hm⟩ := (S.algebraicExtension L).exists_measurable_archimedeanComplexEmbedding
    L₀ (fun x _ => hdL x)
  have hi := (Complex.measurable_re.comp
    (measurable_hermitianScalarExtensionArchInner ξ
      τ hτ hm K₀ (fun ω _ => hd ω) z z)).sqrt
  convert hi using 1
  funext x
  dsimp only [Function.comp_def]
  rw [← hermitianScalarExtension_norm_sq_eq_re_archInner ξ x (τ x) (hτ x)]
  exact (Real.sqrt_sq ((hermitianScalarExtension ξ).norm_nonneg x.val
    ((1 : x.val.abv.Completion) ⊗ₜ[L] z))).symm

/-- Finite Hermitian scalar extension preserves measurability for the actual
completed norms under the source common countable-density hypothesis. -/
theorem IsMeasurable.hermitianScalarExtension_of_finiteDimensional
    [FiniteDimensional K L] (hξ : ξ.IsMeasurable)
    (hcount : S.HasCommonCountableDenseSubfield) :
    (hermitianScalarExtension (L := L) ξ).IsMeasurable := by
  constructor
  intro z
  apply measurable_of_restrict_of_restrict_compl (S.algebraicExtension L).measurableSet_Ωinf
  · exact measurable_hermitianScalarExtension_norm_infinite_of_finiteDimensional
      ξ z
  · have hi := hξ.injectiveScalarExtension_of_common_countable_dense_subfield (L := L) hcount
    convert (hi z).comp measurable_subtype_coe using 1
    funext x
    exact hermitianScalarExtension_norm_of_finite ξ x.val
      (not_not.mp x.property) _

/-- The defining completed pairing on rational pure tensors, before applying
any complex embedding. -/
theorem hermitianScalarExtensionArchInner_rational_tmul_eq
    (x : (S.algebraicExtension L).Ωinf) (a c : L) (e f : E) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq
      (S.ϕ x.val.base) x.val.abv x.val.restrict_eq
    let : IsRCLikeNormedField x.val.abv.Completion := hL x.val x.property
    let := IsRCLikeNormedField.rclike x.val.abv.Completion
    hermitianScalarExtensionArchInner ξ x
      ((1 : x.val.abv.Completion) ⊗ₜ[L] (a ⊗ₜ[K] e))
      ((1 : x.val.abv.Completion) ⊗ₜ[L] (c ⊗ₜ[K] f)) =
      starRingEnd x.val.abv.Completion (algebraMap L x.val.abv.Completion a) *
        algebraMap L x.val.abv.Completion c *
        algebraMap (S.ϕ x.val.base).Completion x.val.abv.Completion
          (ξ.archimedeanInner
            ⟨x.val.base, (scalarExtension_mem_Ωinf_iff x.val).mp x.property⟩
            ((1 : (S.ϕ x.val.base).Completion) ⊗ₜ[K] e)
            ((1 : (S.ϕ x.val.base).Completion) ⊗ₜ[K] f)) := by
  intro aVW hW rW
  let := aVW
  let := hW
  let := rW
  let := hS x.val.base ((scalarExtension_mem_Ωinf_iff x.val).mp x.property)
  let := IsRCLikeNormedField.rclike (S.ϕ x.val.base).Completion
  let := ξ.fibreNormedAddCommGroup x.val.base
  let := ξ.fibreNormedSpace x.val.base
  let := ξ.fiberInnerProductSpace x.val.base ((scalarExtension_mem_Ωinf_iff x.val).mp x.property)
  simp only [hermitianScalarExtensionArchInner, completedScalarExtensionEquiv_tmul,
    mul_one, ArakelovGeometry.hermitianScalarExtensionCore_tmul]
  rfl

/-- The actual defining pairing of a finite-stage rational vector is
transported by the canonical isometric completed-field embedding. -/
theorem hermitianScalarExtensionArchInner_finiteStage
    (F : AdelicStructure.FiniteIntermediateField K L)
    [hF : (S.algebraicExtension F).IsArchimedeanNormalized]
    (x : (S.algebraicExtension L).Ωinf) (z t : F ⊗[K] E) :
    let xF : (S.algebraicExtension F).Ωinf :=
      ⟨AdelicStructure.ParameterSpaceExtension.restrict S L x.val F,
        (scalarExtension_mem_Ωinf_iff _).mpr
          ((scalarExtension_mem_Ωinf_iff x.val).mp x.property)⟩
    let := AbsoluteValue.normedAlgebraCompletionOfEq
      xF.val.abv x.val.abv rfl
    algebraMap xF.val.abv.Completion x.val.abv.Completion
      (hermitianScalarExtensionArchInner ξ xF
        ((1 : xF.val.abv.Completion) ⊗ₜ[F] z)
        ((1 : xF.val.abv.Completion) ⊗ₜ[F] t)) =
      hermitianScalarExtensionArchInner ξ x
        ((1 : x.val.abv.Completion) ⊗ₜ[L]
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
            ((1 : L) ⊗ₜ[F] z)))
        ((1 : x.val.abv.Completion) ⊗ₜ[L]
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
            ((1 : L) ⊗ₜ[F] t))) := by
  intro xF aFW
  let := aFW
  let : IsRCLikeNormedField xF.val.abv.Completion := hF xF.val xF.property
  let := IsRCLikeNormedField.rclike xF.val.abv.Completion
  let : IsRCLikeNormedField x.val.abv.Completion := hL x.val x.property
  let := IsRCLikeNormedField.rclike x.val.abv.Completion
  let := AbsoluteValue.normedAlgebraCompletionOfEq
    (S.ϕ x.val.base) xF.val.abv xF.val.restrict_eq
  let := AbsoluteValue.normedAlgebraCompletionOfEq
    (S.ϕ x.val.base) x.val.abv x.val.restrict_eq
  let := AbsoluteValue.isScalarTower_completionOfEq_tower
    (S.ϕ x.val.base) xF.val.abv x.val.abv xF.val.restrict_eq rfl x.val.restrict_eq
  let C := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
  have hcoef (a : F) :
      algebraMap xF.val.abv.Completion x.val.abv.Completion
        (algebraMap F xF.val.abv.Completion a) =
      algebraMap L x.val.abv.Completion (algebraMap F L a) :=
    AbsoluteValue.algebraMap_normedAlgebraCompletionOfEq_coe xF.val.abv x.val.abv rfl a
  have hbase (a : (S.ϕ x.val.base).Completion) :
      algebraMap xF.val.abv.Completion x.val.abv.Completion
        (algebraMap (S.ϕ x.val.base).Completion xF.val.abv.Completion a) =
      algebraMap (S.ϕ x.val.base).Completion x.val.abv.Completion a :=
    (IsScalarTower.algebraMap_apply
      (S.ϕ x.val.base).Completion xF.val.abv.Completion x.val.abv.Completion a).symm
  change algebraMap xF.val.abv.Completion x.val.abv.Completion
      (hermitianScalarExtensionArchInner ξ xF (1 ⊗ₜ[F] z) (1 ⊗ₜ[F] t)) =
    hermitianScalarExtensionArchInner ξ x
      (1 ⊗ₜ[L] (C (1 ⊗ₜ[F] z))) (1 ⊗ₜ[L] (C (1 ⊗ₜ[F] t)))
  induction z using TensorProduct.inductionOn with
  | tmul a e =>
      induction t using TensorProduct.inductionOn with
      | tmul c f =>
          simp only [C, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
            Algebra.smul_def, mul_one]
          rw [hermitianScalarExtensionArchInner_rational_tmul_eq ξ xF,
            hermitianScalarExtensionArchInner_rational_tmul_eq ξ x]
          simp only [map_mul, normedAlgebra_map_conj]
          let q := ξ.archimedeanInner
            ⟨x.val.base, (scalarExtension_mem_Ωinf_iff x.val).mp x.property⟩
            ((1 : (S.ϕ x.val.base).Completion) ⊗ₜ[K] e)
            ((1 : (S.ϕ x.val.base).Completion) ⊗ₜ[K] f)
          change starRingEnd x.val.abv.Completion
              (algebraMap xF.val.abv.Completion x.val.abv.Completion
                (algebraMap F xF.val.abv.Completion a)) *
              algebraMap xF.val.abv.Completion x.val.abv.Completion
                (algebraMap F xF.val.abv.Completion c) *
              algebraMap xF.val.abv.Completion x.val.abv.Completion
                (algebraMap (S.ϕ x.val.base).Completion xF.val.abv.Completion q) =
            starRingEnd x.val.abv.Completion
              (algebraMap L x.val.abv.Completion (algebraMap F L a)) *
              algebraMap L x.val.abv.Completion (algebraMap F L c) *
              algebraMap (S.ϕ x.val.base).Completion x.val.abv.Completion q
          rw [hcoef, hcoef, hbase]
      | add t q ht hq =>
          simpa only [TensorProduct.tmul_add, map_add,
            hermitianScalarExtensionArchInner_add_right] using congrArg₂ (· + ·) ht hq
  | add z q hz hq =>
      simpa only [TensorProduct.tmul_add, map_add,
        hermitianScalarExtensionArchInner_add_left] using congrArg₂ (· + ·) hz hq

/-- A rational vector defined over a finite intermediate field has exactly
the same actual Hermitian norm at its restricted place. -/
theorem hermitianScalarExtension_norm_finiteStage
    (F : AdelicStructure.FiniteIntermediateField K L)
    [hF : (S.algebraicExtension F).IsArchimedeanNormalized]
    (x : S.ParameterSpaceExtension L) (z : F ⊗[K] E) :
    (hermitianScalarExtension ξ).norm x
      ((1 : x.abv.Completion) ⊗ₜ[L]
        (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
          ((1 : L) ⊗ₜ[F] z))) =
      (hermitianScalarExtension ξ).norm
        (AdelicStructure.ParameterSpaceExtension.restrict S L x F)
        ((1 : (x.abv.under F).Completion) ⊗ₜ[F] z) := by
  let y := AdelicStructure.ParameterSpaceExtension.restrict S L x F
  let Z : x.abv.Completion ⊗[L] (L ⊗[K] E) :=
    (1 : x.abv.Completion) ⊗ₜ[L]
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E ((1 : L) ⊗ₜ[F] z))
  let Y : y.abv.Completion ⊗[F] (F ⊗[K] E) := (1 : y.abv.Completion) ⊗ₜ[F] z
  by_cases hx : x ∈ (S.algebraicExtension L).Ωfin
  · have hb : x.base ∈ S.Ωfin := (AdelicStructure.mem_Ωfin_algebraicExtension_iff x).mp hx
    have hy : y ∈ (S.algebraicExtension F).Ωfin :=
      (AdelicStructure.mem_Ωfin_algebraicExtension_iff y).mpr hb
    calc
      _ = (ξ.injectiveScalarExtension (L := L)).norm x Z :=
        hermitianScalarExtension_norm_of_finite ξ x hx Z
      _ = (ξ.scalarExtension (L := L)).norm x Z :=
        (ξ.scalarExtension_norm_of_mem_Ωfin x hb Z).symm
      _ = (ξ.scalarExtension (L := F)).norm y Y :=
        ξ.scalarExtension_norm_finiteStage F x z
      _ = (ξ.injectiveScalarExtension (L := F)).norm y Y :=
        ξ.scalarExtension_norm_of_mem_Ωfin y hb Y
      _ = _ := (hermitianScalarExtension_norm_of_finite ξ y hy Y).symm
  · have hy : y ∈ (S.algebraicExtension F).Ωinf :=
      (scalarExtension_mem_Ωinf_iff y).mpr ((scalarExtension_mem_Ωinf_iff x).mp hx)
    let := AbsoluteValue.normedAlgebraCompletionOfEq y.abv x.abv rfl
    let : IsRCLikeNormedField x.abv.Completion := hL x hx
    let := IsRCLikeNormedField.rclike x.abv.Completion
    let τ := rclikeComplexEmbedding x.abv.Completion
    let σ := τ.comp (algebraMap y.abv.Completion x.abv.Completion)
    have hτ (a) : ‖τ a‖ = ‖a‖ := norm_rclikeComplexEmbedding a
    have hσ (a) : ‖σ a‖ = ‖a‖ := by
      rw [RingHom.comp_apply, hτ, norm_algebraMap']
    have hi := hermitianScalarExtensionArchInner_finiteStage ξ F
      ⟨x, hx⟩ z z
    have h₁ := hermitianScalarExtension_norm_sq_eq_re_archInner ξ ⟨x, hx⟩ τ hτ Z
    have h₂ := hermitianScalarExtension_norm_sq_eq_re_archInner ξ ⟨y, hy⟩ σ hσ Y
    have hs := h₁.trans
      ((congrArg (fun a : x.abv.Completion => (τ a).re) hi.symm).trans h₂.symm)
    exact (sq_eq_sq₀ ((hermitianScalarExtension ξ).norm_nonneg x Z)
      ((hermitianScalarExtension ξ).norm_nonneg y Y)).mp hs

omit hL in
/-- Arbitrary algebraic Hermitian scalar extension preserves measurability
under common countable density and the original usual Archimedean norms.
The extending normalization is derived on the actual completed fields. -/
theorem IsMeasurable.hermitianScalarExtension_of_common_countable_dense_subfield
    (hξ : ξ.IsMeasurable) (hcount : S.HasCommonCountableDenseSubfield) :
    (hermitianScalarExtension ξ
      (hL := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension
          (L := L))⟩)).IsMeasurable := by
  constructor
  intro z
  obtain ⟨F, y, hy⟩ := exists_finiteStage_tensor_lift z
  let hF := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := F)
  let hL := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
  have hm := IsMeasurable.hermitianScalarExtension_of_finiteDimensional
    (L := F) ξ (hL := ⟨hF⟩) hξ hcount
  have hr : @Measurable (S.algebraicExtension L).Ω (S.algebraicExtension F).Ω
      (S.algebraicExtension L).instMeasurableSpaceΩ
      (S.algebraicExtension F).instMeasurableSpaceΩ
      (fun x => AdelicStructure.ParameterSpaceExtension.restrict S L x F) := by
    change @Measurable _ _ (AdelicStructure.Algebraic.projectiveMeasurableSpace S L)
      (AdelicStructure.Algebraic.projectiveMeasurableSpace S F) _
    rw [AdelicStructure.Algebraic.projectiveMeasurableSpace_eq,
      AdelicStructure.Algebraic.projectiveMeasurableSpace_eq]
    exact AdelicStructure.ParameterSpaceExtension.measurable_restrict S L F.1
  have he : (fun x : (S.algebraicExtension L).Ω =>
      (hermitianScalarExtension ξ (hL := ⟨hL⟩)).norm x
        ((1 : x.abv.Completion) ⊗ₜ[L] z)) =
      (fun x : (S.algebraicExtension L).Ω =>
        (hermitianScalarExtension ξ (hL := ⟨hF⟩)).norm
          (AdelicStructure.ParameterSpaceExtension.restrict S L x F)
          ((1 : (x.abv.under F).Completion) ⊗ₜ[F] y)) := by
    funext x
    rw [← hy]
    exact hermitianScalarExtension_norm_finiteStage ξ (hL := ⟨hL⟩) F (hF := ⟨hF⟩) x y
  exact he.symm ▸ (hm y).comp hr

end ArakelovGeometry.NormFamily
