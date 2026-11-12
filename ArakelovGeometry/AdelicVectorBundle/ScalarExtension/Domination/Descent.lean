/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Integral
import ArakelovGeometry.AdelicVectorBundle.Dual.Bidual
import ArakelovGeometry.AdelicVectorBundle.NormFamily.BasisComparison
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Domination.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Identity
import Mathlib.CategoryTheory.Category.Init

/-!
# Descent of domination along algebraic scalar extension

Integrable envelopes descend by the algebraic fibre-integration operator.
Completed base vectors identify the restricted extended norm with the
original bidual norm under the usual Archimedean normalization.
-/

@[expose] public section

open MeasureTheory Filter
open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

universe u v w wE

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- Algebraic fibre integration descends an integrable upper envelope,
without assuming measurability of the function on the base. -/
theorem HasIntegrableUpperBound.of_algebraic_comp {g : S.Ω → ℝ}
    (h : HasIntegrableUpperBound
      (fun x : (S.algebraicExtension L).Ω => g x.base) (S.algebraicExtension L).v) :
    HasIntegrableUpperBound g S.v := by
  obtain ⟨A, hA, hb⟩ := h
  refine ⟨AdelicStructure.Algebraic.fibreIntegral S L A,
    AdelicStructure.Algebraic.integrable_fibreIntegral S L hA, ?_⟩
  filter_upwards [AdelicStructure.Algebraic.ae_ae_fibre_of_ae S L hb,
    AdelicStructure.Algebraic.integrable_fibre_ae S L hA] with ω hωb hωA
  have hb' : ∀ᵐ x : AdelicStructure.Algebraic.BaseFiber L ω
      ∂AdelicStructure.Algebraic.fibreProbabilityMeasure S L ω, g ω ≤ A x.val := by
    filter_upwards [hωb] with x hx
    change g x.val.proj ≤ A x.val at hx
    simpa only [x.property] using hx
  have hi := integral_mono_ae (integrable_const (g ω)) hωA hb'
  simpa [AdelicStructure.Algebraic.fibreIntegral] using hi

namespace NormFamily

variable {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E)

/-- Restricting the actual injective extension to the original completed
fibre recovers its completed bidual norm. -/
theorem injectiveScalarExtension_norm_completed_one_tmul
    (x : S.ParameterSpaceExtension L) (y : (S.ϕ x.base).Completion ⊗[K] E) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    (ξ.injectiveScalarExtension (L := L)).norm x
      ((completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).symm
        ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] y)) =
      ξ.dual.dual.norm x.base
        ((Module.Dual.eval K E).baseChange (S.ϕ x.base).Completion y) := by
  intro aVW
  let := aVW
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  change scalarExtensionInjectiveSeminorm
    (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq
      ((completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).symm
        ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] y))) = _
  rw [LinearEquiv.apply_symm_apply, scalarExtensionInjectiveSeminorm_one_tmul]
  exact (ξ.dual_dual_norm_eval_eq_sSup x.base y).symm

/-- Under the usual Archimedean normalization, restricting the mixed
scalar extension to the original completed fibre is its bidual norm. -/
theorem scalarExtension_norm_completed_one_tmul
    [hS : S.IsArchimedeanNormalized]
    (x : S.ParameterSpaceExtension L) (y : (S.ϕ x.base).Completion ⊗[K] E) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    (ξ.scalarExtension (L := L)).norm x
      ((completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).symm
        ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] y)) =
      ξ.dual.dual.norm x.base
        ((Module.Dual.eval K E).baseChange (S.ϕ x.base).Completion y) := by
  intro aVW
  let := aVW
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let z := (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).symm
    ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] y)
  have hi := ξ.injectiveScalarExtension_norm_completed_one_tmul x y
  by_cases hx : x.base ∈ S.Ωfin
  · exact (ξ.scalarExtension_norm_of_mem_Ωfin x hx z).trans hi
  · apply le_antisymm
    · have hp : (ξ.projectiveScalarExtension (L := L)).norm x z ≤ ξ.norm x.base y := by
        change scalarExtensionProjectiveSeminorm
          (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq z) ≤ _
        rw [LinearEquiv.apply_symm_apply]
        exact scalarExtensionProjectiveSeminorm_one_tmul_le y
      exact ((ξ.scalarExtension_norm_of_not_mem_Ωfin x hx z).trans_le hp).trans_eq
        (ξ.dual_dual_norm_eval_eq_of_isRCLike x.base (hS x.base hx) y).symm
    · exact hi.symm.trans_le (ξ.injectiveScalarExtension_norm_le_scalarExtension_norm x z)

variable {ι : Type*} [Finite ι] (b : Module.Basis ι K E)

omit [Algebra.IsAlgebraic K L] [FiniteDimensional K E] in
/-- Completed coordinates of a base vector become their images under the
canonical isometric embedding of the two completed scalar fields. -/
theorem scalarExtension_coordinate_completed_one_tmul
    (x : S.ParameterSpaceExtension L) (y : (S.ϕ x.base).Completion ⊗[K] E) (i : ι) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    ((b.baseChange L).baseChange x.abv.Completion).equivFun
      ((completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).symm
        ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] y)) i =
      algebraMap (S.ϕ x.base).Completion x.abv.Completion
        ((b.baseChange (S.ϕ x.base).Completion).equivFun y i) := by
  intro aVW
  let := aVW
  induction y using TensorProduct.inductionOn with
  | add y z hy hz =>
      simp only [TensorProduct.tmul_add, map_add, Pi.add_apply, hy, hz]
  | tmul a e =>
      simp only [completedScalarExtensionEquiv_symm_tmul, mul_one,
        Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul,
        Algebra.smul_def, map_mul,
        AbsoluteValue.algebraMap_normedAlgebraCompletionOfEq_coe]

variable [Fintype ι]

omit [Finite ι] [FiniteDimensional K E] in
/-- The extended mixed rational-basis norm restricts isometrically to the
original completed mixed basis norm, including the empty basis. -/
theorem ofBasisMixed_norm_completed_one_tmul
    (x : S.ParameterSpaceExtension L) (y : (S.ϕ x.base).Completion ⊗[K] E) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)).norm x
      ((completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).symm
        ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] y)) =
      (ofBasisMixed S E b).norm x.base y := by
  intro aVW
  let := aVW
  let z := (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).symm
    ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] y)
  have hn (i : ι) :
      ‖((b.baseChange L).baseChange x.abv.Completion).equivFun z i‖ =
        ‖(b.baseChange (S.ϕ x.base).Completion).equivFun y i‖ := by
    rw [scalarExtension_coordinate_completed_one_tmul b x y i]
    exact (AbsoluteValue.isometry_normedAlgebraCompletionOfEq
      (S.ϕ x.base) x.abv x.restrict_eq).norm_map_of_map_zero (map_zero _) _
  by_cases hx : x.base ∈ S.Ωinf
  · have hxL : x ∈ (S.algebraicExtension L).Ωinf :=
      fun h => hx ((AdelicStructure.mem_Ωfin_algebraicExtension_iff x).mp h)
    have he := ofBasisMixed_norm_of_infinite (S := S.algebraicExtension L)
      (b.baseChange L) x hxL z
    rw [he, ofBasisMixed_norm_of_infinite b x.base hx y]
    exact Finset.sum_congr rfl (fun i _ => hn i)
  · have hfL : x ∈ (S.algebraicExtension L).Ωfin :=
      (AdelicStructure.mem_Ωfin_algebraicExtension_iff x).mpr (not_not.mp hx)
    have he := ofBasisMixed_norm_of_finite (S := S.algebraicExtension L)
      (b.baseChange L) x hfL z
    rw [he, ofBasisMixed_norm_of_finite b x.base (not_not.mp hx) y]
    change ‖((b.baseChange L).baseChange x.abv.Completion).equivFun z‖ =
      ‖(b.baseChange (S.ϕ x.base).Completion).equivFun y‖
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (_root_.norm_nonneg _)).mpr
      intro i
      rw [hn i]
      exact norm_le_pi_norm _ i
    · apply (pi_norm_le_iff_of_nonneg (_root_.norm_nonneg _)).mpr
      intro i
      rw [← hn i]
      exact norm_le_pi_norm _ i

omit [Finite ι] in
/-- Restriction to completed base vectors bounds the base bidual-to-basis
distance by the distance on every actual extended completed fibre. -/
theorem bidual_localDist_ofBasisMixed_le_scalarExtension
    [hS : S.IsArchimedeanNormalized]
    (x : S.ParameterSpaceExtension L) :
    (ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)).localDist
      (ofBasisMixed S E b) x.base ≤
        (ξ.scalarExtension (L := L)).localDist
          (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)) x := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let η := ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)
  let ηL := ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)
  have h0 := (ξ.scalarExtension (L := L)).localDist_nonneg ηL x
  apply (η.localDist_le_iff_norm_le (ofBasisMixed S E b) x.base h0).mpr
  intro y
  let z := (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).symm
    ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] y)
  have hb := ((ξ.scalarExtension (L := L)).localDist_le_iff_norm_le ηL x h0).mp le_rfl z
  have hn := ξ.scalarExtension_norm_completed_one_tmul x y
  have hm := ofBasisMixed_norm_completed_one_tmul b x y
  change (ξ.scalarExtension (L := L)).norm x z = _ at hn
  change ηL.norm x z = _ at hm
  rw [hn, hm] at hb
  exact hb

/-- Domination of an algebraic scalar extension descends to the actual
completed bidual family under the usual Archimedean normalization. -/
theorem IsDominated.bidual_of_scalarExtension
    (hL : (ξ.scalarExtension (L := L)).IsDominated)
    [hS : S.IsArchimedeanNormalized] :
    (ξ.dual.dual.pullback (Module.Dual.eval K E)
      (Module.eval_apply_injective K)).IsDominated := by
  let b := Module.finBasis K E
  let η := ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)
  have hfin := S.v_Ωinf_lt_top_of_isRCLike
  have hfinL : (S.algebraicExtension L).v (S.algebraicExtension L).Ωinf < ⊤ := by
    rw [scalarExtension_measure_Ωinf]
    exact hfin
  have hbL := IsDominated.localDist_ofBasisMixed_of_ultrametric (b.baseChange L)
    (ξ.scalarExtension (L := L)) hL ξ.scalarExtension_isUltrametric hfinL
  have hu : HasIntegrableUpperBound
      (fun x : (S.algebraicExtension L).Ω => η.localDist (ofBasisMixed S E b) x.base)
      (S.algebraicExtension L).v := hbL.1.mono
    (Eventually.of_forall fun x ↦ ξ.bidual_localDist_ofBasisMixed_le_scalarExtension b x)
  have hb : HasIntegrableBounds (η.localDist (ofBasisMixed S E b)) S.v :=
    ⟨hu.of_algebraic_comp,
      ⟨0, integrable_zero _ _ _, Eventually.of_forall (η.localDist_nonneg _)⟩⟩
  exact ((isStronglyDominated_iff_localDist_ofBasisMixed_of_measure_lt_top b η hfin).mpr hb).1

/-- The converse implication of Corollary 4.1.13: domination of one
algebraic scalar extension and integrable distance to the completed bidual
imply domination of the original family. -/
theorem IsDominated.of_scalarExtension
    (hL : (ξ.scalarExtension (L := L)).IsDominated)
    [hS : S.IsArchimedeanNormalized]
    (hb : HasIntegrableBounds
      (ξ.localDist (ξ.dual.dual.pullback (Module.Dual.eval K E)
        (Module.eval_apply_injective K))) S.v) : ξ.IsDominated := by
  have hη := IsDominated.bidual_of_scalarExtension ξ hL
  apply hη.of_localDist
  have he : (ξ.dual.dual.pullback (Module.Dual.eval K E)
      (Module.eval_apply_injective K)).localDist ξ =
        ξ.localDist (ξ.dual.dual.pullback (Module.Dual.eval K E)
          (Module.eval_apply_injective K)) :=
    funext fun ω => (ξ.dual.dual.pullback (Module.Dual.eval K E)
      (Module.eval_apply_injective K)).localDist_comm ξ ω
  rw [he]
  exact hb.1

end NormFamily

end ArakelovGeometry

end
