/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Examples.Trivial
import ArakelovGeometry.ExternalResults.Place
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The mass-one trivial place and its actual completed fibre

The single place specializes the existing proper trivial adelic structure.
The canonical algebra map is bijective at the trivial absolute value;
the completed tensor fibre is therefore canonically the original space.
-/

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.AdelicStructure

noncomputable section

universe u w

/-- One actual trivial absolute value with mass one, reusing the existing
proper trivial adelic structure. -/
abbrev singleTrivialPlace (K : Type u) [Field K] : AdelicStructure.{u, 0} K :=
  trivialAdelicStructure K PUnit (Measure.dirac PUnit.unit)

variable (K : Type u) [Field K]

instance singleTrivialPlace_isProper : (singleTrivialPlace K).IsProper := inferInstance

instance singleTrivialPlace_discreteMeasurableSpace :
    DiscreteMeasurableSpace (singleTrivialPlace K).Ω := by
  change DiscreteMeasurableSpace PUnit
  infer_instance

instance singleTrivialPlace_isProbabilityMeasure :
    IsProbabilityMeasure (singleTrivialPlace K).v := by
  change IsProbabilityMeasure (Measure.dirac PUnit.unit)
  infer_instance

@[simp]
theorem singleTrivialPlace_Ωinf : (singleTrivialPlace K).Ωinf = ∅ := by
  classical
  ext ω
  have h := AbsoluteValue.isNonarchimedeanPlace_trivialPlace (K := K)
  simp only [AbsoluteValue.IsNonarchimedeanPlace, AbsoluteValue.trivialPlace_out_eq] at h
  change ¬ IsNonarchimedean (AbsoluteValue.trivial : AbsoluteValue K ℝ) ↔ False
  exact iff_false_intro (not_not.mpr h)

@[simp]
theorem singleTrivialPlace_Ωfin : (singleTrivialPlace K).Ωfin = Set.univ := by
  classical
  ext ω
  have h := AbsoluteValue.isNonarchimedeanPlace_trivialPlace (K := K)
  simp only [AbsoluteValue.IsNonarchimedeanPlace, AbsoluteValue.trivialPlace_out_eq] at h
  simp [Ωfin, singleTrivialPlace, trivialAdelicStructure, h]

/-- The usual infinite-place normalization is vacuous at the actual
single trivial place, in every characteristic. -/
theorem singleTrivialPlace_normalized :
    ∀ ω ∈ (singleTrivialPlace K).Ωinf,
      IsRCLikeNormedField ((singleTrivialPlace K).ϕ ω).Completion := by
  simp only [singleTrivialPlace_Ωinf, Set.mem_empty_iff_false, false_implies, implies_true]

@[simp]
theorem integral_singleTrivialPlace (f : (singleTrivialPlace K).Ω → ℝ) :
    ∫ ω, f ω ∂(singleTrivialPlace K).v = f PUnit.unit := integral_dirac _ _

open Classical in
/-- The inverse of the canonical algebra map to the actual trivial
completion. No alternate completion or scalar action is introduced. -/
def trivialCompletionAlgEquiv :
    (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion ≃ₐ[K] K :=
  (AlgEquiv.ofBijective
    (Algebra.ofId K (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion) ⟨
      (algebraMap K (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion).injective,
      by
        intro y
        have ht : ¬ (AbsoluteValue.trivial : AbsoluteValue K ℝ).IsNontrivial :=
          (AbsoluteValue.not_isNontrivial_iff _).mpr (fun x hx ↦ AbsoluteValue.trivial_apply hx)
        obtain ⟨x, hx⟩ := AbsoluteValue.surjective_coe_completion_of_not_isNontrivial
          (AbsoluteValue.trivial : AbsoluteValue K ℝ) ht y
        refine ⟨x.ofAbs, ?_⟩
        simpa only [Algebra.ofId_apply, UniformSpace.Completion.algebraMap_def,
          WithAbs.algebraMap_right_apply, Algebra.algebraMap_self, RingHom.id_apply,
          WithAbs.toAbs_ofAbs] using hx⟩).symm

open Classical in
@[simp]
theorem trivialCompletionAlgEquiv_algebraMap (x : K) :
    trivialCompletionAlgEquiv K
      (algebraMap K (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion x) = x :=
  (trivialCompletionAlgEquiv K).commutes x

open Classical in
/-- The actual completed norm is the original trivial absolute value
under the canonical inverse, on every completed scalar. -/
theorem norm_trivialCompletion
    (a : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion) :
    ‖a‖ = AbsoluteValue.trivial (trivialCompletionAlgEquiv K a) := by
  have he := (trivialCompletionAlgEquiv K).symm_apply_apply a
  change algebraMap K (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
    (trivialCompletionAlgEquiv K a) = a at he
  calc
    ‖a‖ = ‖algebraMap K (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
        (trivialCompletionAlgEquiv K a)‖ := congrArg norm he.symm
    _ = AbsoluteValue.trivial (trivialCompletionAlgEquiv K a) := by
      rw [UniformSpace.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
        UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_toAbs]
      simp

variable (E : Type w) [AddCommGroup E] [Module K E]

open Classical in
/-- The canonical identification of the genuine completed tensor fibre
at a trivial place with the original rational vector space. -/
def trivialCompletedTensorEquiv :
    (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion ⊗[K] E ≃ₗ[K] E :=
  (TensorProduct.congr (trivialCompletionAlgEquiv K).toLinearEquiv
    (LinearEquiv.refl K E)).trans (TensorProduct.lid K E)

open Classical in
@[simp]
theorem trivialCompletedTensorEquiv_tmul
    (a : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion) (x : E) :
    trivialCompletedTensorEquiv K E (a ⊗ₜ[K] x) = trivialCompletionAlgEquiv K a • x := by
  simp [trivialCompletedTensorEquiv]

open Classical in
@[simp]
theorem trivialCompletedTensorEquiv_one_tmul (x : E) :
    trivialCompletedTensorEquiv K E ((1 : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion)
      ⊗ₜ[K] x) = x := by
  simp

open Classical in
/-- Completed scalar multiplication is transported through the actual
field isomorphism on every tensor, not only rational pure tensors. -/
theorem trivialCompletedTensorEquiv_smul
    (a : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion)
    (z : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion ⊗[K] E) :
    trivialCompletedTensorEquiv K E (a • z) =
      trivialCompletionAlgEquiv K a • trivialCompletedTensorEquiv K E z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => simp [TensorProduct.smul_tmul', mul_smul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

end

end ArakelovGeometry.AdelicStructure
