/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic

import ArakelovGeometry.AdelicVectorBundle.NormFamily.BasisComparison
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Domination.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Domination.Descent
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Dual.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Identity
import Mathlib.CategoryTheory.Category.Init

/-!
# Descent from compatible norms on actual algebraic extensions

Compatibility is equality on all completed base vectors under the canonical
completed-fibre inclusion. It gives a restriction inequality for dual norms
and for mixed-basis distance, and the actual algebraic fibre integral descends
the resulting integrable envelopes.
-/

@[expose] public section

open MeasureTheory Filter
open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

universe u v w wE

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E) (η : NormFamily (S.algebraicExtension L) (L ⊗[K] E))
  (hcompat : ∀ x : S.ParameterSpaceExtension L,
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    ∀ y : (S.ϕ x.base).Completion ⊗[K] E,
      η.norm x ((completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).symm
        ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] y)) = ξ.norm x.base y)

include hcompat

/-- Restriction to every completed base vector cannot increase the dual norm.
The extended functional is transported through the actual completed pairing. -/
theorem dual_norm_le_of_completed_restriction (x : S.ParameterSpaceExtension L)
    (f : (S.ϕ x.base).Completion ⊗[K] Module.Dual K E) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    ξ.dual.norm x.base f ≤ η.dual.norm x
      ((dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion
        ((completedScalarExtensionEquiv (Module.Dual K E)
          (S.ϕ x.base) x.abv x.restrict_eq).symm
            ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] f))) := by
  intro aVW
  let := aVW
  let fL := (completedScalarExtensionEquiv (Module.Dual K E)
    (S.ϕ x.base) x.abv x.restrict_eq).symm
      ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] f)
  let f' := (dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion fL
  apply ξ.dual_norm_le x.base f (η.dual.norm_nonneg x f')
  intro y
  let yL := (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).symm
    ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] y)
  have he := completedScalarExtensionEquiv_dual_apply
    (S.ϕ x.base) x.abv x.restrict_eq fL yL
  simp only [fL, yL, LinearEquiv.apply_symm_apply, LinearMap.baseChange_tmul,
    LinearEquiv.coe_coe, dualBaseChangeEquiv_tmul, one_smul,
    Module.Dual.baseChange_apply_tmul, Algebra.smul_def, mul_one] at he
  have hm := (AbsoluteValue.isometry_normedAlgebraCompletionOfEq
    (S.ϕ x.base) x.abv x.restrict_eq).norm_map_of_map_zero (map_zero _)
      (dualBaseChangeEquiv K (S.ϕ x.base).Completion E f y)
  have hn := η.norm_dual_apply_le x f' yL
  have hc : η.norm x yL = ξ.norm x.base y := hcompat x y
  rw [hc] at hn
  exact hm.symm.trans_le ((congrArg (fun a : x.abv.Completion => ‖a‖) he).trans_le hn)

omit [FiniteDimensional K E] in
/-- Completed-fibre compatibility preserves the norm of each original
rational vector under the canonical algebraic scalar extension. -/
theorem norm_one_tmul_eq_of_completed_restriction (x : S.ParameterSpaceExtension L)
    (e : E) :
    η.norm x ((1 : x.abv.Completion) ⊗ₜ[L] ((1 : L) ⊗ₜ[K] e)) =
      ξ.norm x.base ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] e) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  have ht := completedScalarExtensionEquiv_tmul E (S.ϕ x.base) x.abv x.restrict_eq
    (1 : x.abv.Completion) (1 : L) e
  simp only [map_one, one_mul] at ht
  have hc := hcompat x ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] e)
  rw [← ht, LinearEquiv.symm_apply_apply] at hc
  exact hc

/-- The rational dual restriction inequality used in domination descent.
Its producer tests all completed base vectors. -/
theorem dual_norm_one_tmul_le_of_completed_restriction (x : S.ParameterSpaceExtension L)
    (f : Module.Dual K E) :
    ξ.dual.norm x.base ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] f) ≤
      η.dual.norm x ((1 : x.abv.Completion) ⊗ₜ[L] Module.Dual.baseChange L f) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  have h := dual_norm_le_of_completed_restriction ξ η hcompat x
    ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] f)
  simp only [completedScalarExtensionEquiv_symm_tmul, map_one, one_mul,
    LinearMap.baseChange_tmul, LinearEquiv.coe_coe, dualBaseChangeEquiv_tmul, one_smul] at h
  exact h

omit [FiniteDimensional K E] in
/-- Upper envelopes for rational primal norms descend through the actual
algebraic fibre integral under completed-fibre compatibility. -/
theorem IsUpperDominated.of_completed_restriction (hη : η.IsUpperDominated) :
    ξ.IsUpperDominated := by
  constructor
  intro e he
  have heL : (1 : L) ⊗ₜ[K] e ≠ 0 := by
    intro hz
    apply he
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := K) (B := L) E
    change (1 : L) ⊗ₜ[K] e = (1 : L) ⊗ₜ[K] (0 : E)
    simpa only [TensorProduct.tmul_zero] using hz
  have hu : HasIntegrableUpperBound
      (fun x : (S.algebraicExtension L).Ω => ξ.logNorm e x.base)
      (S.algebraicExtension L).v := by
    apply (hη ((1 : L) ⊗ₜ[K] e) heL).mono
    exact Eventually.of_forall fun x =>
      (congrArg Real.log (norm_one_tmul_eq_of_completed_restriction ξ η hcompat x e)).symm.le
  exact hu.of_algebraic_comp

/-- Domination descends from an actual algebraically extended norm family
agreeing with the original family on all completed base fibres. No original
ultrametricity or Archimedean normalization is required. -/
theorem IsDominated.of_completed_restriction (hη : η.IsDominated) : ξ.IsDominated := by
  refine ⟨IsUpperDominated.of_completed_restriction ξ η hcompat hη.1, ?_⟩
  constructor
  intro f hf
  have hfL : Module.Dual.baseChange L f ≠ 0 := by
    intro hz
    apply hf
    apply Module.FaithfullyFlat.tensorProduct_mk_injective
      (A := K) (B := L) (Module.Dual K E)
    change (1 : L) ⊗ₜ[K] f = (1 : L) ⊗ₜ[K] (0 : Module.Dual K E)
    apply (dualBaseChangeEquiv K L E).injective
    simp only [TensorProduct.tmul_zero, map_zero, dualBaseChangeEquiv_tmul, one_smul, hz]
  have hu : HasIntegrableUpperBound
      (fun x : (S.algebraicExtension L).Ω => ξ.dual.logNorm f x.base)
      (S.algebraicExtension L).v := by
    apply (hη.2 (Module.Dual.baseChange L f) hfL).mono
    exact Eventually.of_forall fun x => Real.log_le_log (ξ.dual.norm_rational_pos x.base hf)
      (dual_norm_one_tmul_le_of_completed_restriction ξ η hcompat x f)
  exact hu.of_algebraic_comp

variable {ι : Type*} [Fintype ι] (b : Module.Basis ι K E)

/-- Actual completed-fibre restriction bounds the original basis distance
by the extended basis distance. This uses compatibility on every completed
vector and the proved isometry of the mixed coordinate norms. -/
theorem localDist_ofBasisMixed_le_of_completed_restriction
    (x : S.ParameterSpaceExtension L) :
    ξ.localDist (ofBasisMixed S E b) x.base ≤ η.localDist
      (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)) x := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let η₀ := ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)
  have h0 := η.localDist_nonneg η₀ x
  apply (ξ.localDist_le_iff_norm_le (ofBasisMixed S E b) x.base h0).mpr
  intro y
  let z := (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).symm
    ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] y)
  have hb := (η.localDist_le_iff_norm_le η₀ x h0).mp le_rfl z
  have hn : η.norm x z = ξ.norm x.base y := hcompat x y
  have hm := ofBasisMixed_norm_completed_one_tmul b x y
  change η₀.norm x z = (ofBasisMixed S E b).norm x.base y at hm
  rw [hn, hm] at hb
  exact hb

omit [Fintype ι] in
/-- Strong domination descends from an actual compatible algebraic norm
family. Finite measure of the infinite locus suffices, without assuming
that the original family is ultrametric. -/
theorem IsStronglyDominated.of_completed_restriction (hη : η.IsStronglyDominated)
    (hfin : S.v S.Ωinf < ⊤) : ξ.IsStronglyDominated := by
  let b := Module.finBasis K E
  have hfinL : (S.algebraicExtension L).v (S.algebraicExtension L).Ωinf < ⊤ := by
    rw [scalarExtension_measure_Ωinf]
    exact hfin
  have hbL := IsStronglyDominated.localDist_ofBasisMixed (b.baseChange L) η hη hfinL
  have huL : HasIntegrableUpperBound
      (fun x : (S.algebraicExtension L).Ω => ξ.localDist (ofBasisMixed S E b) x.base)
      (S.algebraicExtension L).v := hbL.1.mono
    (Eventually.of_forall fun x =>
      localDist_ofBasisMixed_le_of_completed_restriction ξ η hcompat b x)
  have hu : HasIntegrableUpperBound (ξ.localDist (ofBasisMixed S E b)) S.v :=
    huL.of_algebraic_comp
  have hb : HasIntegrableBounds (ξ.localDist (ofBasisMixed S E b)) S.v :=
    ⟨hu, ⟨0, integrable_zero _ _ _, Eventually.of_forall (ξ.localDist_nonneg _)⟩⟩
  exact (isStronglyDominated_iff_localDist_ofBasisMixed_of_measure_lt_top b ξ hfin).mpr hb

end ArakelovGeometry.NormFamily

end
