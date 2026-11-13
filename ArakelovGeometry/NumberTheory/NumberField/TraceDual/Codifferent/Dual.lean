/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.TraceDual.Integral

import Mathlib.Topology.Sheaves.Init

/-!
# Original codifferent-valued lattice dual

The canonical codifferent is a literal submodule of K. Restriction of original
K-linear functionals gives the actual OK-linear dual into that submodule.
-/

@[expose] public section

noncomputable section

open scoped NumberField TensorProduct nonZeroDivisors

namespace ArakelovGeometry.NumberFieldCodifferentDual

variable {K E : Type*} [Field K] [NumberField K]
  [AddCommGroup E] [Module K E]

/-- The usual trace codifferent as its literal integral submodule of K. -/
def codifferentModule (K : Type*) [Field K] [NumberField K] : Submodule (𝓞 K) K :=
  (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)).coeToSubmodule

/-- Original evaluation with values in the original codifferent. -/
def restriction (M : Submodule (𝓞 K) E) :
    NumberFieldIntegralTraceDual.integralTraceDual M →ₗ[𝓞 K]
      (M →ₗ[𝓞 K] codifferentModule K) where
  toFun f := ((f.1.restrictScalars (𝓞 K)).comp M.subtype).codRestrict
    (codifferentModule K) (fun m =>
      (NumberFieldIntegralTraceDual.mem_integralTraceDual_iff_codifferent M f.1).mp f.2 m)
  map_add' f g := by
    apply LinearMap.ext
    intro m
    exact Subtype.ext rfl
  map_smul' a f := by
    apply LinearMap.ext
    intro m
    exact Subtype.ext rfl

@[simp]
theorem restriction_apply (M : Submodule (𝓞 K) E)
    (f : NumberFieldIntegralTraceDual.integralTraceDual M) (m : M) :
    (restriction M f m : K) = f.1 (m : E) := rfl

/-- Extend a codifferent-valued original map through the original generic tensor. -/
def extension (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤)
    (g : M →ₗ[𝓞 K] codifferentModule K) : Module.Dual K E :=
  (((codifferentModule K).subtype.comp g).liftBaseChange K).comp
    (NumberFieldFullLattice.genericTensorEquiv M hspan).symm.toLinearMap

@[simp]
theorem extension_apply (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤)
    (g : M →ₗ[𝓞 K] codifferentModule K) (m : M) :
    extension M hspan g (m : E) = (g m : K) := by
  let e := NumberFieldFullLattice.genericTensorEquiv M hspan
  have he : e (1 ⊗ₜ[𝓞 K] m) = (m : E) := by simp [e]
  have hi : e.symm (m : E) = 1 ⊗ₜ[𝓞 K] m :=
    (congrArg e.symm he.symm).trans (e.symm_apply_apply _)
  change ((codifferentModule K).subtype.comp g).liftBaseChange K (e.symm (m : E)) = _
  rw [hi, LinearMap.liftBaseChange_tmul]
  simp

theorem restriction_injective (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    Function.Injective (restriction M) := by
  intro f g h
  apply NumberFieldIntegralTraceDual.traceRestriction_injective M hspan
  apply LinearMap.ext
  intro m
  apply (Int.cast_injective (α := ℚ))
  rw [NumberFieldIntegralTraceDual.traceRestriction_apply,
    NumberFieldIntegralTraceDual.traceRestriction_apply]
  exact congrArg (Algebra.trace ℚ K)
    (congrArg (fun φ : M →ₗ[𝓞 K] codifferentModule K => (φ m : K)) h)

theorem restriction_surjective (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    Function.Surjective (restriction M) := by
  intro g
  have hg : extension M hspan g ∈ NumberFieldIntegralTraceDual.integralTraceDual M := by
    apply (NumberFieldIntegralTraceDual.mem_integralTraceDual_iff_codifferent _ _).mpr
    intro m
    rw [extension_apply]
    exact (g m).property
  refine ⟨⟨extension M hspan g, hg⟩, ?_⟩
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  exact extension_apply M hspan g m

/-- The actual integral linear isomorphism into the original codifferent. -/
def codifferentEquiv (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    NumberFieldIntegralTraceDual.integralTraceDual M ≃ₗ[𝓞 K]
      (M →ₗ[𝓞 K] codifferentModule K) :=
  LinearEquiv.ofBijective (restriction M)
    ⟨restriction_injective M hspan, restriction_surjective M hspan⟩

@[simp]
theorem codifferentEquiv_apply (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤)
    (f : NumberFieldIntegralTraceDual.integralTraceDual M) (m : M) :
    (codifferentEquiv M hspan f m : K) = f.1 (m : E) := rfl

@[simp]
theorem codifferentEquiv_symm_apply (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤)
    (g : M →ₗ[𝓞 K] codifferentModule K) (m : M) :
    ((codifferentEquiv M hspan).symm g).1 (m : E) = (g m : K) :=
  congrArg (fun φ : M →ₗ[𝓞 K] codifferentModule K => (φ m : K))
    ((codifferentEquiv M hspan).apply_symm_apply g)

end ArakelovGeometry.NumberFieldCodifferentDual

namespace ArakelovGeometry.NormFamily

open AdelicStructure

variable {K E : Type*} [Field K] [NumberField K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}

/-- The actual codifferent-valued dual of the original dominated pure global ball. -/
def normalizedGlobalUnitBallCodifferentEquiv
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) [hdom : ξ.IsDominated]
    [hξ : ξ.IsUltrametricAtFinitePlaces] [hpure : ξ.IsPureAtFinitePlaces] :
    NumberFieldIntegralTraceDual.integralTraceDual (ξ.globalUnitBallModule) ≃ₗ[𝓞 K]
      ((ξ.globalUnitBallModule) →ₗ[𝓞 K] NumberFieldCodifferentDual.codifferentModule K) :=
  NumberFieldCodifferentDual.codifferentEquiv (ξ.globalUnitBallModule)
    (hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure).2.2

@[simp]
theorem normalizedGlobalUnitBallCodifferentEquiv_apply
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [ξ.IsDominated] [ξ.IsUltrametricAtFinitePlaces] [ξ.IsPureAtFinitePlaces]
    (f : NumberFieldIntegralTraceDual.integralTraceDual (ξ.globalUnitBallModule))
    (m : ξ.globalUnitBallModule) :
    (ξ.normalizedGlobalUnitBallCodifferentEquiv f m : K) = f.1 (m : E) :=
  NumberFieldCodifferentDual.restriction_apply _ _ _

end ArakelovGeometry.NormFamily
