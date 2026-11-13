/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.TraceDual.Codifferent.Dual

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import Mathlib.Topology.Sheaves.Init

/-! # The actual codifferent tensor and original trace-integral dual

Finite generation of the original integral submodule produces its projectivity.
The native finite-projective Hom–tensor equivalence has the exact original
evaluation formula. Full span then identifies its target with the original
trace-integral dual and the actual integer dual. No freeness over the number
field's integer ring or target duality certificate is assumed.
-/

@[expose] public section

open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NumberFieldCodifferentTensorDual

open NumberFieldCodifferentDual NumberFieldIntegralTraceDual

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]

/-- Actual codifferent tensor evaluation for the produced finite projective module. -/
def tensorCodifferentEquiv (M : Submodule (𝓞 K) E) (hfg : M.FG) :
    codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M ≃ₗ[𝓞 K]
      (M →ₗ[𝓞 K] codifferentModule K) := by
  let : Module.Finite (𝓞 K) M := Module.Finite.of_fg hfg
  let := NumberFieldFullLattice.projective M hfg
  exact (TensorProduct.comm (𝓞 K) _ _).trans (dualTensorHomEquiv (𝓞 K) M _)

@[simp]
theorem tensorCodifferentEquiv_tmul_apply (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (a : codifferentModule K) (φ : Module.Dual (𝓞 K) M) (m : M) :
    tensorCodifferentEquiv M hfg (a ⊗ₜ[𝓞 K] φ) m = φ m • a := by
  let : Module.Finite (𝓞 K) M := Module.Finite.of_fg hfg
  let := NumberFieldFullLattice.projective M hfg
  simp [tensorCodifferentEquiv, dualTensorHomEquiv]

@[simp]
theorem tensorCodifferentEquiv_tmul_coe (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (a : codifferentModule K) (φ : Module.Dual (𝓞 K) M) (m : M) :
    (tensorCodifferentEquiv M hfg (a ⊗ₜ[𝓞 K] φ) m : K) =
      algebraMap (𝓞 K) K (φ m) * (a : K) := by
  rw [tensorCodifferentEquiv_tmul_apply, SetLike.val_smul]
  exact Algebra.smul_def (φ m) (a : K)

/-- The actual tensor description of original trace-integral functionals. -/
def traceTensorEquiv (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M ≃ₗ[𝓞 K] integralTraceDual M :=
  (tensorCodifferentEquiv M hfg).trans (codifferentEquiv M hspan).symm

@[simp]
theorem traceTensorEquiv_apply (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤)
    (z : codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) (m : M) :
    (traceTensorEquiv M hfg hspan z).1 (m : E) =
      (tensorCodifferentEquiv M hfg z m : K) :=
  codifferentEquiv_symm_apply M hspan (tensorCodifferentEquiv M hfg z) m

@[simp]
theorem traceTensorEquiv_tmul_apply (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤)
    (a : codifferentModule K) (φ : Module.Dual (𝓞 K) M) (m : M) :
    (traceTensorEquiv M hfg hspan (a ⊗ₜ[𝓞 K] φ)).1 (m : E) =
      algebraMap (𝓞 K) K (φ m) * (a : K) := by
  rw [traceTensorEquiv_apply, tensorCodifferentEquiv_tmul_coe]

/-- Trace evaluation identifies the tensor with the original integer dual.
Finite dimension of the original space is produced from finite generation and span. -/
def integerTensorEquiv (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M ≃ₗ[ℤ] Module.Dual ℤ M := by
  let : Module.Finite (𝓞 K) M := Module.Finite.of_fg hfg
  let : FiniteDimensional K E :=
    (NumberFieldFullLattice.genericTensorEquiv M hspan).finiteDimensional
  exact ((traceTensorEquiv M hfg hspan).restrictScalars ℤ).trans
    (integralTraceEquiv M hspan)

@[simp]
theorem integerTensorEquiv_apply (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤)
    (z : codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) (m : M) :
    (integerTensorEquiv M hfg hspan z m : ℚ) =
      Algebra.trace ℚ K (tensorCodifferentEquiv M hfg z m : K) := by
  let : Module.Finite (𝓞 K) M := Module.Finite.of_fg hfg
  let : FiniteDimensional K E :=
    (NumberFieldFullLattice.genericTensorEquiv M hspan).finiteDimensional
  exact (integralTraceEquiv_apply M hspan (traceTensorEquiv M hfg hspan z) m).trans
    (congrArg (Algebra.trace ℚ K) (traceTensorEquiv_apply M hfg hspan z m))

@[simp]
theorem integerTensorEquiv_tmul_apply (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤)
    (a : codifferentModule K) (φ : Module.Dual (𝓞 K) M) (m : M) :
    (integerTensorEquiv M hfg hspan (a ⊗ₜ[𝓞 K] φ) m : ℚ) =
      Algebra.trace ℚ K (algebraMap (𝓞 K) K (φ m) * (a : K)) := by
  rw [integerTensorEquiv_apply, tensorCodifferentEquiv_tmul_coe]

end ArakelovGeometry.NumberFieldCodifferentTensorDual

namespace ArakelovGeometry.NormFamily

open AdelicStructure NumberFieldCodifferentDual NumberFieldCodifferentTensorDual
  NumberFieldIntegralTraceDual

variable {K E : Type*} [Field K] [NumberField K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}

/-- Tensor–Hom duality on the actual dominated pure global ball. -/
def globalUnitBallTensorCodifferentEquiv
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) [hdom : ξ.IsDominated]
    [hξ : ξ.IsUltrametricAtFinitePlaces] [hpure : ξ.IsPureAtFinitePlaces] :
    codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) (ξ.globalUnitBallModule) ≃ₗ[𝓞 K]
      ((ξ.globalUnitBallModule) →ₗ[𝓞 K] codifferentModule K) :=
  tensorCodifferentEquiv (ξ.globalUnitBallModule)
    (hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure).1

@[simp]
theorem globalUnitBallTensorCodifferentEquiv_tmul_apply
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [ξ.IsDominated] [ξ.IsUltrametricAtFinitePlaces] [ξ.IsPureAtFinitePlaces]
    (a : codifferentModule K) (φ : Module.Dual (𝓞 K) (ξ.globalUnitBallModule))
    (m : ξ.globalUnitBallModule) :
    ξ.globalUnitBallTensorCodifferentEquiv (a ⊗ₜ[𝓞 K] φ) m = φ m • a :=
  tensorCodifferentEquiv_tmul_apply _ _ a φ m

/-- The original trace-integral dual of the pure global ball as an actual tensor. -/
def globalUnitBallTraceTensorEquiv
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) [hdom : ξ.IsDominated]
    [hξ : ξ.IsUltrametricAtFinitePlaces] [hpure : ξ.IsPureAtFinitePlaces] :
    codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) (ξ.globalUnitBallModule) ≃ₗ[𝓞 K]
      integralTraceDual (ξ.globalUnitBallModule) :=
  let hm := hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure
  traceTensorEquiv (ξ.globalUnitBallModule) hm.1 hm.2.2

@[simp]
theorem globalUnitBallTraceTensorEquiv_tmul_apply
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [ξ.IsDominated] [ξ.IsUltrametricAtFinitePlaces] [ξ.IsPureAtFinitePlaces]
    (a : codifferentModule K) (φ : Module.Dual (𝓞 K) (ξ.globalUnitBallModule))
    (m : ξ.globalUnitBallModule) :
    (ξ.globalUnitBallTraceTensorEquiv (a ⊗ₜ[𝓞 K] φ)).1 (m : E) =
      algebraMap (𝓞 K) K (φ m) * (a : K) :=
  traceTensorEquiv_tmul_apply _ _ _ a φ m

/-- The actual integer trace dual of the original pure global ball. -/
def globalUnitBallIntegerTensorEquiv
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) [hdom : ξ.IsDominated]
    [hξ : ξ.IsUltrametricAtFinitePlaces] [hpure : ξ.IsPureAtFinitePlaces] :
    codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) (ξ.globalUnitBallModule) ≃ₗ[ℤ]
      Module.Dual ℤ (ξ.globalUnitBallModule) :=
  let hm := hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure
  integerTensorEquiv (ξ.globalUnitBallModule) hm.1 hm.2.2

@[simp]
theorem globalUnitBallIntegerTensorEquiv_tmul_apply
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [ξ.IsDominated] [ξ.IsUltrametricAtFinitePlaces] [ξ.IsPureAtFinitePlaces]
    (a : codifferentModule K) (φ : Module.Dual (𝓞 K) (ξ.globalUnitBallModule))
    (m : ξ.globalUnitBallModule) :
    (ξ.globalUnitBallIntegerTensorEquiv (a ⊗ₜ[𝓞 K] φ) m : ℚ) =
      Algebra.trace ℚ K (algebraMap (𝓞 K) K (φ m) * (a : K)) :=
  integerTensorEquiv_tmul_apply _ _ _ a φ m

end ArakelovGeometry.NormFamily
