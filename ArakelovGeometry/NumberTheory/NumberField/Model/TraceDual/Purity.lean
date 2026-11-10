/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Model.TraceDual.Projective.Generic
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Purity.Dual
import Mathlib.Topology.Sheaves.Init

/-! # Actual finite-place purity of the original prescribed trace-dual metric -/

@[expose] public section

noncomputable section
open NumberField
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldClassicalTraceDualPurity

open AdelicStructure NumberFieldProjectiveGeneric NumberFieldCodifferentDual
  NumberFieldProjectiveTraceDualGeneric NumberFieldProjectiveTraceDualMetric
  NumberFieldTraceDualizingLine

universe u
variable {K : Type u} [Field K] [NumberField K]
  (M : Type u) [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

omit [Module.Projective (𝓞 K) M] in
/-- The prescribed trace tensor has the actual scalar-line norm product on
every completed fibre after the canonical tensor-unit insertion. -/
theorem prescribedTraceDualFamily_norm_tensorUnit
    {η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)}
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (z : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K]
      Module.Dual K (K ⊗[𝓞 K] M)) :
    (prescribedTraceDualFamily hη).norm ω
      (LinearEquiv.baseChange K ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion
        _ _ (TensorProduct.rid K (Module.Dual K (K ⊗[𝓞 K] M))).symm z) =
      (dualizingLine K).norm ω
        ((1 : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion) ⊗ₜ[K] (1 : K)) *
          η.dual.norm ω z := by
  rw [prescribedTraceDualFamily, tensorUnitBaseChange_symm]
  exact (NormFamily.orthogonalTensorPair_norm_tmul_completed η.dual (dualizingLine K).toNormFamily
    normalizedNumberFieldArchimedeanCompletions hη.dual (dualizingLine_isHermitian K) ω z _).trans
      (mul_comm _ _)

/-- The actual original prescribed trace metric is the dual norm times the
actual trace-line unit norm, for every place and every completed vector. -/
theorem originalPrescribedTraceDualFamily_norm
    {η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)}
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (z : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K]
      (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M))) :
    (originalPrescribedTraceDualFamily M hη).norm ω z =
      (dualizingLine K).norm ω
        ((1 : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion) ⊗ₜ[K] (1 : K)) *
          η.dual.norm ω
            (LinearEquiv.baseChange K ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion
              _ _ ((traceTensorGenericPairEquiv M).trans
                (TensorProduct.rid K (Module.Dual K (K ⊗[𝓞 K] M)))) z) := by
  let F := ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion
  let e := LinearEquiv.baseChange K F _ _ (TensorProduct.rid K (Module.Dual K (K ⊗[𝓞 K] M)))
  let t := LinearEquiv.baseChange K F _ _ (traceTensorGenericPairEquiv M) z
  have h := prescribedTraceDualFamily_norm_tensorUnit M hη ω (e t)
  change (prescribedTraceDualFamily hη).norm ω (e.symm (e t)) =
    (dualizingLine K).norm ω ((1 : F) ⊗ₜ[K] (1 : K)) * η.dual.norm ω (e t) at h
  erw [e.symm_apply_apply] at h
  erw [LinearEquiv.baseChange_trans]
  exact h

/-- The original prescribed trace metric is pure at finite places whenever
the original metric is pure, including the zero-rank module. -/
theorem originalPrescribedTraceDualFamily_isPureAtFinitePlaces
    {η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)}
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (hpη : η.IsPureAtFinitePlaces) :
    (originalPrescribedTraceDualFamily M hη).IsPureAtFinitePlaces := by
  intro ω hω z hz
  let F := ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion
  let e := LinearEquiv.baseChange K F _ _ ((traceTensorGenericPairEquiv M).trans
    (TensorProduct.rid K (Module.Dual K (K ⊗[𝓞 K] M))))
  have he : e z ≠ 0 := fun h => hz (e.injective (h.trans e.map_zero.symm))
  have hunit : (1 : F) ⊗ₜ[K] (1 : K) ≠ 0 := by
    intro h
    have hh := congrArg (TensorProduct.AlgebraTensorModule.rid K F F) h
    simp at hh
  obtain ⟨a, ha, hNa⟩ := dualizingLine_isPureAtFinitePlaces K ω hω _ hunit
  obtain ⟨b, hb, hNb⟩ := hpη.dual ω hω (e z) he
  refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
  rw [norm_mul, ← hNa, ← hNb]
  exact originalPrescribedTraceDualFamily_norm M hη ω z

end ArakelovGeometry.NumberFieldClassicalTraceDualPurity
