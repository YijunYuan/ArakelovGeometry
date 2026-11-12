/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

import ArakelovGeometry

/-!
# Norm-family construction interfaces

Run with `lake env lean test/ObjectAPI.lean` after `lake build`.
These examples select different norm families on the same vector space explicitly,
infer their property assumptions, and exercise preservation through tensor and subspace operations.
-/

open ArakelovGeometry
open scoped NumberField TensorProduct

-- Direct `lake env lean` invocations need the same synthesis depth as `lakefile.toml`.
set_option maxSynthPendingDepth 3

noncomputable section

universe u v

variable {K : Type u} {E : Type (max u v)} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

section Hermitian

variable {S : AdelicStructure K} (ξ η : NormFamily S E)
  [hS : S.IsArchimedeanNormalized] [ξ.IsHermitian] [η.IsHermitian]

example (ω : S.Ωinf) (x y : (S.ϕ ω.val).Completion ⊗[K] E) :
    (S.ϕ ω.val).Completion × (S.ϕ ω.val).Completion :=
  (ξ.archimedeanInner ω x y, η.archimedeanInner ω x y)

example {ι : Type*} [Fintype ι] (b : Module.Basis ι K E)
    (ω : S.Ωinf) (σ : (S.ϕ ω.val).Completion →+* ℂ) : Matrix ι ι ℂ × Matrix ι ι ℂ :=
  (ξ.archimedeanGram b ω σ, η.archimedeanGram b ω σ)

example (ω : S.Ω) (hω : ω ∈ S.Ωinf) :
    letI := hS ω hω
    letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    letI := ξ.fibreNormedAddCommGroup ω
    letI := ξ.fibreNormedSpace ω
    InnerProductSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E) :=
  ξ.fiberInnerProductSpace ω hω

example : ∀ i, (NormFamily.tensorPairFactors ξ η i).IsHermitian := inferInstance

example : NormFamily S (⨂[K] i, BinaryTensorFactors E E i) :=
  NormFamily.orthogonalTensor (NormFamily.tensorPairFactors ξ η)

example [ξ.IsDominated] [η.IsDominated] :
    (NormFamily.orthogonalTensor (NormFamily.tensorPairFactors ξ η)).IsStronglyDominated :=
  inferInstance

example [S.HasMeasurableBase] [ξ.IsMeasurable] [η.IsMeasurable] :
    ((ξ.dual ⊗ʰ η) ⊗ʰ ξ).IsMeasurable := inferInstance

example [S.HasMeasurableBase] (hξ : ξ.IsMeasurable) (hη : η.IsMeasurable) :
    (ξ ⊗ʰ η).IsMeasurable := hξ.orthogonalTensorPair hη

end Hermitian

section Arithmetic

variable [NumberField K]
  (ξ : NormFamily (AdelicStructure.normalizedNumberFieldAdelicStructure K) E)
  [ξ.IsUltrametric]

example : (NumberFieldTraceDualizingLine.dualizingLine K).IsLine := inferInstance

example : (NumberFieldTraceDualizingLine.dualizingLine K).IsHermitian := inferInstance

example [ξ.HasFiniteNormExceptions] (P : Submodule K E) :
    (ξ.restrict P).HasFiniteNormExceptions := inferInstance

example [ξ.HasFiniteNormExceptions] :
    K ⊗[𝓞 K] ξ.globalUnitBallModule ≃ₗ[K] E := ξ.normalizedGlobalGenericFiberEquiv

example [ξ.IsDominated] [ξ.IsPureAtFinitePlaces] :
    Module.Basis (Fin (Module.finrank ℚ K * Module.finrank K E)) ℤ ξ.globalUnitBallModule :=
  ξ.normalizedGlobalUnitBallIntegerBasis

example [ξ.IsDominated] [ξ.IsPureAtFinitePlaces] :
    letI : Module ℚ E := Module.compHom E (algebraMap ℚ K)
    Module.Basis (Fin (Module.finrank ℚ K * Module.finrank K E)) ℚ E :=
  ξ.normalizedGlobalUnitBallRationalBasis

end Arithmetic
