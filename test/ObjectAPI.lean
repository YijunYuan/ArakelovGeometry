/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

import ArakelovGeometry

/-!
# Bundled vector spaces and norm-family construction interfaces

Run with `lake env lean test/ObjectAPI.lean` after `lake build`.
These examples use bundles as vector spaces, retain the carriers of their constructions,
and select different norm families on a fixed vector space explicitly. They also infer property
assumptions and exercise preservation through tensor and subspace operations.
-/

open ArakelovGeometry
open scoped NumberField TensorProduct

-- Direct `lake env lean` invocations need the same synthesis depth as `lakefile.toml`.
set_option maxSynthPendingDepth 3

noncomputable section

universe u v

section Bundled

variable (C : AdelicCurve) (V : C.AdelicVectorBundle) (W : C.AdelicVectorBundle)

example (x y : V) (a : C.K) : V := a • x + y
example (f : V →ₗ[C.K] W) (x : V) : W := f x
example : FiniteDimensional C.K V := inferInstance
example : V.toNormFamily.IsAdelic := inferInstance
example : V.toNormFamily.toAdelicVectorBundle = V := rfl
example : V.rank = Module.finrank C.K V := rfl

example [C.IsProper] [C.AS.HasMeasurableBase] [C.AS.IsArchimedeanNormalized] : ℝ :=
  V.degree

example [C.AS.HasMeasurableBase] (P : Submodule C.K V) :
    (V.restrictOfMeasurableBase P).carrier = P := rfl

example [C.AS.HasMeasurableBase] (P : Submodule C.K V) :
    (V.quotientOfMeasurableBase P).carrier = (V ⧸ P) := rfl

example [C.AS.HasMeasurableBase] [C.AS.IsArchimedeanNormalized]
    [V.IsHermitian] [W.IsHermitian] :
    (V ⊗ʰ W).carrier = (V ⊗[C.K] W) := rfl

end Bundled

section CarrierUniverse

universe w
variable {K : Type u} [Field K] (S : AdelicStructure.{u, v} K)

example (V : AdelicVectorBundle.{w} S) : Type w := V
example (C : AdelicCurve.{u, v}) (V : C.AdelicVectorBundle.{w}) : Type w := V

end CarrierUniverse

section IndependentUniverses

universe w₁ w₂ w₃
variable (C : AdelicCurve.{u, v})
  (V : C.AdelicVectorBundle.{w₁}) (W : C.AdelicVectorBundle.{w₂})
  (Z : C.AdelicVectorBundle.{w₃})
  [C.AS.HasMeasurableBase] [C.AS.IsArchimedeanNormalized]

example : (V.injectiveTensorPair W).carrier = (V ⊗[C.K] W) := rfl
example : (V.mixedTensorPair W).carrier = (V ⊗[C.K] W) := rfl

example [V.IsHermitian] [W.IsHermitian] [Z.IsHermitian] :
    (V ⊗ʰ (W ⊗ʰ Z)).carrier = (V ⊗[C.K] (W ⊗[C.K] Z)) := rfl

example (f : V →ₗ[C.K] W) : EReal := V.mapHeight W f

example [C.IsProper] (e : V ≃ₗ[C.K] W)
    (he : ∀ ω x, W.norm ω (e.toLinearMap.baseChange (C.AS.ϕ ω).Completion x) = V.norm ω x) :
    V.degree = W.degree := V.degree_eq_of_completed_isometry W e he

example [C.IsProper] [V.IsHermitian] [W.IsHermitian] :
    (V ⊗ʰ W).degree = (W.rank : ℝ) * V.degree + (V.rank : ℝ) * W.degree :=
  V.degree_orthogonalTensorPair W

example [C.IsProper] [V.IsHermitian] [W.IsHermitian]
    (f : V →ₗ[C.K] W) (hf : f ≠ 0) (t : ℝ) :
    (V.hermitianHNFiltration t).map f ≤
      W.hermitianHNFiltration (t - (V.mapHeight W f).toReal) :=
  V.map_hermitianHNFiltration_le W f hf t

end IndependentUniverses

variable {K : Type u} {E : Type (max u v)} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

section Packaging

variable {S : AdelicStructure K} (ξ η : NormFamily S E) [ξ.IsAdelic] [η.IsAdelic]

example : S.toAdelicCurve.AdelicVectorBundle := ξ.toAdelicVectorBundle
example : (ξ.toAdelicVectorBundle : Type (max u v)) = E := rfl
example : ξ.toAdelicVectorBundle.toNormFamily = ξ := rfl
example : η.toAdelicVectorBundle.toNormFamily = η := rfl

example : AdelicVectorBundle S where
  carrier := E
  toNormFamily := ξ

end Packaging

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

example : NormFamily S (⨂[K] i, LiftedTensorFactors E E i) :=
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
