/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

import ArakelovGeometry

/-!
# Property typeclass regression checks

Run with `lake env lean test/Typeclasses.lean` after `lake build`.
These examples exercise inference through public bundle constructors, including
nested constructions and the background conditions on the adelic structure.
-/

open ArakelovGeometry
open scoped TensorProduct

noncomputable section

universe w w'

variable {K : Type*} [Field K] {S : AdelicStructure K}
  {E : Type w} {F : Type w'} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  (V : AdelicVectorBundle.{w} S) (W : AdelicVectorBundle.{w'} S)

example [DiscreteMeasurableSpace S.Ω] : S.HasMeasurableBase := inferInstance
example [S.HasCommonCountableDenseSubfield] : S.HasMeasurableBase := inferInstance
example [S.HasCommonCountableDenseSubfield] : S.HasOrdinaryBase := inferInstance
example [S.HasOrdinaryBase] : S.HasRegularBase := inferInstance
example [S.HasOnlyFinitePlaces] : S.IsArchimedeanNormalized := inferInstance
example [MeasurableSingletonClass S.Ω] [S.HasPositiveAtoms] [S.HasOnlyFinitePlaces] :
    S.HasRegularBase := inferInstance

example : V.toNormFamily.IsMeasurable := inferInstance
example : V.toNormFamily.dual.IsMeasurable := inferInstance
example : V.toNormFamily.IsDominated := inferInstance
example : (V.toNormFamily.injectiveTensorPair W.toNormFamily).IsUltrametric := inferInstance
example [V.IsLine] : V.IsStronglyAdelic := inferInstance
example [V.IsLine] : V.dualLine.IsLine := inferInstance

section Hermitian

variable [S.HasMeasurableBase] [S.IsArchimedeanNormalized] [V.IsHermitian] [W.IsHermitian]

example : V.IsStronglyAdelic := inferInstance
example : V.toNormFamily.IsUltrametric := inferInstance
example : (V ⊗ʰ W) = V.orthogonalTensorPair W := rfl
example : (V ⊗ʰ W).IsHermitian := inferInstance
example : (V ⊗ʰ W ⊗ʰ V).IsHermitian := inferInstance
example : (V ⊗ʰ W).toNormFamily = V.toNormFamily ⊗ʰ W.toNormFamily := rfl

example : True := by
  let T := V ⊗ʰ W
  have : T.IsHermitian := inferInstance
  trivial

example : (V.orthogonalTensorPair W).IsStronglyAdelic := inferInstance
example : ((V.orthogonalTensorPair W).orthogonalTensorPair V).IsHermitian := inferInstance
example (P : Submodule K V) : (V.restrictOfMeasurableBase P).IsHermitian := inferInstance
example (P : Submodule K V) : (V.quotientOfMeasurableBase P).IsHermitian := inferInstance
example : V.dualOfMeasurableBase.IsHermitian := inferInstance
example : V.determinantOfMeasurableBase.IsLine := inferInstance

end Hermitian

example [S.IsArchimedeanNormalized] (ξ : NormFamily S E) (η : NormFamily S F)
    [ξ.IsHermitian] [η.IsHermitian] : (ξ ⊗ʰ η) = ξ.orthogonalTensorPair η := rfl

example [S.IsArchimedeanNormalized] (ξ : NormFamily S E) (η : NormFamily S F)
    [ξ.IsHermitian] [η.IsHermitian] : (ξ ⊗ʰ η ⊗ʰ ξ).IsHermitian := inferInstance

example [S.HasMeasurableBase] [S.IsArchimedeanNormalized] [V.IsStronglyAdelic]
    (P : Submodule K V) : (V.restrictOfMeasurableBase P).IsStronglyAdelic := inferInstance

example [S.HasMeasurableBase] [S.IsArchimedeanNormalized] [V.IsStronglyAdelic]
    (P : Submodule K V) : (V.quotientOfMeasurableBase P).IsStronglyAdelic := inferInstance

example [S.IsProper] [S.HasMeasurableBase] [S.IsArchimedeanNormalized] [V.IsLine] :
    V.IsSemistable := inferInstance

example [S.IsProper] [S.HasMeasurableBase] [S.IsArchimedeanNormalized] [V.IsLine] :
    V.IsMeanSlopeSemistable := inferInstance

section ScalarExtension

variable {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

example [S.IsArchimedeanNormalized] :
    (S.algebraicExtension L).IsArchimedeanNormalized := inferInstance

example [S.HasOnlyFinitePlaces] :
    (S.algebraicExtension L).HasOnlyFinitePlaces := inferInstance

example [FiniteDimensional K L] [S.HasCommonCountableDenseSubfield] :
    (S.algebraicExtension L).HasCommonCountableDenseSubfield := inferInstance

example [FiniteDimensional K L] [MeasurableSingletonClass S.Ω] [S.HasPositiveAtoms] :
    (S.algebraicExtension L).HasPositiveAtoms := inferInstance

end ScalarExtension

section IndexedTensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {G : ι → Type w}
  [∀ i, AddCommGroup (G i)] [∀ i, Module K (G i)] [∀ i, FiniteDimensional K (G i)]
  (U : ι → AdelicVectorBundle.{w} S) [S.IsArchimedeanNormalized]

example [S.HasMeasurableBase] [∀ i, (U i).IsHermitian] :
    (AdelicVectorBundle.orthogonalTensorOfMeasurableBase U).IsHermitian := inferInstance

example [∀ i, (U i).IsLine] :
    (AdelicVectorBundle.orthogonalTensorLines U).IsLine := inferInstance

end IndexedTensor

section Arithmetic

variable [NumberField K]
  (ξ : NormFamily (AdelicStructure.normalizedNumberFieldAdelicStructure K) V)

example [ξ.IsPureAtFinitePlaces] (P : Submodule K V) :
    (ξ.restrict P).IsPureAtFinitePlaces := inferInstance

example [ξ.IsPureAtFinitePlaces] : ξ.dual.IsPureAtFinitePlaces := inferInstance

example [ξ.IsPureAtFinitePlaces] (P : Submodule K V) :
    (ξ.quotient P).IsPureAtFinitePlaces := inferInstance

example [ξ.IsClassical] : ξ.IsStronglyDominated := inferInstance

example [ξ.IsClassical] : ξ.IsDominated := inferInstance

end Arithmetic
