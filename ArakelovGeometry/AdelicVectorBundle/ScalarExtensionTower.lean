/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension

/-!
# Transitivity of norm families under scalar extension

Actual completed-fibre tower identities for the scalar-extension norms.
-/

open scoped TensorProduct

namespace AbsoluteValue

/-- The actual completed field of a non-Archimedean absolute value has an
ultrametric norm. -/
theorem isUltrametricDist_completion {k : Type*} [Field k]
    (v : AbsoluteValue k ℝ) (hv : IsNonarchimedean v) :
    IsUltrametricDist v.Completion := by
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
  intro a b
  refine UniformSpace.Completion.induction_on₂ a b ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro c d
    simpa only [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe]
      using (show ‖c + d‖ ≤ max ‖c‖ ‖d‖ from hv c.ofAbs d.ofAbs)

end AbsoluteValue

namespace ArakelovGeometry

noncomputable section

universe u v w wE

variable {K : Type u} [Field K] {L : Type w} [Field L] [Algebra K L]
  {E : Type wE} [AddCommGroup E] [Module K E]

/-- The direct extension place attached to a place in a successive field
extension. Its absolute value is unchanged. -/
def scalarExtensionTowerPlace {S : AdelicStructure.{u, v} K}
    [Algebra.IsAlgebraic K L] {M : Type*} [Field M]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension L) M) :
    AdelicStructure.ParameterSpaceExtension S M where
  base := x.base.base
  abv := x.abv
  restrict_eq := by
    ext a
    change x.abv (algebraMap K M a) = S.ϕ x.base.base a
    rw [IsScalarTower.algebraMap_apply K L M]
    exact (congrArg (fun f : AbsoluteValue L ℝ ↦ f (algebraMap K L a)) x.restrict_eq).trans
      (congrArg (fun f : AbsoluteValue K ℝ ↦ f a) x.base.restrict_eq)


namespace NormFamily

variable {S : AdelicStructure.{u, v} K} [FiniteDimensional K E]
  (ξ : NormFamily S E) [Algebra.IsAlgebraic K L]

/-- Pointwise evaluation of the actual projective scalar-extension family in
the canonical completed-fibre coordinates. -/
theorem projectiveScalarExtension_norm_apply
    (x : AdelicStructure.ParameterSpaceExtension S L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    let := ξ.fibreNormedAddCommGroup x.base
    let := ξ.fibreNormedSpace x.base
    (ξ.projectiveScalarExtension (L := L)).norm x z =
      scalarExtensionProjectiveSeminorm
        (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq z) := rfl

/-- Pointwise evaluation of the actual injective scalar-extension family in
the canonical completed-fibre coordinates. -/
theorem injectiveScalarExtension_norm_apply
    (x : AdelicStructure.ParameterSpaceExtension S L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    let := ξ.fibreNormedAddCommGroup x.base
    let := ξ.fibreNormedSpace x.base
    (ξ.injectiveScalarExtension (L := L)).norm x z =
      scalarExtensionInjectiveSeminorm
        (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq z) := rfl

section Tower

variable {M : Type*} [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- The projective norm on the completed first extension composes with a further
completed extension through the canonical scalar-extension map. -/
theorem projectiveScalarExtension_completed_trans
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension L) M) :
    let v₀ := S.ϕ x.base.base
    let w₀ := x.base.abv
    let u₀ := x.abv
    let hvw : w₀.restriction K = v₀ := x.base.restrict_eq
    let hwu : u₀.restriction L = w₀ := x.restrict_eq
    let hvu : u₀.restriction K = v₀ := (scalarExtensionTowerPlace x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq v₀ w₀ hvw
    let := AbsoluteValue.normedAlgebraCompletionOfEq w₀ u₀ hwu
    let := AbsoluteValue.normedAlgebraCompletionOfEq v₀ u₀ hvu
    let := AbsoluteValue.isScalarTower_completionOfEq_tower v₀ w₀ u₀ hvw hwu hvu
    let : NormedAddCommGroup (v₀.Completion ⊗[K] E) := ξ.fibreNormedAddCommGroup x.base.base
    let : NormedSpace v₀.Completion (v₀.Completion ⊗[K] E) := ξ.fibreNormedSpace x.base.base
    let η := ξ.projectiveScalarExtension (L := L)
    let : NormedAddCommGroup (w₀.Completion ⊗[L] (L ⊗[K] E)) :=
      η.fibreNormedAddCommGroup x.base
    let : NormedSpace w₀.Completion (w₀.Completion ⊗[L] (L ⊗[K] E)) :=
      η.fibreNormedSpace x.base
    ∀ y : u₀.Completion ⊗[w₀.Completion] (w₀.Completion ⊗[L] (L ⊗[K] E)),
    scalarExtensionProjectiveSeminorm (k := w₀.Completion) (L := u₀.Completion) y =
      scalarExtensionProjectiveSeminorm (k := v₀.Completion) (L := u₀.Completion)
        (TensorProduct.AlgebraTensorModule.cancelBaseChange
          v₀.Completion w₀.Completion u₀.Completion u₀.Completion (v₀.Completion ⊗[K] E)
          (LinearEquiv.baseChange w₀.Completion u₀.Completion _ _
            (completedScalarExtensionEquiv E v₀ w₀ hvw) y)) := by
  intro v₀ w₀ u₀ hvw hwu hvu aVW aWU aVU tVWU nV nsV η nW nsW y
  let := aVW
  let := aWU
  let := aVU
  let := tVWU
  let := nV
  let := nsV
  let := nW
  let := nsW
  exact scalarExtensionProjectiveSeminorm_comp_equiv
    (k := v₀.Completion) (L := w₀.Completion) (M := u₀.Completion)
    (completedScalarExtensionEquiv E v₀ w₀ hvw)
    (fun a ↦ ξ.projectiveScalarExtension_norm_apply x.base a) y


/-- The actual completed-fibre scalar-extension map carries the iterated
projective norm to the direct one, before evaluating the global family. -/
theorem projectiveScalarExtension_completed_trans_apply
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension L) M)
    (z : x.abv.Completion ⊗[M] (M ⊗[L] (L ⊗[K] E))) :
    let v₀ := S.ϕ x.base.base
    let w₀ := x.base.abv
    let u₀ := x.abv
    let hvw : w₀.restriction K = v₀ := x.base.restrict_eq
    let hwu : u₀.restriction L = w₀ := x.restrict_eq
    let hvu : u₀.restriction K = v₀ := (scalarExtensionTowerPlace x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq v₀ w₀ hvw
    let := AbsoluteValue.normedAlgebraCompletionOfEq w₀ u₀ hwu
    let := AbsoluteValue.normedAlgebraCompletionOfEq v₀ u₀ hvu
    let := AbsoluteValue.isScalarTower_completionOfEq_tower v₀ w₀ u₀ hvw hwu hvu
    let : NormedAddCommGroup (v₀.Completion ⊗[K] E) := ξ.fibreNormedAddCommGroup x.base.base
    let : NormedSpace v₀.Completion (v₀.Completion ⊗[K] E) := ξ.fibreNormedSpace x.base.base
    let η := ξ.projectiveScalarExtension (L := L)
    let : NormedAddCommGroup (w₀.Completion ⊗[L] (L ⊗[K] E)) :=
      η.fibreNormedAddCommGroup x.base
    let : NormedSpace w₀.Completion (w₀.Completion ⊗[L] (L ⊗[K] E)) :=
      η.fibreNormedSpace x.base
    scalarExtensionProjectiveSeminorm (k := w₀.Completion) (L := u₀.Completion)
        (completedScalarExtensionEquiv (L ⊗[K] E) w₀ u₀ hwu z) =
      scalarExtensionProjectiveSeminorm (k := v₀.Completion) (L := u₀.Completion)
        (completedScalarExtensionEquiv E v₀ u₀ hvu
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E).toLinearMap.baseChange
            u₀.Completion z)) := by
  intro v₀ w₀ u₀ hvw hwu hvu aVW aWU aVU tVWU nV nsV η nW nsW
  let := aVW
  let := aWU
  let := aVU
  let := tVWU
  let := nV
  let := nsV
  let := nW
  let := nsW
  exact (ξ.projectiveScalarExtension_completed_trans x
    (completedScalarExtensionEquiv (L ⊗[K] E) w₀ u₀ hwu z)).trans
      (congrArg (scalarExtensionProjectiveSeminorm
        (k := v₀.Completion) (L := u₀.Completion))
        (completedScalarExtensionEquiv_tower E v₀ w₀ u₀ hvw hwu hvu z))

/-- The injective norm on the completed first extension composes with a further
completed extension through the canonical scalar-extension map. -/
theorem injectiveScalarExtension_completed_trans_of_norm_eq
    (η : NormFamily (S.algebraicExtension L) (L ⊗[K] E))
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension L) M)
    (hx : IsNonarchimedean x.abv)
    (hη : ∀ a, η.norm x.base a = (ξ.injectiveScalarExtension (L := L)).norm x.base a) :
    let v₀ := S.ϕ x.base.base
    let w₀ := x.base.abv
    let u₀ := x.abv
    let hvw : w₀.restriction K = v₀ := x.base.restrict_eq
    let hwu : u₀.restriction L = w₀ := x.restrict_eq
    let hvu : u₀.restriction K = v₀ := (scalarExtensionTowerPlace x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq v₀ w₀ hvw
    let := AbsoluteValue.normedAlgebraCompletionOfEq w₀ u₀ hwu
    let := AbsoluteValue.normedAlgebraCompletionOfEq v₀ u₀ hvu
    let := AbsoluteValue.isScalarTower_completionOfEq_tower v₀ w₀ u₀ hvw hwu hvu
    let : NormedAddCommGroup (v₀.Completion ⊗[K] E) := ξ.fibreNormedAddCommGroup x.base.base
    let : NormedSpace v₀.Completion (v₀.Completion ⊗[K] E) := ξ.fibreNormedSpace x.base.base
    let finW : FiniteDimensional w₀.Completion (w₀.Completion ⊗[L] (L ⊗[K] E)) := inferInstance
    let nW : NormedAddCommGroup (w₀.Completion ⊗[L] (L ⊗[K] E)) :=
      η.fibreNormedAddCommGroup x.base
    let nsW : NormedSpace w₀.Completion (w₀.Completion ⊗[L] (L ⊗[K] E)) :=
      η.fibreNormedSpace x.base
    let : Module w₀.Completion (w₀.Completion ⊗[L] (L ⊗[K] E)) := nsW.toModule
    let : @FiniteDimensional w₀.Completion (w₀.Completion ⊗[L] (L ⊗[K] E))
      (inferInstance : NormedField w₀.Completion).toField.toDivisionRing
      nW.toAddCommGroup nsW.toModule := finW
    ∀ y : u₀.Completion ⊗[w₀.Completion] (w₀.Completion ⊗[L] (L ⊗[K] E)),
    scalarExtensionInjectiveSeminorm (k := w₀.Completion) (L := u₀.Completion) y =
      scalarExtensionInjectiveSeminorm (k := v₀.Completion) (L := u₀.Completion)
        (TensorProduct.AlgebraTensorModule.cancelBaseChange
          v₀.Completion w₀.Completion u₀.Completion u₀.Completion (v₀.Completion ⊗[K] E)
          (LinearEquiv.baseChange w₀.Completion u₀.Completion _ _
            (completedScalarExtensionEquiv E v₀ w₀ hvw) y)) := by
  intro v₀ w₀ u₀ hvw hwu hvu aVW aWU aVU tVWU nV nsV finW nW nsW modW finW' y
  let := aVW
  let := aWU
  let := aVU
  let := tVWU
  let := nV
  let := nsV
  let := modW
  let := finW'
  let := nW
  let := nsW
  let := AbsoluteValue.isUltrametricDist_completion u₀ hx
  exact scalarExtensionInjectiveSeminorm_comp_equiv
    (k := v₀.Completion) (L := w₀.Completion) (M := u₀.Completion)
    (completedScalarExtensionEquiv E v₀ w₀ hvw)
    (fun a ↦ (hη a).trans (ξ.injectiveScalarExtension_norm_apply x.base a)) y


/-- The actual completed-fibre scalar-extension map carries the iterated
injective norm to the direct one, before evaluating the global family. -/
theorem injectiveScalarExtension_completed_trans_apply_of_norm_eq
    (η : NormFamily (S.algebraicExtension L) (L ⊗[K] E))
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension L) M)
    (hx : IsNonarchimedean x.abv)
    (hη : ∀ a, η.norm x.base a = (ξ.injectiveScalarExtension (L := L)).norm x.base a)
    (z : x.abv.Completion ⊗[M] (M ⊗[L] (L ⊗[K] E))) :
    let v₀ := S.ϕ x.base.base
    let w₀ := x.base.abv
    let u₀ := x.abv
    let hvw : w₀.restriction K = v₀ := x.base.restrict_eq
    let hwu : u₀.restriction L = w₀ := x.restrict_eq
    let hvu : u₀.restriction K = v₀ := (scalarExtensionTowerPlace x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq v₀ w₀ hvw
    let := AbsoluteValue.normedAlgebraCompletionOfEq w₀ u₀ hwu
    let := AbsoluteValue.normedAlgebraCompletionOfEq v₀ u₀ hvu
    let := AbsoluteValue.isScalarTower_completionOfEq_tower v₀ w₀ u₀ hvw hwu hvu
    let : NormedAddCommGroup (v₀.Completion ⊗[K] E) := ξ.fibreNormedAddCommGroup x.base.base
    let : NormedSpace v₀.Completion (v₀.Completion ⊗[K] E) := ξ.fibreNormedSpace x.base.base
    let finW : FiniteDimensional w₀.Completion (w₀.Completion ⊗[L] (L ⊗[K] E)) := inferInstance
    let nW : NormedAddCommGroup (w₀.Completion ⊗[L] (L ⊗[K] E)) :=
      η.fibreNormedAddCommGroup x.base
    let nsW : NormedSpace w₀.Completion (w₀.Completion ⊗[L] (L ⊗[K] E)) :=
      η.fibreNormedSpace x.base
    let : Module w₀.Completion (w₀.Completion ⊗[L] (L ⊗[K] E)) := nsW.toModule
    let : @FiniteDimensional w₀.Completion (w₀.Completion ⊗[L] (L ⊗[K] E))
      (inferInstance : NormedField w₀.Completion).toField.toDivisionRing
      nW.toAddCommGroup nsW.toModule := finW
    let p := scalarExtensionInjectiveSeminorm (k := w₀.Completion) (L := u₀.Completion)
      (E := w₀.Completion ⊗[L] (L ⊗[K] E))
    let q := scalarExtensionInjectiveSeminorm (k := v₀.Completion) (L := u₀.Completion)
      (E := v₀.Completion ⊗[K] E)
    p (completedScalarExtensionEquiv (L ⊗[K] E) w₀ u₀ hwu z) =
      q (completedScalarExtensionEquiv E v₀ u₀ hvu
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E).toLinearMap.baseChange
            u₀.Completion z)) := by
  intro v₀ w₀ u₀ hvw hwu hvu aVW aWU aVU tVWU nV nsV finW nW nsW modW finW' p q
  let := aVW
  let := aWU
  let := aVU
  let := tVWU
  let := nV
  let := nsV
  let := modW
  let := finW'
  let := nW
  let := nsW
  let := AbsoluteValue.isUltrametricDist_completion u₀ hx
  have ht := scalarExtensionInjectiveSeminorm_comp_equiv
    (k := v₀.Completion) (L := w₀.Completion) (M := u₀.Completion)
    (completedScalarExtensionEquiv E v₀ w₀ hvw)
    (fun a ↦ (hη a).trans (ξ.injectiveScalarExtension_norm_apply x.base a))
    (completedScalarExtensionEquiv (L ⊗[K] E) w₀ u₀ hwu z)
  exact ht.trans (congrArg q
    (completedScalarExtensionEquiv_tower E v₀ w₀ u₀ hvw hwu hvu z))

/-- The actual completed-fibre scalar-extension map carries the iterated
projective norm to the direct one, before evaluating the global family. -/
theorem projectiveScalarExtension_completed_trans_apply_of_norm_eq
    (η : NormFamily (S.algebraicExtension L) (L ⊗[K] E))
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension L) M)
    (hη : ∀ a, η.norm x.base a = (ξ.projectiveScalarExtension (L := L)).norm x.base a)
    (z : x.abv.Completion ⊗[M] (M ⊗[L] (L ⊗[K] E))) :
    let v₀ := S.ϕ x.base.base
    let w₀ := x.base.abv
    let u₀ := x.abv
    let hvw : w₀.restriction K = v₀ := x.base.restrict_eq
    let hwu : u₀.restriction L = w₀ := x.restrict_eq
    let hvu : u₀.restriction K = v₀ := (scalarExtensionTowerPlace x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq v₀ w₀ hvw
    let := AbsoluteValue.normedAlgebraCompletionOfEq w₀ u₀ hwu
    let := AbsoluteValue.normedAlgebraCompletionOfEq v₀ u₀ hvu
    let := AbsoluteValue.isScalarTower_completionOfEq_tower v₀ w₀ u₀ hvw hwu hvu
    let : NormedAddCommGroup (v₀.Completion ⊗[K] E) := ξ.fibreNormedAddCommGroup x.base.base
    let : NormedSpace v₀.Completion (v₀.Completion ⊗[K] E) := ξ.fibreNormedSpace x.base.base
    let : NormedAddCommGroup (w₀.Completion ⊗[L] (L ⊗[K] E)) :=
      η.fibreNormedAddCommGroup x.base
    let : NormedSpace w₀.Completion (w₀.Completion ⊗[L] (L ⊗[K] E)) :=
      η.fibreNormedSpace x.base
    scalarExtensionProjectiveSeminorm (k := w₀.Completion) (L := u₀.Completion)
        (completedScalarExtensionEquiv (L ⊗[K] E) w₀ u₀ hwu z) =
      scalarExtensionProjectiveSeminorm (k := v₀.Completion) (L := u₀.Completion)
        (completedScalarExtensionEquiv E v₀ u₀ hvu
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E).toLinearMap.baseChange
            u₀.Completion z)) := by
  intro v₀ w₀ u₀ hvw hwu hvu aVW aWU aVU tVWU nV nsV nW nsW
  let := aVW
  let := aWU
  let := aVU
  let := tVWU
  let := nV
  let := nsV
  let := nW
  let := nsW
  have ht := scalarExtensionProjectiveSeminorm_comp_equiv
    (k := v₀.Completion) (L := w₀.Completion) (M := u₀.Completion)
    (completedScalarExtensionEquiv E v₀ w₀ hvw)
    (fun a ↦ (hη a).trans (ξ.projectiveScalarExtension_norm_apply x.base a))
    (completedScalarExtensionEquiv (L ⊗[K] E) w₀ u₀ hwu z)
  exact ht.trans (congrArg (scalarExtensionProjectiveSeminorm
    (k := v₀.Completion) (L := u₀.Completion))
    (completedScalarExtensionEquiv_tower E v₀ w₀ u₀ hvw hwu hvu z))

variable [Algebra.IsAlgebraic L M]

/-- Projective norm families are transitive on the actual completed fibres
of a successive algebraic extension. -/
theorem projectiveScalarExtension_trans
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension L) M)
    (z : x.abv.Completion ⊗[M] (M ⊗[L] (L ⊗[K] E))) :
    let := Algebra.IsAlgebraic.trans K L M
    ((ξ.projectiveScalarExtension (L := L)).projectiveScalarExtension (L := M)).norm x z =
      (ξ.projectiveScalarExtension (L := M)).norm (scalarExtensionTowerPlace x)
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E).toLinearMap.baseChange
          x.abv.Completion z) := by
  let := Algebra.IsAlgebraic.trans K L M
  exact ((ξ.projectiveScalarExtension (L := L)).projectiveScalarExtension_norm_apply x z).trans
    ((ξ.projectiveScalarExtension_completed_trans_apply x z).trans
      (ξ.projectiveScalarExtension_norm_apply (scalarExtensionTowerPlace x) _).symm)

/-- Injective norm families are transitive on the actual completed fibres
of a successive algebraic extension at a non-Archimedean place. -/
theorem injectiveScalarExtension_trans
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension L) M)
    (hx : IsNonarchimedean x.abv)
    (z : x.abv.Completion ⊗[M] (M ⊗[L] (L ⊗[K] E))) :
    let := Algebra.IsAlgebraic.trans K L M
    ((ξ.injectiveScalarExtension (L := L)).injectiveScalarExtension (L := M)).norm x z =
      (ξ.injectiveScalarExtension (L := M)).norm (scalarExtensionTowerPlace x)
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E).toLinearMap.baseChange
          x.abv.Completion z) := by
  let := Algebra.IsAlgebraic.trans K L M
  exact ((ξ.injectiveScalarExtension (L := L)).injectiveScalarExtension_norm_apply x z).trans
    ((ξ.injectiveScalarExtension_completed_trans_apply_of_norm_eq
      (ξ.injectiveScalarExtension (L := L)) x hx (fun _ ↦ rfl) z).trans
      (ξ.injectiveScalarExtension_norm_apply (scalarExtensionTowerPlace x) _).symm)

/-- A first-step fibre with the projective extension norm has the same further
projective extension as the original family extended directly. -/
theorem projectiveScalarExtension_trans_of_norm_eq
    (η : NormFamily (S.algebraicExtension L) (L ⊗[K] E))
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension L) M)
    (hη : ∀ a, η.norm x.base a = (ξ.projectiveScalarExtension (L := L)).norm x.base a)
    (z : x.abv.Completion ⊗[M] (M ⊗[L] (L ⊗[K] E))) :
    let := Algebra.IsAlgebraic.trans K L M
    (η.projectiveScalarExtension (L := M)).norm x z =
      (ξ.projectiveScalarExtension (L := M)).norm (scalarExtensionTowerPlace x)
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E).toLinearMap.baseChange
          x.abv.Completion z) := by
  let := Algebra.IsAlgebraic.trans K L M
  exact (η.projectiveScalarExtension_norm_apply x z).trans
    ((ξ.projectiveScalarExtension_completed_trans_apply_of_norm_eq η x hη z).trans
      (ξ.projectiveScalarExtension_norm_apply (scalarExtensionTowerPlace x) _).symm)

/-- A first-step fibre with the injective extension norm has the same further
injective extension at a non-Archimedean place as direct extension. -/
theorem injectiveScalarExtension_trans_of_norm_eq
    (η : NormFamily (S.algebraicExtension L) (L ⊗[K] E))
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension L) M)
    (hx : IsNonarchimedean x.abv)
    (hη : ∀ a, η.norm x.base a = (ξ.injectiveScalarExtension (L := L)).norm x.base a)
    (z : x.abv.Completion ⊗[M] (M ⊗[L] (L ⊗[K] E))) :
    let := Algebra.IsAlgebraic.trans K L M
    (η.injectiveScalarExtension (L := M)).norm x z =
      (ξ.injectiveScalarExtension (L := M)).norm (scalarExtensionTowerPlace x)
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E).toLinearMap.baseChange
          x.abv.Completion z) := by
  let := Algebra.IsAlgebraic.trans K L M
  exact (η.injectiveScalarExtension_norm_apply x z).trans
    ((ξ.injectiveScalarExtension_completed_trans_apply_of_norm_eq η x hx hη z).trans
      (ξ.injectiveScalarExtension_norm_apply (scalarExtensionTowerPlace x) _).symm)

/-- The source's place-dependent scalar-extension family is transitive under
the canonical completed-fibre map of a successive algebraic extension. -/
theorem scalarExtension_trans
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension L) M)
    (z : x.abv.Completion ⊗[M] (M ⊗[L] (L ⊗[K] E))) :
    let := Algebra.IsAlgebraic.trans K L M
    ((ξ.scalarExtension (L := L)).scalarExtension (L := M)).norm x z =
      (ξ.scalarExtension (L := M)).norm (scalarExtensionTowerPlace x)
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E).toLinearMap.baseChange
          x.abv.Completion z) := by
  let := Algebra.IsAlgebraic.trans K L M
  by_cases h : x.base.base ∈ S.Ωfin
  · have hbase := (scalarExtension_mem_Ωfin_iff x.base).mpr h
    have hx : IsNonarchimedean x.abv := (scalarExtension_mem_Ωfin_iff x).mpr hbase
    exact ((ξ.scalarExtension (L := L)).scalarExtension_norm_of_mem_Ωfin x hbase z).trans
      ((ξ.injectiveScalarExtension_trans_of_norm_eq (ξ.scalarExtension (L := L)) x hx
        (fun a ↦ ξ.scalarExtension_norm_of_mem_Ωfin x.base h a) z).trans
        (ξ.scalarExtension_norm_of_mem_Ωfin (scalarExtensionTowerPlace x) h _).symm)
  · have hbase : x.base ∉ (S.algebraicExtension L).Ωfin :=
      fun hbase ↦ h ((scalarExtension_mem_Ωfin_iff x.base).mp hbase)
    exact ((ξ.scalarExtension (L := L)).scalarExtension_norm_of_not_mem_Ωfin x hbase z).trans
      ((ξ.projectiveScalarExtension_trans_of_norm_eq (ξ.scalarExtension (L := L)) x
        (fun a ↦ ξ.scalarExtension_norm_of_not_mem_Ωfin x.base h a) z).trans
        (ξ.scalarExtension_norm_of_not_mem_Ωfin (scalarExtensionTowerPlace x) h _).symm)

end Tower

end NormFamily

end

end ArakelovGeometry
