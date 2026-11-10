/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Dual
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionTower
public import ArakelovGeometry.Analysis.ScalarExtensionLine

/-!
# Duality for scalar extensions of norm families

Canonical completed-fibre pairings transport the local scalar-extension
duality theorems to the actual norm families.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The canonical completed-fibre scalar-extension maps preserve the actual
pairing of the extended algebraic dual with the extended vector space. -/
theorem completedScalarExtensionEquiv_dual_apply
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) (h : w.restriction K = v)
    (z : w.Completion ⊗[L] (L ⊗[K] Module.Dual K E))
    (x : w.Completion ⊗[L] (L ⊗[K] E)) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq v w h
    dualBaseChangeEquiv v.Completion w.Completion (v.Completion ⊗[K] E)
      ((dualBaseChangeEquiv K v.Completion E).toLinearMap.baseChange w.Completion
        (completedScalarExtensionEquiv (Module.Dual K E) v w h z))
      (completedScalarExtensionEquiv E v w h x) =
      dualBaseChangeEquiv L w.Completion (L ⊗[K] E)
        ((dualBaseChangeEquiv K L E).toLinearMap.baseChange w.Completion z) x := by
  intro aVW
  let := aVW
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simp only [map_add, LinearMap.add_apply, hz, ht]
  | tmul a y =>
    induction y using TensorProduct.inductionOn with
    | add y t hy ht => simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, hy, ht]
    | tmul b f =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul c y =>
        induction y using TensorProduct.inductionOn with
        | add y t hy ht => simp only [TensorProduct.tmul_add, map_add, hy, ht]
        | tmul d e =>
          simp only [completedScalarExtensionEquiv_tmul, LinearMap.baseChange_tmul,
            LinearEquiv.coe_coe, dualBaseChangeEquiv_tmul_apply_tmul, one_mul,
            map_mul, AbsoluteValue.algebraMap_normedAlgebraCompletionOfEq_coe]
          ring

private theorem projective_dual_transport
    {k l V A : Type*} [NormedField k] [CompleteSpace k]
    [NormedField l] [CompleteSpace l] [NormedAlgebra k l]
    [NormedAddCommGroup V] [NormedSpace k V] [FiniteDimensional k V]
    [NormedAddCommGroup A] [NormedSpace k A] [FiniteDimensional k A]
    (e : A ≃ₗ[k] Module.Dual k V)
    (he : ∀ a, ‖a‖ = linearMapOperatorSeminorm (e a))
    (hr : Module.finrank k V = 1) (z : l ⊗[k] A) :
    let := scalarExtensionProjectiveNormedAddCommGroup (k := k) (L := l) (E := V)
    let := scalarExtensionProjectiveNormedSpace (k := k) (L := l) (E := V)
    linearMapOperatorSeminorm
        (dualBaseChangeEquiv k l V (e.toLinearMap.baseChange l z)) =
      scalarExtensionProjectiveSeminorm z := by
  intro extGroup extSpace
  let := extGroup
  let := extSpace
  let := linearDualNormedAddCommGroup (k := k) (E := V)
  let := linearDualNormedSpace (k := k) (E := V)
  let ei : A ≃ₗᵢ[k] Module.Dual k V := { e with norm_map' := fun a ↦ (he a).symm }
  exact (scalarExtensionProjective_dual_of_finrank_one hr _).trans
    (scalarExtensionProjectiveSeminorm_baseChange_isometry (L := l) ei z)

private theorem injective_dual_transport
    {k l V A : Type*} [NormedField k] [CompleteSpace k]
    [NormedField l] [CompleteSpace l] [NormedAlgebra k l] [IsUltrametricDist l]
    [NormedAddCommGroup V] [NormedSpace k V] [FiniteDimensional k V]
    [NormedAddCommGroup A] [NormedSpace k A] [FiniteDimensional k A]
    (e : A ≃ₗ[k] Module.Dual k V)
    (he : ∀ a, ‖a‖ = linearMapOperatorSeminorm (e a)) (z : l ⊗[k] A) :
    let := scalarExtensionInjectiveNormedAddCommGroup (k := k) (L := l) (E := V)
    let := scalarExtensionInjectiveNormedSpace (k := k) (L := l) (E := V)
    linearMapOperatorSeminorm
        (dualBaseChangeEquiv k l V (e.toLinearMap.baseChange l z)) =
      scalarExtensionInjectiveSeminorm z := by
  intro extGroup extSpace
  let := extGroup
  let := extSpace
  let := linearDualNormedAddCommGroup (k := k) (E := V)
  let := linearDualNormedSpace (k := k) (E := V)
  let ei : A ≃ₗᵢ[k] Module.Dual k V := { e with norm_map' := fun a ↦ (he a).symm }
  exact (scalarExtensionInjective_dual _).trans
    (scalarExtensionInjectiveSeminorm_baseChange_isometry (L := l) ei z)

namespace NormFamily

private theorem dual_norm_eq_of_pairing {k X : Type*} [Field k]
    {T : AdelicStructure k} [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    (η : NormFamily T X) (ω : T.Ω) {G : Type*}
    [NormedAddCommGroup G]
    (e : ((T.ϕ ω).Completion ⊗[k] X) → G) (he : Function.Surjective e)
    (hn : ∀ x, η.norm ω x = ‖e x‖)
    (z : (T.ϕ ω).Completion ⊗[k] Module.Dual k X)
    (f : G → (T.ϕ ω).Completion)
    (hf : ∀ x, dualBaseChangeEquiv k (T.ϕ ω).Completion X z x = f (e x)) :
    η.dual.norm ω z = sSup (Set.range fun y : G ↦ ‖f y‖ / ‖y‖) := by
  rw [η.dual_norm_eq_sSup]
  congr 1
  ext c
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e x, by dsimp only; rw [hf, hn]⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := he y
    exact ⟨x, by dsimp only; rw [hf, hn]⟩

variable {S : AdelicStructure K} (ξ : NormFamily S E) [Algebra.IsAlgebraic K L]

/-- The dual of the actual projective extension is computed in the canonical
completed scalar-extension coordinates. -/
theorem projectiveScalarExtension_dual_norm_apply
    (x : AdelicStructure.ParameterSpaceExtension S L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] Module.Dual K E)) :
    let v := S.ϕ x.base
    let w := x.abv
    let h : w.restriction K = v := x.restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq v w h
    let finV : FiniteDimensional v.Completion (v.Completion ⊗[K] E) := inferInstance
    let nV : NormedAddCommGroup (v.Completion ⊗[K] E) := ξ.fibreNormedAddCommGroup x.base
    let nsV : NormedSpace v.Completion (v.Completion ⊗[K] E) := ξ.fibreNormedSpace x.base
    let : Module v.Completion (v.Completion ⊗[K] E) := nsV.toModule
    let : @FiniteDimensional v.Completion (v.Completion ⊗[K] E)
      (inferInstance : NormedField v.Completion).toField.toDivisionRing
      nV.toAddCommGroup nsV.toModule := finV
    let Z := completedScalarExtensionEquiv (Module.Dual K E) v w h z
    let f := dualBaseChangeEquiv v.Completion w.Completion (v.Completion ⊗[K] E)
      ((dualBaseChangeEquiv K v.Completion E).toLinearMap.baseChange w.Completion Z)
    let finG : FiniteDimensional w.Completion
      (w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E)) := inferInstance
    let extGroup : NormedAddCommGroup
        (w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E)) :=
      scalarExtensionProjectiveNormedAddCommGroup
        (k := v.Completion) (L := w.Completion) (E := v.Completion ⊗[K] E)
    let extSpace : NormedSpace w.Completion
        (w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E)) :=
      scalarExtensionProjectiveNormedSpace
        (k := v.Completion) (L := w.Completion) (E := v.Completion ⊗[K] E)
    let : Module w.Completion (w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E)) :=
      extSpace.toModule
    let : @FiniteDimensional w.Completion
      (w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E))
      (inferInstance : NormedField w.Completion).toField.toDivisionRing
      extGroup.toAddCommGroup extSpace.toModule := finG
    (ξ.projectiveScalarExtension (L := L)).dual.norm x
        ((dualBaseChangeEquiv K L E).toLinearMap.baseChange w.Completion z) =
      linearMapOperatorSeminorm f := by
  intro v w h aVW finV nV nsV modV finV' Z f finG extGroup extSpace modG finG'
  let := aVW
  let := nV
  let := nsV
  let := modV
  let := finV'
  let := extGroup
  let := extSpace
  let := modG
  let := finG'
  have hg := (ξ.projectiveScalarExtension (L := L)).dual_norm_eq_of_pairing x
    (G := w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E))
    (completedScalarExtensionEquiv E v w h)
    (completedScalarExtensionEquiv E v w h).surjective
    (fun y ↦ ξ.projectiveScalarExtension_norm_apply x y)
    ((dualBaseChangeEquiv K L E).toLinearMap.baseChange w.Completion z) f
    (fun y ↦ (completedScalarExtensionEquiv_dual_apply v w h z y).symm)
  exact hg.trans (linearMapOperatorSeminorm_eq_sSup f).symm

omit [Algebra.IsAlgebraic K L] in
private theorem projective_dual_completed
    (hr : Module.finrank K E = 1)
    (x : AdelicStructure.ParameterSpaceExtension S L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] Module.Dual K E)) :
    let v := S.ϕ x.base
    let w := x.abv
    let h : w.restriction K = v := x.restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq v w h
    let finV : FiniteDimensional v.Completion (v.Completion ⊗[K] E) := inferInstance
    let nV : NormedAddCommGroup (v.Completion ⊗[K] E) := ξ.fibreNormedAddCommGroup x.base
    let nsV : NormedSpace v.Completion (v.Completion ⊗[K] E) := ξ.fibreNormedSpace x.base
    let : Module v.Completion (v.Completion ⊗[K] E) := nsV.toModule
    let : @FiniteDimensional v.Completion (v.Completion ⊗[K] E)
      (inferInstance : NormedField v.Completion).toField.toDivisionRing
      nV.toAddCommGroup nsV.toModule := finV
    let finA : FiniteDimensional v.Completion (v.Completion ⊗[K] Module.Dual K E) := inferInstance
    let nA : NormedAddCommGroup (v.Completion ⊗[K] Module.Dual K E) :=
      ξ.dual.fibreNormedAddCommGroup x.base
    let nsA : NormedSpace v.Completion (v.Completion ⊗[K] Module.Dual K E) :=
      ξ.dual.fibreNormedSpace x.base
    let : Module v.Completion (v.Completion ⊗[K] Module.Dual K E) := nsA.toModule
    let : @FiniteDimensional v.Completion (v.Completion ⊗[K] Module.Dual K E)
      (inferInstance : NormedField v.Completion).toField.toDivisionRing
      nA.toAddCommGroup nsA.toModule := finA
    let Z := completedScalarExtensionEquiv (Module.Dual K E) v w h z
    let f := dualBaseChangeEquiv v.Completion w.Completion (v.Completion ⊗[K] E)
      ((dualBaseChangeEquiv K v.Completion E).toLinearMap.baseChange w.Completion Z)
    let finG : FiniteDimensional w.Completion
      (w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E)) := inferInstance
    let extGroup : NormedAddCommGroup
        (w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E)) :=
      scalarExtensionProjectiveNormedAddCommGroup
        (k := v.Completion) (L := w.Completion) (E := v.Completion ⊗[K] E)
    let extSpace : NormedSpace w.Completion
        (w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E)) :=
      scalarExtensionProjectiveNormedSpace
        (k := v.Completion) (L := w.Completion) (E := v.Completion ⊗[K] E)
    let : Module w.Completion (w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E)) :=
      extSpace.toModule
    let : @FiniteDimensional w.Completion
      (w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E))
      (inferInstance : NormedField w.Completion).toField.toDivisionRing
      extGroup.toAddCommGroup extSpace.toModule := finG
    linearMapOperatorSeminorm f = scalarExtensionProjectiveSeminorm Z := by
  intro v w h aVW finV nV nsV modV finV' finA nA nsA modA finA' Z f finG
    extGroup extSpace modG finG'
  let := aVW
  let := nV
  let := nsV
  let := modV
  let := finV'
  let := nA
  let := nsA
  let := modA
  let := finA'
  let := extGroup
  let := extSpace
  let := modG
  let := finG'
  have hr' : Module.finrank v.Completion (v.Completion ⊗[K] E) = 1 := by
    rw [Module.finrank_baseChange, hr]
  exact projective_dual_transport (dualBaseChangeEquiv K v.Completion E)
    (fun _ ↦ rfl) hr' Z

/-- The dual of the actual injective extension is computed in the canonical
completed scalar-extension coordinates. -/
theorem injectiveScalarExtension_dual_norm_apply
    (x : AdelicStructure.ParameterSpaceExtension S L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] Module.Dual K E)) :
    let v := S.ϕ x.base
    let w := x.abv
    let h : w.restriction K = v := x.restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq v w h
    let finV : FiniteDimensional v.Completion (v.Completion ⊗[K] E) := inferInstance
    let nV : NormedAddCommGroup (v.Completion ⊗[K] E) := ξ.fibreNormedAddCommGroup x.base
    let nsV : NormedSpace v.Completion (v.Completion ⊗[K] E) := ξ.fibreNormedSpace x.base
    let : Module v.Completion (v.Completion ⊗[K] E) := nsV.toModule
    let : @FiniteDimensional v.Completion (v.Completion ⊗[K] E)
      (inferInstance : NormedField v.Completion).toField.toDivisionRing
      nV.toAddCommGroup nsV.toModule := finV
    let Z := completedScalarExtensionEquiv (Module.Dual K E) v w h z
    let f := dualBaseChangeEquiv v.Completion w.Completion (v.Completion ⊗[K] E)
      ((dualBaseChangeEquiv K v.Completion E).toLinearMap.baseChange w.Completion Z)
    let finG : FiniteDimensional w.Completion
      (w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E)) := inferInstance
    let extGroup : NormedAddCommGroup
        (w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E)) :=
      scalarExtensionInjectiveNormedAddCommGroup
        (k := v.Completion) (L := w.Completion) (E := v.Completion ⊗[K] E)
    let extSpace : NormedSpace w.Completion
        (w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E)) :=
      scalarExtensionInjectiveNormedSpace
        (k := v.Completion) (L := w.Completion) (E := v.Completion ⊗[K] E)
    let : Module w.Completion (w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E)) :=
      extSpace.toModule
    let : @FiniteDimensional w.Completion
      (w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E))
      (inferInstance : NormedField w.Completion).toField.toDivisionRing
      extGroup.toAddCommGroup extSpace.toModule := finG
    (ξ.injectiveScalarExtension (L := L)).dual.norm x
        ((dualBaseChangeEquiv K L E).toLinearMap.baseChange w.Completion z) =
      linearMapOperatorSeminorm f := by
  intro v w h aVW finV nV nsV modV finV' Z f finG extGroup extSpace modG finG'
  let := aVW
  let := nV
  let := nsV
  let := modV
  let := finV'
  let := extGroup
  let := extSpace
  let := modG
  let := finG'
  have hg := (ξ.injectiveScalarExtension (L := L)).dual_norm_eq_of_pairing x
    (G := w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E))
    (completedScalarExtensionEquiv E v w h)
    (completedScalarExtensionEquiv E v w h).surjective
    (fun y ↦ ξ.injectiveScalarExtension_norm_apply x y)
    ((dualBaseChangeEquiv K L E).toLinearMap.baseChange w.Completion z) f
    (fun y ↦ (completedScalarExtensionEquiv_dual_apply v w h z y).symm)
  exact hg.trans (linearMapOperatorSeminorm_eq_sSup f).symm

omit [Algebra.IsAlgebraic K L] in
private theorem injective_dual_completed
    (x : AdelicStructure.ParameterSpaceExtension S L)
    (hx : IsNonarchimedean x.abv)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] Module.Dual K E)) :
    let v := S.ϕ x.base
    let w := x.abv
    let h : w.restriction K = v := x.restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq v w h
    let finV : FiniteDimensional v.Completion (v.Completion ⊗[K] E) := inferInstance
    let nV : NormedAddCommGroup (v.Completion ⊗[K] E) := ξ.fibreNormedAddCommGroup x.base
    let nsV : NormedSpace v.Completion (v.Completion ⊗[K] E) := ξ.fibreNormedSpace x.base
    let : Module v.Completion (v.Completion ⊗[K] E) := nsV.toModule
    let : @FiniteDimensional v.Completion (v.Completion ⊗[K] E)
      (inferInstance : NormedField v.Completion).toField.toDivisionRing
      nV.toAddCommGroup nsV.toModule := finV
    let finA : FiniteDimensional v.Completion (v.Completion ⊗[K] Module.Dual K E) := inferInstance
    let nA : NormedAddCommGroup (v.Completion ⊗[K] Module.Dual K E) :=
      ξ.dual.fibreNormedAddCommGroup x.base
    let nsA : NormedSpace v.Completion (v.Completion ⊗[K] Module.Dual K E) :=
      ξ.dual.fibreNormedSpace x.base
    let : Module v.Completion (v.Completion ⊗[K] Module.Dual K E) := nsA.toModule
    let : @FiniteDimensional v.Completion (v.Completion ⊗[K] Module.Dual K E)
      (inferInstance : NormedField v.Completion).toField.toDivisionRing
      nA.toAddCommGroup nsA.toModule := finA
    let Z := completedScalarExtensionEquiv (Module.Dual K E) v w h z
    let f := dualBaseChangeEquiv v.Completion w.Completion (v.Completion ⊗[K] E)
      ((dualBaseChangeEquiv K v.Completion E).toLinearMap.baseChange w.Completion Z)
    let finG : FiniteDimensional w.Completion
      (w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E)) := inferInstance
    let extGroup : NormedAddCommGroup
        (w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E)) :=
      scalarExtensionInjectiveNormedAddCommGroup
        (k := v.Completion) (L := w.Completion) (E := v.Completion ⊗[K] E)
    let extSpace : NormedSpace w.Completion
        (w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E)) :=
      scalarExtensionInjectiveNormedSpace
        (k := v.Completion) (L := w.Completion) (E := v.Completion ⊗[K] E)
    let : Module w.Completion (w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E)) :=
      extSpace.toModule
    let : @FiniteDimensional w.Completion
      (w.Completion ⊗[v.Completion] (v.Completion ⊗[K] E))
      (inferInstance : NormedField w.Completion).toField.toDivisionRing
      extGroup.toAddCommGroup extSpace.toModule := finG
    linearMapOperatorSeminorm f = scalarExtensionInjectiveSeminorm Z := by
  intro v w h aVW finV nV nsV modV finV' finA nA nsA modA finA' Z f finG
    extGroup extSpace modG finG'
  let := aVW
  let := nV
  let := nsV
  let := modV
  let := finV'
  let := nA
  let := nsA
  let := modA
  let := finA'
  let := extGroup
  let := extSpace
  let := modG
  let := finG'
  let := AbsoluteValue.isUltrametricDist_completion w hx
  exact injective_dual_transport (dualBaseChangeEquiv K v.Completion E)
    (fun _ ↦ rfl) Z

/-- Projective scalar extension commutes with the actual completed dual
family in dimension one. -/
theorem projectiveScalarExtension_dual_of_finrank_one
    (hr : Module.finrank K E = 1) (x : AdelicStructure.ParameterSpaceExtension S L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] Module.Dual K E)) :
    (ξ.dual.projectiveScalarExtension (L := L)).norm x z =
      (ξ.projectiveScalarExtension (L := L)).dual.norm x
        ((dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion z) := by
  exact (ξ.dual.projectiveScalarExtension_norm_apply x z).trans
    ((ξ.projective_dual_completed hr x z).symm.trans
      (ξ.projectiveScalarExtension_dual_norm_apply x z).symm)

/-- Injective scalar extension commutes with the actual completed dual
family at every non-Archimedean place, in arbitrary finite dimension. -/
theorem injectiveScalarExtension_dual
    (x : AdelicStructure.ParameterSpaceExtension S L) (hx : IsNonarchimedean x.abv)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] Module.Dual K E)) :
    (ξ.dual.injectiveScalarExtension (L := L)).norm x z =
      (ξ.injectiveScalarExtension (L := L)).dual.norm x
        ((dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion z) := by
  exact (ξ.dual.injectiveScalarExtension_norm_apply x z).trans
    ((ξ.injective_dual_completed x hx z).symm.trans
      (ξ.injectiveScalarExtension_dual_norm_apply x z).symm)

private theorem dual_norm_eq_of_norm_eq {k X : Type*} [Field k]
    {T : AdelicStructure k} [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    (η θ : NormFamily T X) (ω : T.Ω)
    (hn : ∀ x, η.norm ω x = θ.norm ω x)
    (z : (T.ϕ ω).Completion ⊗[k] Module.Dual k X) :
    η.dual.norm ω z = θ.dual.norm ω z := by
  rw [η.dual_norm_eq_sSup, θ.dual_norm_eq_sSup]
  simp only [hn]

/-- The source's scalar-extension family commutes with duality in dimension
one, using the canonical completed scalar extension of the algebraic dual map. -/
theorem scalarExtension_dual_of_finrank_one
    (hr : Module.finrank K E = 1) (x : AdelicStructure.ParameterSpaceExtension S L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] Module.Dual K E)) :
    (ξ.dual.scalarExtension (L := L)).norm x z =
      (ξ.scalarExtension (L := L)).dual.norm x
        ((dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion z) := by
  by_cases hx : x.base ∈ S.Ωfin
  · have hx' : IsNonarchimedean x.abv := (scalarExtension_mem_Ωfin_iff x).mpr hx
    exact (ξ.dual.scalarExtension_norm_of_mem_Ωfin x hx z).trans
      ((ξ.injectiveScalarExtension_dual x hx' z).trans
        (dual_norm_eq_of_norm_eq (ξ.scalarExtension (L := L))
          (ξ.injectiveScalarExtension (L := L)) x
          (fun a ↦ ξ.scalarExtension_norm_of_mem_Ωfin x hx a) _).symm)
  · exact (ξ.dual.scalarExtension_norm_of_not_mem_Ωfin x hx z).trans
      ((ξ.projectiveScalarExtension_dual_of_finrank_one hr x z).trans
        (dual_norm_eq_of_norm_eq (ξ.scalarExtension (L := L))
          (ξ.projectiveScalarExtension (L := L)) x
          (fun a ↦ ξ.scalarExtension_norm_of_not_mem_Ωfin x hx a) _).symm)

end NormFamily

end

end ArakelovGeometry
