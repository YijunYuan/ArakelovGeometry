/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Local.Lattice.CompletedUnitBall
public import ArakelovGeometry.NumberTheory.NumberField.Local.Lattice.FreeUnitBall
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Rational

/-!
# Actual completed local unit-ball reconstruction

The produced local free basis gives actual completed coordinates. Continuity
and the produced rational unit-ball closure make every completed-ball
coordinate integral; no completed coefficient-integrality or density
certificate is assumed.
-/

@[expose] public section

open scoped TensorProduct NumberField

noncomputable section

namespace ArakelovGeometry.NormFamily

open AdelicStructure

universe u v w

variable {K : Type u} [Field K] [NumberField K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Scalar extension of the produced local generic basis is an actual basis
of the canonical completed tensor fibre. -/
def completedLocalUnitBallBasis (ξ : NormFamily S E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric) :
    Module.Basis (Fin (Module.finrank (S.rationalLocalRing ω hω)
      (ξ.rationalUnitBallModule ω hω hξ))) (S.ϕ ω).Completion
      ((S.ϕ ω).Completion ⊗[K] E) :=
  (ξ.rationalLocalUnitBallGenericBasis ω hω hnt hξ).baseChange (S.ϕ ω).Completion

@[simp]
theorem completedLocalUnitBallBasis_apply (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric)
    (i : Fin (Module.finrank (S.rationalLocalRing ω hω)
      (ξ.rationalUnitBallModule ω hω hξ))) :
    ξ.completedLocalUnitBallBasis ω hω hnt hξ i =
      1 ⊗ₜ[K] (ξ.rationalLocalUnitBallBasis ω hω hnt hξ i : E) := by
  rw [completedLocalUnitBallBasis, Module.Basis.baseChange_apply,
    ξ.rationalLocalUnitBallGenericBasis_coe]

/-- Actual generic-basis coordinates of original local-ball vectors are the
literal field images of their actual local-basis coefficients. -/
theorem rationalLocalUnitBallGenericBasis_repr_coe (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric)
    (x : ξ.rationalUnitBallModule ω hω hξ)
    (i : Fin (Module.finrank (S.rationalLocalRing ω hω)
      (ξ.rationalUnitBallModule ω hω hξ))) :
    (ξ.rationalLocalUnitBallGenericBasis ω hω hnt hξ).repr (x : E) i =
      ((ξ.rationalLocalUnitBallBasis ω hω hnt hξ).repr x i : K) := by
  let e := ξ.rationalUnitBallGenericFibreEquiv ω hω hnt hξ
  have he : e.symm (x : E) = 1 ⊗ₜ[S.rationalLocalRing ω hω] x := by
    apply e.injective
    rw [e.apply_symm_apply, ξ.rationalUnitBallGenericFibreEquiv_tmul, one_smul]
  change ((ξ.rationalLocalUnitBallBasis ω hω hnt hξ).baseChange K).repr
    (e.symm (x : E)) i = _
  rw [he, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  rfl

/-- Completed coordinates of rational local-ball images are their actual
completion-embedded literal local coefficients. -/
theorem completedLocalUnitBallBasis_repr_rational (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric)
    (x : ξ.rationalUnitBallModule ω hω hξ)
    (i : Fin (Module.finrank (S.rationalLocalRing ω hω)
      (ξ.rationalUnitBallModule ω hω hξ))) :
    (ξ.completedLocalUnitBallBasis ω hω hnt hξ).repr (1 ⊗ₜ[K] (x : E)) i =
      algebraMap K (S.ϕ ω).Completion
        ((ξ.rationalLocalUnitBallBasis ω hω hnt hξ).repr x i : K) := by
  rw [completedLocalUnitBallBasis, Module.Basis.baseChange_repr_tmul,
    ξ.rationalLocalUnitBallGenericBasis_repr_coe, Algebra.smul_def, mul_one]

/-- Continuity and the actual rational-ball closure force every completed-ball
coordinate to have completed scalar norm at most one. -/
theorem completedLocalUnitBallBasis_coordinates_le_one (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric)
    {z : (S.ϕ ω).Completion ⊗[K] E} (hz : z ∈ ξ.completedUnitBall ω) :
    ∀ i, ‖(ξ.completedLocalUnitBallBasis ω hω hnt hξ).repr z i‖ ≤ 1 := by
  let := ξ.fibreNormedAddCommGroup ω
  let b := ξ.completedLocalUnitBallBasis ω hω hnt hξ
  have hc : IsClosed {z | ∀ i, ‖b.repr z i‖ ≤ 1} := by
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_le (ξ.continuous_completed_linearMap ω (b.coord i)).norm continuous_const
  have him : ((fun x : E => (1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) '' ξ.rationalUnitBall ω) ⊆
      {z | ∀ i, ‖b.repr z i‖ ≤ 1} := by
    rintro _ ⟨x, hx, rfl⟩ i
    rw [ξ.completedLocalUnitBallBasis_repr_rational ω hω hnt hξ ⟨x, hx⟩ i,
      S.norm_algebraMap_eq_absValue]
    exact ((ξ.rationalLocalUnitBallBasis ω hω hnt hξ).repr ⟨x, hx⟩ i).property
  have hcl := closure_minimal him hc
  rw [ξ.closure_rationalUnitBall_image_eq_completedUnitBall hξ ω hω] at hcl
  exact hcl hz

/-- The canonical completed tensor map preserves the produced basis
coordinates through the literal completed coefficient-ring inclusion. -/
theorem completedLocalUnitBallBasis_repr_tensorMap (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric)
    (t : (S.completedLocalRing ω hω) ⊗[S.rationalLocalRing ω hω]
      (ξ.rationalUnitBallModule ω hω hξ))
    (i : Fin (Module.finrank (S.rationalLocalRing ω hω)
      (ξ.rationalUnitBallModule ω hω hξ))) :
    (ξ.completedLocalUnitBallBasis ω hω hnt hξ).repr
        (ξ.rationalUnitBallCompletedTensorMap ω hω hξ t : (S.ϕ ω).Completion ⊗[K] E) i =
      (((ξ.rationalLocalUnitBallBasis ω hω hnt hξ).baseChange
        (S.completedLocalRing ω hω)).repr t i : (S.ϕ ω).Completion) := by
  classical
  let b := ξ.completedLocalUnitBallBasis ω hω hnt hξ
  let bt := (ξ.rationalLocalUnitBallBasis ω hω hnt hξ).baseChange
    (S.completedLocalRing ω hω)
  let f := ξ.rationalUnitBallCompletedTensorMap ω hω hξ
  have h : ((b.coord i).restrictScalars (S.completedLocalRing ω hω)).comp
        ((ξ.completedUnitBallModule ω hω hξ).subtype.comp f) =
      (Algebra.linearMap (S.completedLocalRing ω hω) (S.ϕ ω).Completion).comp (bt.coord i) := by
    apply bt.ext
    intro j
    have hl : (f (bt j) : (S.ϕ ω).Completion ⊗[K] E) = b j := by
      dsimp only [bt, f, b]
      rw [Module.Basis.baseChange_apply, ξ.rationalUnitBallCompletedTensorMap_tmul,
        one_smul, ξ.rationalUnitBallCompletionMap_coe, ← ξ.completedLocalUnitBallBasis_apply]
    change b.coord i (f (bt j) : (S.ϕ ω).Completion ⊗[K] E) =
      algebraMap (S.completedLocalRing ω hω) (S.ϕ ω).Completion (bt.coord i (bt j))
    rw [hl]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  exact congrArg (fun l => l t) h

/-- Produced integral completed coordinates and the actual basis-coordinate
formula prove the canonical completed tensor map bijective. -/
theorem rationalUnitBallCompletedTensorMap_bijective (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric) :
    Function.Bijective (ξ.rationalUnitBallCompletedTensorMap ω hω hξ) := by
  let b := ξ.completedLocalUnitBallBasis ω hω hnt hξ
  let bt := (ξ.rationalLocalUnitBallBasis ω hω hnt hξ).baseChange
    (S.completedLocalRing ω hω)
  constructor
  · intro t u h
    apply bt.ext_elem
    intro i
    apply Subtype.ext
    exact (ξ.completedLocalUnitBallBasis_repr_tensorMap ω hω hnt hξ t i).symm.trans
      ((congrArg (fun z : ξ.completedUnitBallModule ω hω hξ =>
        b.repr (z : (S.ϕ ω).Completion ⊗[K] E) i) h).trans
          (ξ.completedLocalUnitBallBasis_repr_tensorMap ω hω hnt hξ u i))
  · intro z
    let c : Fin (Module.finrank (S.rationalLocalRing ω hω)
        (ξ.rationalUnitBallModule ω hω hξ)) → S.completedLocalRing ω hω := fun i =>
      ⟨b.repr (z : (S.ϕ ω).Completion ⊗[K] E) i,
        (S.mem_completedLocalRing ω hω _).mpr
          (ξ.completedLocalUnitBallBasis_coordinates_le_one ω hω hnt hξ z.property i)⟩
    refine ⟨bt.equivFun.symm c, ?_⟩
    apply Subtype.ext
    apply b.ext_elem
    intro i
    rw [ξ.completedLocalUnitBallBasis_repr_tensorMap ω hω hnt hξ]
    have hc : bt.repr (bt.equivFun.symm c) i = c i := by
      simpa only [Module.Basis.equivFun_apply] using
        congrArg (fun z => z i) (bt.equivFun.apply_symm_apply c)
    exact congrArg (fun a : S.completedLocalRing ω hω => (a : (S.ϕ ω).Completion)) hc

/-- Remark 4.4.1(2): actual completed coefficient extension of the literal
rational local unit ball is the literal completed unit-ball module. -/
def rationalUnitBallCompletedTensorEquiv (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric) :
    (S.completedLocalRing ω hω) ⊗[S.rationalLocalRing ω hω]
      (ξ.rationalUnitBallModule ω hω hξ) ≃ₗ[S.completedLocalRing ω hω]
      ξ.completedUnitBallModule ω hω hξ :=
  LinearEquiv.ofBijective (ξ.rationalUnitBallCompletedTensorMap ω hω hξ)
    (ξ.rationalUnitBallCompletedTensorMap_bijective ω hω hnt hξ)

@[simp]
theorem rationalUnitBallCompletedTensorEquiv_tmul (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric)
    (a : S.completedLocalRing ω hω) (x : ξ.rationalUnitBallModule ω hω hξ) :
    ξ.rationalUnitBallCompletedTensorEquiv ω hω hnt hξ (a ⊗ₜ[S.rationalLocalRing ω hω] x) =
      a • ξ.rationalUnitBallCompletionMap ω hω hξ x :=
  ξ.rationalUnitBallCompletedTensorMap_tmul ω hω hξ a x

/-- Native actual completed-ball reconstruction at every normalized finite
number-field point, with nontriviality produced from the actual parameter. -/
def normalizedRationalUnitBallCompletedTensorEquiv
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) (hξ : ξ.IsUltrametric) :
    ((normalizedNumberFieldAdelicStructure K).completedLocalRing ω hω) ⊗[
      (normalizedNumberFieldAdelicStructure K).rationalLocalRing ω hω]
      (ξ.rationalUnitBallModule ω hω hξ) ≃ₗ[
      (normalizedNumberFieldAdelicStructure K).completedLocalRing ω hω]
      ξ.completedUnitBallModule ω hω hξ :=
  ξ.rationalUnitBallCompletedTensorEquiv ω hω
    (NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω)) hξ

@[simp]
theorem normalizedRationalUnitBallCompletedTensorEquiv_tmul
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) (hξ : ξ.IsUltrametric)
    (a : (normalizedNumberFieldAdelicStructure K).completedLocalRing ω hω)
    (x : ξ.rationalUnitBallModule ω hω hξ) :
    ξ.normalizedRationalUnitBallCompletedTensorEquiv ω hω hξ
        (a ⊗ₜ[(normalizedNumberFieldAdelicStructure K).rationalLocalRing ω hω] x) =
      a • ξ.rationalUnitBallCompletionMap ω hω hξ x :=
  ξ.rationalUnitBallCompletedTensorEquiv_tmul ω hω _ hξ a x

end ArakelovGeometry.NormFamily

end
