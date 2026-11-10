/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NormFamilyCompletedUnitBallBasis

/-!
# Actual completed local unit-ball lattices

The actual local completed tensor equivalence transports the produced rational
local basis to a completed coefficient basis of the literal ball. This gives
finite freeness, full rank and the actual canonical completed generic fibre.
No global coherence, domination or assumed local-lattice certificate is used.
-/

open scoped TensorProduct NumberField

noncomputable section

namespace ArakelovGeometry.NormFamily

open AdelicStructure

universe u v w

variable {K : Type u} [Field K] [NumberField K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The produced local basis extends and transports to a genuine completed
coefficient basis of the literal completed unit ball. -/
def completedUnitBallBasis (ξ : NormFamily S E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric) :
    Module.Basis (Fin (Module.finrank (S.rationalLocalRing ω hω)
      (ξ.rationalUnitBallModule ω hω hξ))) (S.completedLocalRing ω hω)
      (ξ.completedUnitBallModule ω hω hξ) :=
  ((ξ.rationalLocalUnitBallBasis ω hω hnt hξ).baseChange
    (S.completedLocalRing ω hω)).map (ξ.rationalUnitBallCompletedTensorEquiv ω hω hnt hξ)

@[simp]
theorem completedUnitBallBasis_coe (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric)
    (i : Fin (Module.finrank (S.rationalLocalRing ω hω)
      (ξ.rationalUnitBallModule ω hω hξ))) :
    (ξ.completedUnitBallBasis ω hω hnt hξ i : (S.ϕ ω).Completion ⊗[K] E) =
      1 ⊗ₜ[K] (ξ.rationalLocalUnitBallBasis ω hω hnt hξ i : E) := by
  rw [completedUnitBallBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    ξ.rationalUnitBallCompletedTensorEquiv_tmul, one_smul]
  rfl

/-- The actual completed unit ball is free over its actual completed coefficient ring. -/
theorem free_completedUnitBallModule (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric) :
    Module.Free (S.completedLocalRing ω hω) (ξ.completedUnitBallModule ω hω hξ) :=
  Module.Free.of_basis (ξ.completedUnitBallBasis ω hω hnt hξ)

/-- The actual finite completed coefficient basis gives a finite local module. -/
theorem finite_completedUnitBallModule (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric) :
    Module.Finite (S.completedLocalRing ω hω) (ξ.completedUnitBallModule ω hω hξ) :=
  Module.Finite.of_basis (ξ.completedUnitBallBasis ω hω hnt hξ)

/-- The literal completed unit-ball rank equals the original rational dimension. -/
theorem finrank_completedUnitBallModule (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric) :
    Module.finrank (S.completedLocalRing ω hω) (ξ.completedUnitBallModule ω hω hξ) =
      Module.finrank K E := by
  rw [Module.finrank_eq_card_basis (ξ.completedUnitBallBasis ω hω hnt hξ),
    Fintype.card_fin, ξ.finrank_rationalUnitBallModule ω hω hnt hξ]

/-- The actual completed-ball inclusion extended to its actual completed field. -/
def completedUnitBallGenericFibreMap (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hξ : ξ.IsUltrametric) :
    (S.ϕ ω).Completion ⊗[S.completedLocalRing ω hω]
      (ξ.completedUnitBallModule ω hω hξ) →ₗ[(S.ϕ ω).Completion]
      ((S.ϕ ω).Completion ⊗[K] E) :=
  (ξ.completedUnitBallModule ω hω hξ).subtype.liftBaseChange (S.ϕ ω).Completion

omit [NumberField K] [FiniteDimensional K E] in
@[simp]
theorem completedUnitBallGenericFibreMap_tmul (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hξ : ξ.IsUltrametric) (a : (S.ϕ ω).Completion)
    (x : ξ.completedUnitBallModule ω hω hξ) :
    ξ.completedUnitBallGenericFibreMap ω hω hξ (a ⊗ₜ[S.completedLocalRing ω hω] x) =
      a • (x : (S.ϕ ω).Completion ⊗[K] E) :=
  LinearMap.liftBaseChange_tmul _ _ a x

/-- The actual completed generic fibre isomorphism matches the two produced
completed-field bases of the actual ball tensor and the original completed fibre. -/
def completedUnitBallGenericFibreEquiv (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric) :
    (S.ϕ ω).Completion ⊗[S.completedLocalRing ω hω]
      (ξ.completedUnitBallModule ω hω hξ) ≃ₗ[(S.ϕ ω).Completion]
      ((S.ϕ ω).Completion ⊗[K] E) :=
  ((ξ.completedUnitBallBasis ω hω hnt hξ).baseChange (S.ϕ ω).Completion).equiv
    (ξ.completedLocalUnitBallBasis ω hω hnt hξ) (Equiv.refl _)

/-- The produced completed generic equivalence is the original canonical map. -/
theorem completedUnitBallGenericFibreEquiv_coe (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric) :
    (ξ.completedUnitBallGenericFibreEquiv ω hω hnt hξ).toLinearMap =
      ξ.completedUnitBallGenericFibreMap ω hω hξ := by
  apply ((ξ.completedUnitBallBasis ω hω hnt hξ).baseChange (S.ϕ ω).Completion).ext
  intro i
  change ((ξ.completedUnitBallBasis ω hω hnt hξ).baseChange (S.ϕ ω).Completion).equiv
    (ξ.completedLocalUnitBallBasis ω hω hnt hξ) (Equiv.refl _) _ = _
  rw [Module.Basis.equiv_apply, Equiv.refl_apply, Module.Basis.baseChange_apply,
    ξ.completedUnitBallGenericFibreMap_tmul, one_smul,
    ξ.completedUnitBallBasis_coe, ξ.completedLocalUnitBallBasis_apply]

@[simp]
theorem completedUnitBallGenericFibreEquiv_tmul (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric)
    (a : (S.ϕ ω).Completion) (x : ξ.completedUnitBallModule ω hω hξ) :
    ξ.completedUnitBallGenericFibreEquiv ω hω hnt hξ
        (a ⊗ₜ[S.completedLocalRing ω hω] x) =
      a • (x : (S.ϕ ω).Completion ⊗[K] E) := by
  change (ξ.completedUnitBallGenericFibreEquiv ω hω hnt hξ).toLinearMap _ = _
  rw [ξ.completedUnitBallGenericFibreEquiv_coe, ξ.completedUnitBallGenericFibreMap_tmul]

/-- The original actual completed generic-fibre tensor map is bijective. -/
theorem completedUnitBallGenericFibreMap_bijective (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric) :
    Function.Bijective (ξ.completedUnitBallGenericFibreMap ω hω hξ) := by
  rw [← ξ.completedUnitBallGenericFibreEquiv_coe ω hω hnt hξ]
  exact (ξ.completedUnitBallGenericFibreEquiv ω hω hnt hξ).bijective

/-- The literal completed local ball spans the actual completed vector-space fibre. -/
theorem span_completedUnitBall_eq_top (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric) :
    Submodule.span (S.ϕ ω).Completion (ξ.completedUnitBall ω) = ⊤ := by
  apply top_unique
  rw [← (ξ.completedLocalUnitBallBasis ω hω hnt hξ).span_eq]
  apply Submodule.span_mono
  rintro z ⟨i, rfl⟩
  rw [ξ.completedLocalUnitBallBasis_apply,
    ← ξ.completedUnitBallBasis_coe ω hω hnt hξ i]
  exact (ξ.completedUnitBallBasis ω hω hnt hξ i).property

/-- Native completed local freeness at every actual normalized finite parameter. -/
theorem free_normalizedCompletedUnitBallModule
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) (hξ : ξ.IsUltrametric) :
    Module.Free ((normalizedNumberFieldAdelicStructure K).completedLocalRing ω hω)
      (ξ.completedUnitBallModule ω hω hξ) :=
  ξ.free_completedUnitBallModule ω hω
    (NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω)) hξ

/-- Native actual completed local rank equals the original rational dimension. -/
theorem finrank_normalizedCompletedUnitBallModule
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) (hξ : ξ.IsUltrametric) :
    Module.finrank ((normalizedNumberFieldAdelicStructure K).completedLocalRing ω hω)
      (ξ.completedUnitBallModule ω hω hξ) = Module.finrank K E :=
  ξ.finrank_completedUnitBallModule ω hω
    (NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω)) hξ

/-- Native actual completed generic-fibre reconstruction at every finite normalized point. -/
def normalizedCompletedUnitBallGenericFibreEquiv
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) (hξ : ξ.IsUltrametric) :
    ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[
      (normalizedNumberFieldAdelicStructure K).completedLocalRing ω hω]
      (ξ.completedUnitBallModule ω hω hξ) ≃ₗ[
      ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion]
      (((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] E) :=
  ξ.completedUnitBallGenericFibreEquiv ω hω
    (NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω)) hξ

@[simp]
theorem normalizedCompletedUnitBallGenericFibreEquiv_tmul
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) (hξ : ξ.IsUltrametric)
    (a : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion)
    (x : ξ.completedUnitBallModule ω hω hξ) :
    ξ.normalizedCompletedUnitBallGenericFibreEquiv ω hω hξ
        (a ⊗ₜ[(normalizedNumberFieldAdelicStructure K).completedLocalRing ω hω] x) =
      a • (x : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] E) :=
  ξ.completedUnitBallGenericFibreEquiv_tmul ω hω _ hξ a x

end ArakelovGeometry.NormFamily

end
