/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DirectSumDualFinite
public import ArakelovGeometry.Analysis.NormShapeDualOperator

/-!
# The actual Archimedean dual of a profile direct sum

The polar-profile formula on the completed algebraic dual and the resulting
measurability in Chen–Moriwaki Proposition 4.1.35.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w w'
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

variable (ξ : NormFamily S E) (η : NormFamily S F)

/-- The actual completed dual at an isometrically real or complex place. -/
theorem directSum_dual_norm_of_isRCLike (ψ : S.Ω → NormShape) (ω : S.Ω)
    (hL : IsRCLikeNormedField (S.ϕ ω).Completion)
    (f : (S.ϕ ω).Completion ⊗[K] Module.Dual K (E × F)) :
    (ξ.directSum η ψ).dual.norm ω f = (ψ ω).dual.perspective
      (ξ.dual.norm ω ((LinearMap.inl K E F).dualMap.baseChange (S.ϕ ω).Completion f))
      (η.dual.norm ω ((LinearMap.inr K E F).dualMap.baseChange (S.ϕ ω).Completion f)) := by
  let := hL
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := η.fibreNormedAddCommGroup ω
  let := η.fibreNormedSpace ω
  let e := TensorProduct.prodRight K (S.ϕ ω).Completion (S.ϕ ω).Completion E F
  let f₁ := dualBaseChangeEquiv K (S.ϕ ω).Completion E
    ((LinearMap.inl K E F).dualMap.baseChange (S.ϕ ω).Completion f)
  let f₂ := dualBaseChangeEquiv K (S.ϕ ω).Completion F
    ((LinearMap.inr K E F).dualMap.baseChange (S.ϕ ω).Completion f)
  have hfst (z : (S.ϕ ω).Completion ⊗[K] (E × F)) :
      (LinearMap.fst K E F).baseChange (S.ϕ ω).Completion z = (e z).1 := by
    induction z using TensorProduct.inductionOn with
    | tmul a z => rfl
    | add z t hz ht => simp [hz, ht]
  have hsnd (z : (S.ϕ ω).Completion ⊗[K] (E × F)) :
      (LinearMap.snd K E F).baseChange (S.ϕ ω).Completion z = (e z).2 := by
    induction z using TensorProduct.inductionOn with
    | tmul a z => rfl
    | add z t hz ht => simp [hz, ht]
  rw [dual_norm_eq_sSup]
  change sSup _ = (ψ ω).dual.perspective
    (linearMapOperatorSeminorm f₁) (linearMapOperatorSeminorm f₂)
  rw [← sSup_profile_dual_ratio (ψ ω) f₁ f₂]
  congr 1
  ext r
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨e z, ?_⟩
    simp only [dualBaseChange_prod_apply, hfst, hsnd, directSum_norm]
    rfl
  · rintro ⟨z, rfl⟩
    refine ⟨e.symm z, ?_⟩
    simp only [dualBaseChange_prod_apply, hfst, hsnd, directSum_norm]
    change ‖f₁ (e (e.symm z)).1 + f₂ (e (e.symm z)).2‖ /
      (ψ ω).perspective ‖(e (e.symm z)).1‖ ‖(e (e.symm z)).2‖ = _
    rw [e.apply_symm_apply]

/-- The Archimedean formula for rational functionals. -/
theorem directSum_dual_norm_rational_of_isRCLike (ψ : S.Ω → NormShape) (ω : S.Ω)
    (hL : IsRCLikeNormedField (S.ϕ ω).Completion) (ℓ : Module.Dual K (E × F)) :
    (ξ.directSum η ψ).dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ) =
      (ψ ω).dual.perspective
        (ξ.dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ.comp (LinearMap.inl K E F)))
        (η.dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ.comp (LinearMap.inr K E F))) := by
  have h₁ : (LinearMap.inl K E F).dualMap ℓ = ℓ.comp (LinearMap.inl K E F) := by
    ext x; rfl
  have h₂ : (LinearMap.inr K E F).dualMap ℓ = ℓ.comp (LinearMap.inr K E F) := by
    ext x; rfl
  simpa only [LinearMap.baseChange_tmul, h₁, h₂] using
    ξ.directSum_dual_norm_of_isRCLike η ψ ω hL (1 ⊗ₜ[K] ℓ)

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.NormShape

variable {K : Type*} [Field K] (S : AdelicStructure K)

/-- The source dual profile: polar at infinite places and maximum at finite places. -/
noncomputable def adelicDual (ψ : S.Ω → NormShape) (ω : S.Ω) : NormShape := by
  classical
  exact if ω ∈ S.Ωinf then (ψ ω).dual else maxShape

/-- The place-dependent dual profile preserves source measurability. -/
theorem IsMeasurableFamily.adelicDual {ψ : S.Ω → NormShape}
    (hψ : IsMeasurableFamily ψ) : IsMeasurableFamily (adelicDual S ψ) := by
  classical
  let : MeasurableSpace C(Set.Icc (0 : ℝ) 1, ℝ) := borel _
  change Measurable (fun ω ↦ (NormShape.adelicDual S ψ ω).continuousMap)
  have h : Measurable (S.Ωinf.piecewise (fun ω ↦ (ψ ω).dual.continuousMap)
      (fun _ : S.Ω ↦ maxShape.continuousMap)) :=
    hψ.dual.piecewise S.measurableSet_Ωinf measurable_const
  convert h using 1
  ext ω
  by_cases hω : ω ∈ S.Ωinf <;> simp [NormShape.adelicDual, Set.piecewise, hω]

end ArakelovGeometry.NormShape

namespace ArakelovGeometry.NormFamily

universe u v w w'
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]
variable (ξ : NormFamily S E) (η : NormFamily S F)

/-- The single place-dependent dual profile computes every actual completed dual norm. -/
theorem directSum_dual_norm (ψ : S.Ω → NormShape)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω)
    (f : (S.ϕ ω).Completion ⊗[K] Module.Dual K (E × F)) :
    (ξ.directSum η ψ).dual.norm ω f = (NormShape.adelicDual S ψ ω).perspective
      (ξ.dual.norm ω ((LinearMap.inl K E F).dualMap.baseChange (S.ϕ ω).Completion f))
      (η.dual.norm ω ((LinearMap.inr K E F).dualMap.baseChange (S.ϕ ω).Completion f)) := by
  classical
  by_cases hω : ω ∈ S.Ωinf
  · simpa only [NormShape.adelicDual, ite_eq_left hω] using
      ξ.directSum_dual_norm_of_isRCLike η ψ ω (hS ω hω) f
  · rw [NormShape.adelicDual, ite_eq_right hω,
      NormShape.maxShape_perspective (ξ.dual.norm_nonneg ω _) (η.dual.norm_nonneg ω _)]
    exact ξ.directSum_dual_norm_eq_max_of_finite η ψ ω
      (by simpa [AdelicStructure.Ωinf, AdelicStructure.Ωfin] using hω) f

/-- Actual dual measurability for general measurable profile sums. -/
theorem directSum_dual_isMeasurable (ψ : S.Ω → NormShape)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ξ.dual.IsMeasurable) (hη : η.dual.IsMeasurable)
    (hψ : NormShape.IsMeasurableFamily ψ) : (ξ.directSum η ψ).dual.IsMeasurable := by
  intro ℓ
  have h := (hψ.adelicDual S).perspective
    (hξ (ℓ.comp (LinearMap.inl K E F))) (hη (ℓ.comp (LinearMap.inr K E F)))
    (fun ω ↦ ξ.dual.norm_nonneg ω _) (fun ω ↦ η.dual.norm_nonneg ω _)
  convert h using 1
  ext ω
  have h₁ : (LinearMap.inl K E F).dualMap ℓ = ℓ.comp (LinearMap.inl K E F) := by
    ext x; rfl
  have h₂ : (LinearMap.inr K E F).dualMap ℓ = ℓ.comp (LinearMap.inr K E F) := by
    ext x; rfl
  simpa only [LinearMap.baseChange_tmul, h₁, h₂] using
    ξ.directSum_dual_norm η ψ hS ω (1 ⊗ₜ[K] ℓ)

end ArakelovGeometry.NormFamily
