/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.DeterminantMap

/-!
# Canonical determinant isomorphisms and completed isometries

The actual top exterior map respects composition and identities. An isometry
on the completed vector fibres therefore induces an isometry on the actual
completed determinant lines, including the scalar unit lines in rank zero.
-/

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

section Algebra

variable (K : Type*) [Field K]
  {E : Type*} [AddCommGroup E] [Module K E]
  {F : Type*} [AddCommGroup F] [Module K F]
  {G : Type*} [AddCommGroup G] [Module K G]

private theorem exteriorPowerDegreeEquiv_map_comp {n m r : ℕ}
    (h : n = m) (h' : m = r) (f : E →ₗ[K] F) (g : F →ₗ[K] G) :
    ((exteriorPowerDegreeEquiv K G h').toLinearMap ∘ₗ _root_.exteriorPower.map m g) ∘ₗ
        ((exteriorPowerDegreeEquiv K F h).toLinearMap ∘ₗ _root_.exteriorPower.map n f) =
      (exteriorPowerDegreeEquiv K G (h.trans h')).toLinearMap ∘ₗ
        _root_.exteriorPower.map n (g ∘ₗ f) := by
  subst m
  subst r
  simp only [exteriorPowerDegreeEquiv_rfl, LinearEquiv.refl_toLinearMap,
    LinearMap.id_comp, _root_.exteriorPower.map_comp]

/-- The canonical maps of actual determinant lines respect composition. -/
theorem determinantMap_comp (f : E →ₗ[K] F) (g : F →ₗ[K] G)
    (h : Module.finrank K E = Module.finrank K F)
    (h' : Module.finrank K F = Module.finrank K G) :
    determinantMap K g h' ∘ₗ determinantMap K f h =
      determinantMap K (g ∘ₗ f) (h.trans h') :=
  exteriorPowerDegreeEquiv_map_comp K h h' f g

/-- The canonical determinant map of the identity is the identity. -/
@[simp]
theorem determinantMap_id :
    determinantMap K (LinearMap.id : E →ₗ[K] E) rfl = LinearMap.id := by
  simp only [determinantMap, exteriorPowerDegreeEquiv_rfl, LinearEquiv.refl_toLinearMap,
    _root_.exteriorPower.map_id, LinearMap.id_comp]

/-- A rational linear isomorphism induces the canonical isomorphism of actual
rational determinant lines. -/
def determinantEquiv (e : E ≃ₗ[K] F) :
    (⋀[K]^(Module.finrank K E) E) ≃ₗ[K] (⋀[K]^(Module.finrank K F) F) :=
  LinearEquiv.ofLinearMap (determinantMap K e.toLinearMap e.finrank_eq)
    (determinantMap K e.symm.toLinearMap e.finrank_eq.symm)
    (by rw [determinantMap_comp]; simp)
    (by rw [determinantMap_comp]; simp)

@[simp]
theorem determinantEquiv_toLinearMap (e : E ≃ₗ[K] F) :
    (determinantEquiv K e).toLinearMap = determinantMap K e.toLinearMap e.finrank_eq := rfl

@[simp]
theorem determinantEquiv_symm_toLinearMap (e : E ≃ₗ[K] F) :
    (determinantEquiv K e).symm.toLinearMap =
      determinantMap K e.symm.toLinearMap e.finrank_eq.symm := rfl

end Algebra

namespace NormFamily

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- A contraction on actual completed vector fibres contracts the actual
completed determinant lines in every rank. -/
theorem determinantMap_norm_le_of_norm_le (ξ : NormFamily S E) (η : NormFamily S F)
    (ω : S.Ω) (f : E →ₗ[K] F) (hr : Module.finrank K E = Module.finrank K F)
    (hf : ∀ x, η.norm ω (f.baseChange (S.ϕ ω).Completion x) ≤ ξ.norm ω x)
    (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    η.determinant.norm ω ((determinantMap K f hr).baseChange (S.ϕ ω).Completion z) ≤
      ξ.determinant.norm ω z := by
  have hop := ξ.operatorNorm_le η ω f zero_le_one (fun x ↦ by simpa using hf x)
  have hd := ξ.determinantMap_operatorNorm_le_pow η ω f hr
  have hp : ξ.operatorNorm η ω f ^ Module.finrank K E ≤ 1 :=
    pow_le_one₀ (ξ.operatorNorm_nonneg η ω f) hop
  have he := ξ.determinant.norm_baseChange_le_operatorNorm η.determinant ω
    (determinantMap K f hr) z
  exact he.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (hd.trans hp) (ξ.determinant.norm_nonneg ω z))

/-- Every actual completed-fibre isometry induces an isometry on the actual
completed determinant lines. -/
theorem determinantEquiv_norm_eq (ξ : NormFamily S E) (η : NormFamily S F)
    (ω : S.Ω) (e : E ≃ₗ[K] F)
    (he : ∀ x, η.norm ω (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = ξ.norm ω x)
    (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    η.determinant.norm ω ((determinantEquiv K e).baseChange K (S.ϕ ω).Completion _ _ z) =
      ξ.determinant.norm ω z := by
  let eω := e.baseChange K (S.ϕ ω).Completion E F
  let Dω := (determinantEquiv K e).baseChange K (S.ϕ ω).Completion _ _
  have hei : ∀ y, ξ.norm ω (e.symm.toLinearMap.baseChange (S.ϕ ω).Completion y) =
      η.norm ω y := by
    intro y
    change ξ.norm ω (eω.symm y) = η.norm ω y
    have h : ξ.norm ω (eω.symm y) = η.norm ω (eω (eω.symm y)) :=
      (he (eω.symm y)).symm
    rwa [LinearEquiv.apply_symm_apply] at h
  have hforward : ∀ z, η.determinant.norm ω (Dω z) ≤ ξ.determinant.norm ω z := by
    intro z
    exact ξ.determinantMap_norm_le_of_norm_le η ω e.toLinearMap e.finrank_eq
      (fun x ↦ (he x).le) z
  have hinverse : ∀ y, ξ.determinant.norm ω (Dω.symm y) ≤ η.determinant.norm ω y := by
    intro y
    exact η.determinantMap_norm_le_of_norm_le ξ ω e.symm.toLinearMap
      e.finrank_eq.symm (fun y ↦ (hei y).le) y
  apply le_antisymm (hforward z)
  simpa only [LinearEquiv.symm_apply_apply] using hinverse (Dω z)

end NormFamily

end

end ArakelovGeometry
