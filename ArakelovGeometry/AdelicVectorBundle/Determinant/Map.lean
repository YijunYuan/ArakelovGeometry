/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Determinant.Basic
public import ArakelovGeometry.AdelicVectorBundle.Operator.Norm
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Maps on actual determinant lines

Equal-dimensional linear maps act on the existing top exterior powers.
The only index transport is equality of their dimensions. Scalar extension
commutes with these maps on the actual completed determinant fibres.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

section Algebra

variable (K : Type*) [Field K] (E : Type*) [AddCommGroup E] [Module K E]

/-- Equality of exterior degrees gives the canonical equality isomorphism. -/
def exteriorPowerDegreeEquiv {n m : ℕ} (h : n = m) :
    (⋀[K]^n E) ≃ₗ[K] (⋀[K]^m E) :=
  LinearEquiv.ofEq _ _ (congrArg (fun j ↦ ⋀[K]^j E) h)

@[simp]
theorem exteriorPowerDegreeEquiv_rfl (n : ℕ) :
    exteriorPowerDegreeEquiv K E (rfl : n = n) = LinearEquiv.refl K _ := rfl

/-- Index transport acts on a wedge by the same equality on its finite index. -/
theorem exteriorPowerDegreeEquiv_ιMulti {n m : ℕ} (h : n = m) (x : Fin n → E) :
    exteriorPowerDegreeEquiv K E h (_root_.exteriorPower.ιMulti K n x) =
      _root_.exteriorPower.ιMulti K m (fun i ↦ x ((finCongr h).symm i)) := by
  subst m
  rfl

variable {E} {F : Type*} [AddCommGroup F] [Module K F]

/-- The map on determinant lines of an equal-dimensional rational linear map. -/
def determinantMap (f : E →ₗ[K] F) (h : Module.finrank K E = Module.finrank K F) :
    (⋀[K]^(Module.finrank K E) E) →ₗ[K] (⋀[K]^(Module.finrank K F) F) :=
  (exteriorPowerDegreeEquiv K F h).toLinearMap ∘ₗ
    _root_.exteriorPower.map (Module.finrank K E) f

variable (L : Type*) [Field L] [Algebra K L]

/-- Exterior maps commute with the accepted canonical completed scalar-extension map. -/
theorem exteriorBaseChangeEquiv_map (n : ℕ) (f : E →ₗ[K] F)
    (z : L ⊗[K] (⋀[K]^n E)) :
    exteriorBaseChangeEquiv K L F n ((_root_.exteriorPower.map n f).baseChange L z) =
      _root_.exteriorPower.map n (f.baseChange L) (exteriorBaseChangeEquiv K L E n z) := by
  have he : (exteriorBaseChangeEquiv K L F n).toLinearMap ∘ₗ
        (_root_.exteriorPower.map n f).baseChange L =
      _root_.exteriorPower.map n (f.baseChange L) ∘ₗ
        (exteriorBaseChangeEquiv K L E n).toLinearMap := by
    apply LinearMap.restrictScalars_injective K
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply _root_.exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro x
    change exteriorBaseChangeEquiv K L F n
      ((_root_.exteriorPower.map n f).baseChange L
        (a ⊗ₜ[K] _root_.exteriorPower.ιMulti K n x)) =
      _root_.exteriorPower.map n (f.baseChange L)
        (exteriorBaseChangeEquiv K L E n (a ⊗ₜ[K] _root_.exteriorPower.ιMulti K n x))
    simp only [LinearMap.baseChange_tmul,
      _root_.exteriorPower.map_apply_ιMulti, exteriorBaseChangeEquiv_tmul_ιMulti,
      map_smul, Function.comp_def]
  exact DFunLike.congr_fun he z

/-- Exterior degree transport commutes with scalar extension. -/
theorem exteriorBaseChangeEquiv_degreeEquiv {n m : ℕ} (h : n = m)
    (z : L ⊗[K] (⋀[K]^n E)) :
    exteriorBaseChangeEquiv K L E m
        ((exteriorPowerDegreeEquiv K E h).toLinearMap.baseChange L z) =
      exteriorPowerDegreeEquiv L (L ⊗[K] E) h (exteriorBaseChangeEquiv K L E n z) := by
  subst m
  simp only [exteriorPowerDegreeEquiv_rfl, LinearEquiv.refl_toLinearMap,
    LinearMap.baseChange_id, LinearMap.id_apply, LinearEquiv.refl_apply]

/-- The completed determinant map sends each wedge to the wedge of its images. -/
theorem determinantMap_baseChange_ιMulti (f : E →ₗ[K] F)
    (h : Module.finrank K E = Module.finrank K F)
    (x : Fin (Module.finrank K E) → L ⊗[K] E) :
    (determinantMap K f h).baseChange L
        ((exteriorBaseChangeEquiv K L E (Module.finrank K E)).symm
          (_root_.exteriorPower.ιMulti L (Module.finrank K E) x)) =
      (exteriorBaseChangeEquiv K L F (Module.finrank K F)).symm
        (_root_.exteriorPower.ιMulti L (Module.finrank K F)
          (fun i ↦ f.baseChange L (x ((finCongr h).symm i)))) := by
  apply (exteriorBaseChangeEquiv K L F (Module.finrank K F)).injective
  simp only [determinantMap, LinearMap.baseChange_comp, LinearMap.comp_apply,
    exteriorBaseChangeEquiv_degreeEquiv, exteriorBaseChangeEquiv_map,
    LinearEquiv.apply_symm_apply, _root_.exteriorPower.map_apply_ιMulti,
    exteriorPowerDegreeEquiv_ιMulti, Function.comp_def]

/-- Every degree-zero exterior vector is a scalar multiple of the empty wedge. -/
theorem exteriorPower_eq_smul_empty {n : ℕ} (h : n = 0) (z : ⋀[K]^n E) :
    ∃ a : K, z = a • _root_.exteriorPower.ιMulti K n (fun _ ↦ (0 : E)) := by
  subst n
  refine ⟨_root_.exteriorPower.zeroEquiv K E z, ?_⟩
  apply (_root_.exteriorPower.zeroEquiv K E).injective
  simp only [map_smul, _root_.exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]

end Algebra

namespace NormFamily

universe u w w'

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- An evaluation bound for an equal-rank map gives its rank-th power on
determinants. A zero bound is allowed, so singular and zero maps are included. -/
theorem determinantMap_norm_le_of_pos_rank (ξ : NormFamily S E) (η : NormFamily S F)
    (ω : S.Ω) (f : E →ₗ[K] F) (hr : Module.finrank K E = Module.finrank K F)
    (hpos : 0 < Module.finrank K E) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x, η.norm ω (f.baseChange (S.ϕ ω).Completion x) ≤ C * ξ.norm ω x)
    (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    η.determinant.norm ω ((determinantMap K f hr).baseChange (S.ϕ ω).Completion z) ≤
      C ^ Module.finrank K E * ξ.determinant.norm ω z := by
  have hCr := pow_nonneg hC (Module.finrank K E)
  have hden : 0 < C ^ Module.finrank K E + 1 := by positivity
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨x, hx, he⟩ := ξ.exists_determinant_ιMulti_norm_lt hpos ω z (div_pos hε hden)
  have hdet := η.determinant_norm_ιMulti_le ω
    (fun i ↦ f.baseChange (S.ϕ ω).Completion (x ((finCongr hr).symm i)))
  rw [← determinantMap_baseChange_ιMulti K (S.ϕ ω).Completion f hr x, hx] at hdet
  have hp : (∏ i, η.norm ω (f.baseChange (S.ϕ ω).Completion (x i))) ≤
      C ^ Module.finrank K E * ∏ i, ξ.norm ω (x i) := by
    calc
      _ ≤ ∏ i, C * ξ.norm ω (x i) :=
        Finset.prod_le_prod₀ (fun _ _ ↦ η.norm_nonneg ω _) (fun i _ ↦ hf (x i))
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hε' : C ^ Module.finrank K E * (ε / (C ^ Module.finrank K E + 1)) ≤ ε := by
    calc
      _ ≤ (C ^ Module.finrank K E + 1) * (ε / (C ^ Module.finrank K E + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) (div_pos hε hden).le
      _ = ε := mul_div_cancel₀ _ hden.ne'
  have he' := mul_le_mul_of_nonneg_left he.le hCr
  rw [(finCongr hr).symm.prod_comp
    (fun i ↦ η.norm ω (f.baseChange (S.ϕ ω).Completion (x i)))] at hdet
  exact (hdet.trans hp).trans (by nlinarith)

/-- The determinant of an equal positive-rank map has operator norm at most
the rank-th power of its actual completed operator norm. -/
theorem determinantMap_operatorNorm_le (ξ : NormFamily S E) (η : NormFamily S F)
    (ω : S.Ω) (f : E →ₗ[K] F) (hr : Module.finrank K E = Module.finrank K F)
    (hpos : 0 < Module.finrank K E) :
    ξ.determinant.operatorNorm η.determinant ω (determinantMap K f hr) ≤
      ξ.operatorNorm η ω f ^ Module.finrank K E := by
  apply operatorNorm_le
    _ _ _ _ (pow_nonneg (ξ.operatorNorm_nonneg η ω f) _)
  exact ξ.determinantMap_norm_le_of_pos_rank η ω f hr hpos
    (ξ.operatorNorm_nonneg η ω f) (ξ.norm_baseChange_le_operatorNorm η ω f)

/-- The norm of the completed empty wedge is one. -/
theorem determinant_norm_empty_completed (ξ : NormFamily S E)
    (h : Module.finrank K E = 0) (ω : S.Ω) :
    ξ.determinant.norm ω
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm
        (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K E)
          (fun _ ↦ (0 : (S.ϕ ω).Completion ⊗[K] E)))) = 1 := by
  have he := exteriorBaseChangeEquiv_symm_ιMulti_tmul K (S.ϕ ω).Completion E
    (Module.finrank K E) (fun _ ↦ 1) (fun _ ↦ 0)
  simp only [TensorProduct.tmul_zero, Finset.prod_const_one] at he
  rw [he, ξ.determinant_norm_empty_tmul h ω 1, norm_one]

/-- Maps between rank-zero spaces induce isometries of their scalar determinant lines. -/
theorem determinantMap_norm_eq_of_finrank_eq_zero (ξ : NormFamily S E)
    (η : NormFamily S F) (ω : S.Ω) (f : E →ₗ[K] F)
    (hr : Module.finrank K E = Module.finrank K F) (hzero : Module.finrank K E = 0)
    (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    η.determinant.norm ω ((determinantMap K f hr).baseChange (S.ϕ ω).Completion z) =
      ξ.determinant.norm ω z := by
  obtain ⟨a, ha⟩ := exteriorPower_eq_smul_empty (S.ϕ ω).Completion hzero
    (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E) z)
  have hz : z = a • (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E
      (Module.finrank K E)).symm
        (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K E)
          (fun _ ↦ (0 : (S.ϕ ω).Completion ⊗[K] E))) := by
    apply (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).injective
    simpa only [map_smul, LinearEquiv.apply_symm_apply] using ha
  rw [hz, map_smul, ξ.determinant.norm_smul, η.determinant.norm_smul,
    determinantMap_baseChange_ιMulti, ξ.determinant_norm_empty_completed hzero]
  simp only [map_zero]
  rw [η.determinant_norm_empty_completed (hr.symm.trans hzero)]

/-- In rank zero the determinant operator norm is one, including for the zero map. -/
theorem determinantMap_operatorNorm_eq_one_of_finrank_eq_zero (ξ : NormFamily S E)
    (η : NormFamily S F) (ω : S.Ω) (f : E →ₗ[K] F)
    (hr : Module.finrank K E = Module.finrank K F) (hzero : Module.finrank K E = 0) :
    ξ.determinant.operatorNorm η.determinant ω (determinantMap K f hr) = 1 := by
  apply le_antisymm
  · apply operatorNorm_le _ _ _ _ zero_le_one
    intro z
    rw [ξ.determinantMap_norm_eq_of_finrank_eq_zero η ω f hr hzero z, one_mul]
  · have h := ξ.determinant.norm_baseChange_le_operatorNorm η.determinant ω
      (determinantMap K f hr)
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm
        (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K E) (fun _ ↦ 0)))
    rw [ξ.determinantMap_norm_eq_of_finrank_eq_zero η ω f hr hzero,
      ξ.determinant_norm_empty_completed hzero, mul_one] at h
    exact h

/-- The determinant operator estimate holds in every rank, with the unit
determinant convention handling rank zero. -/
theorem determinantMap_operatorNorm_le_pow (ξ : NormFamily S E) (η : NormFamily S F)
    (ω : S.Ω) (f : E →ₗ[K] F) (hr : Module.finrank K E = Module.finrank K F) :
    ξ.determinant.operatorNorm η.determinant ω (determinantMap K f hr) ≤
      ξ.operatorNorm η ω f ^ Module.finrank K E := by
  by_cases hzero : Module.finrank K E = 0
  · rw [ξ.determinantMap_operatorNorm_eq_one_of_finrank_eq_zero η ω f hr hzero]
    simp only [hzero, pow_zero, le_refl]
  · exact ξ.determinantMap_operatorNorm_le η ω f hr (Nat.pos_of_ne_zero hzero)

end NormFamily

end

end ArakelovGeometry
