/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Basic
public import ArakelovGeometry.AdelicVectorBundle.Determinant.Map
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Integral
import ArakelovGeometry.AdelicVectorBundle.Determinant.Universal
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Line
import ArakelovGeometry.Analysis.ScalarExtension.Line
import Mathlib.CategoryTheory.Category.Init

/-!
# Determinants under scalar extension

Local multilinear scalar-extension bounds identify the actual determinant
of ordinary mixed scalar extension with the scalar-extended determinant:
injective outside infinity and projective at infinity. The resulting actual
determinant line is adelic and preserves degree. The constructions include the
empty exterior power. The separately defined Hermitian scalar extension is
outside this module's comparison.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

section Local

variable {k l E W : Type*} [NormedField k] [NormedField l] [NormedAlgebra k l]
  [NormedAddCommGroup E] [NormedSpace k E]
  [AddCommGroup W] [Module l W]

private theorem seminorm_linearMap_le_of_maximal
    (q : Seminorm l (l ⊗[k] E)) (p : Seminorm l W)
    (f : l ⊗[k] E →ₗ[l] W) {C : ℝ} (hC : 0 ≤ C)
    (hmax : ∀ r : Seminorm l (l ⊗[k] E),
      (∀ x : E, r ((1 : l) ⊗ₜ[k] x) ≤ ‖x‖) → r ≤ q)
    (hf : ∀ x : E, p (f ((1 : l) ⊗ₜ[k] x)) ≤ C * ‖x‖)
    (z : l ⊗[k] E) : p (f z) ≤ C * q z := by
  by_cases hzero : C = 0
  · have hx (x : E) : p (f ((1 : l) ⊗ₜ[k] x)) = 0 :=
      le_antisymm (by simpa only [hzero, zero_mul] using hf x) (apply_nonneg _ _)
    have hz : p (f z) = 0 := by
      induction z using TensorProduct.inductionOn with
      | tmul a x =>
        have he : a ⊗ₜ[k] x = a • ((1 : l) ⊗ₜ[k] x) := by
          simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [he, map_smul, map_smul_eq_mul, hx, mul_zero]
      | add z t hz ht =>
        apply le_antisymm _ (apply_nonneg _ _)
        rw [f.map_add]
        exact (map_add_le_add p (f z) (f t)).trans_eq (by rw [hz, ht, add_zero])
    simp only [hz, hzero, zero_mul, le_refl]
  · have hpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hzero)
    let r : Seminorm l (l ⊗[k] E) :=
      NNReal.mk C⁻¹ (inv_nonneg.mpr hC) • p.comp f
    have hr : r ≤ q := hmax r (fun x => by
      change C⁻¹ * p (f ((1 : l) ⊗ₜ[k] x)) ≤ ‖x‖
      exact (inv_mul_le_iff₀ hpos).2 (hf x))
    have h := hr z
    change C⁻¹ * p (f z) ≤ q z at h
    exact (inv_mul_le_iff₀ hpos).1 h

/-- A base product bound for a linear map extends to the actual projective
scalar-extension seminorm. The bound may be zero. -/
theorem seminorm_linearMap_le_scalarExtensionProjective
    (p : Seminorm l W) (f : l ⊗[k] E →ₗ[l] W) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x : E, p (f ((1 : l) ⊗ₜ[k] x)) ≤ C * ‖x‖)
    (z : l ⊗[k] E) :
    p (f z) ≤ C * scalarExtensionProjectiveSeminorm z :=
  seminorm_linearMap_le_of_maximal _ p f hC
    (fun r hr => le_scalarExtensionProjectiveSeminorm r hr) hf z

variable [CompleteSpace k] [FiniteDimensional k E]

/-- An ultrametric target seminorm extends a base linear bound to the actual
injective scalar-extension norm. The original vector norm is arbitrary. -/
theorem seminorm_linearMap_le_scalarExtensionInjective
    (p : Seminorm l W) (hp : ∀ x y, p (x + y) ≤ max (p x) (p y))
    (f : l ⊗[k] E →ₗ[l] W) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x : E, p (f ((1 : l) ⊗ₜ[k] x)) ≤ C * ‖x‖)
    (z : l ⊗[k] E) :
    p (f z) ≤ C * scalarExtensionInjectiveSeminorm z := by
  by_cases hzero : C = 0
  · have h := seminorm_linearMap_le_scalarExtensionProjective p f hC hf z
    simpa only [hzero, zero_mul] using h
  have hpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hzero)
  let r : Seminorm l (l ⊗[k] E) :=
    NNReal.mk C⁻¹ (inv_nonneg.mpr hC) • p.comp f
  have hr : r ≤ scalarExtensionInjectiveSeminorm :=
    le_scalarExtensionInjectiveSeminorm_of_ultrametric r (fun z t => by
      change C⁻¹ * p (f (z + t)) ≤
        max (C⁻¹ * p (f z)) (C⁻¹ * p (f t))
      rw [f.map_add, ← mul_max_of_nonneg _ _ (inv_nonneg.mpr hC)]
      exact mul_le_mul_of_nonneg_left (hp _ _) (inv_nonneg.mpr hC)) (fun x => by
      change C⁻¹ * p (f ((1 : l) ⊗ₜ[k] x)) ≤ ‖x‖
      exact (inv_mul_le_iff₀ hpos).2 (hf x))
  have h := hr z
  change C⁻¹ * p (f z) ≤ scalarExtensionInjectiveSeminorm z at h
  exact (inv_mul_le_iff₀ hpos).1 h

omit [CompleteSpace k] [FiniteDimensional k E] in
private theorem seminorm_multilinearMap_le_of_linear_bound
    {ι : Type*} [Fintype ι]
    (q : Seminorm l (l ⊗[k] E)) (p : Seminorm l W)
    (f : MultilinearMap l (fun _ : ι => l ⊗[k] E) W)
    (hlinear : ∀ (g : l ⊗[k] E →ₗ[l] W) (A : ℝ), 0 ≤ A →
      (∀ x : E, p (g ((1 : l) ⊗ₜ[k] x)) ≤ A * ‖x‖) →
      ∀ z, p (g z) ≤ A * q z)
    {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x : ι → E, p (f (fun i => (1 : l) ⊗ₜ[k] x i)) ≤ C * ∏ i, ‖x i‖)
    (z : ι → l ⊗[k] E) : p (f z) ≤ C * ∏ i, q (z i) := by
  classical
  have hs (s : Finset ι) : ∀ (x : ι → E) (z : ι → l ⊗[k] E),
      p (f (fun i => if i ∈ s then z i else (1 : l) ⊗ₜ[k] x i)) ≤
        C * ∏ i, if i ∈ s then q (z i) else ‖x i‖ := by
    induction s using Finset.induction_on with
    | empty =>
      intro x z
      simpa only [Finset.notMem_empty, ite_false] using hf x
    | @insert i s hi ih =>
      intro x z
      let m : ι → l ⊗[k] E := fun j => if j ∈ s then z j else (1 : l) ⊗ₜ[k] x j
      let c : ι → ℝ := fun j => if j ∈ s then q (z j) else ‖x j‖
      let A : ℝ := C * ∏ j ∈ Finset.univ.erase i, c j
      have hA : 0 ≤ A := mul_nonneg hC (Finset.prod_nonneg fun j _ => by
        dsimp [c]
        split_ifs
        · exact apply_nonneg _ _
        · exact norm_nonneg _)
      have hbase (y : E) : p ((f.toLinearMap m i) ((1 : l) ⊗ₜ[k] y)) ≤ A * ‖y‖ := by
        have h := ih (Function.update x i y) z
        have hm : (fun j => if j ∈ s then z j else
            (1 : l) ⊗ₜ[k] Function.update x i y j) =
            Function.update m i ((1 : l) ⊗ₜ[k] y) := by
          funext j
          by_cases hj : j = i
          · subst j
            simp only [hi, ite_false, Function.update_self]
          · simp only [Function.update_of_ne hj, m]
        have hc : (fun j => if j ∈ s then q (z j) else
            ‖Function.update x i y j‖) = Function.update c i ‖y‖ := by
          funext j
          by_cases hj : j = i
          · subst j
            simp only [hi, ite_false, Function.update_self]
          · simp only [Function.update_of_ne hj, c]
        rw [hm, hc, Finset.prod_update_of_mem (Finset.mem_univ i),
          Finset.sdiff_singleton_eq_erase] at h
        change p (f (Function.update m i ((1 : l) ⊗ₜ[k] y))) ≤ _
        simpa only [A, mul_assoc, mul_left_comm, mul_comm] using h
      have h := hlinear (f.toLinearMap m i) A hA hbase (z i)
      have hm : Function.update m i (z i) =
          (fun j => if j ∈ insert i s then z j else (1 : l) ⊗ₜ[k] x j) := by
        funext j
        by_cases hj : j = i
        · subst j
          simp only [Function.update_self, Finset.mem_insert_self, ite_true]
        · simp only [Function.update_of_ne hj, Finset.mem_insert, hj, false_or, m]
      have hc : (fun j => if j ∈ insert i s then q (z j) else ‖x j‖) =
          Function.update c i (q (z i)) := by
        funext j
        by_cases hj : j = i
        · subst j
          simp only [Function.update_self, Finset.mem_insert_self, ite_true]
        · simp only [Function.update_of_ne hj, Finset.mem_insert, hj, false_or, c]
      change p (f (Function.update m i (z i))) ≤ _ at h
      rw [hm] at h
      rw [hc, Finset.prod_update_of_mem (Finset.mem_univ i),
        Finset.sdiff_singleton_eq_erase]
      simpa only [A, mul_assoc, mul_left_comm, mul_comm] using h
  simpa only [Finset.mem_univ, ite_true] using hs Finset.univ (fun _ => 0) z

omit [CompleteSpace k] [FiniteDimensional k E] in
/-- A multilinear base product bound extends argument by argument to
projective scalar-extension norms, including an empty family of arguments. -/
theorem seminorm_multilinearMap_le_scalarExtensionProjective
    {ι : Type*} [Fintype ι] (p : Seminorm l W)
    (f : MultilinearMap l (fun _ : ι => l ⊗[k] E) W)
    {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x : ι → E, p (f (fun i => (1 : l) ⊗ₜ[k] x i)) ≤ C * ∏ i, ‖x i‖)
    (z : ι → l ⊗[k] E) :
    p (f z) ≤ C * ∏ i, scalarExtensionProjectiveSeminorm (z i) :=
  seminorm_multilinearMap_le_of_linear_bound _ p f
    (fun g _ hA hg z => seminorm_linearMap_le_scalarExtensionProjective p g hA hg z)
    hC hf z

/-- An ultrametric multilinear target preserves the same product bound for
injective scalar extension. No ultrametricity of the base vector norm is assumed. -/
theorem seminorm_multilinearMap_le_scalarExtensionInjective
    {ι : Type*} [Fintype ι] (p : Seminorm l W)
    (hp : ∀ x y, p (x + y) ≤ max (p x) (p y))
    (f : MultilinearMap l (fun _ : ι => l ⊗[k] E) W)
    {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x : ι → E, p (f (fun i => (1 : l) ⊗ₜ[k] x i)) ≤ C * ∏ i, ‖x i‖)
    (z : ι → l ⊗[k] E) :
    p (f z) ≤ C * ∏ i, scalarExtensionInjectiveSeminorm (z i) :=
  seminorm_multilinearMap_le_of_linear_bound _ p f
    (fun g _ hA hg z => seminorm_linearMap_le_scalarExtensionInjective p hp g hA hg z)
    hC hf z

end Local

section Exterior

variable (K k l E : Type*) [Field K] [Field k] [Field l]
  [Algebra K k] [Algebra K l] [Algebra k l] [IsScalarTower K k l]
  [AddCommGroup E] [Module K E]

/-- Exterior base change commutes with the canonical cancellation of a field
tower. This is an equality on actual exterior powers in every degree. -/
theorem exteriorBaseChangeEquiv_tower (n : ℕ)
    (z : l ⊗[k] (k ⊗[K] (⋀[K]^n E))) :
    exteriorBaseChangeEquiv K l E n
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K k l l (⋀[K]^n E) z) =
    _root_.exteriorPower.map n
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K k l l E).toLinearMap
      (exteriorBaseChangeEquiv k l (k ⊗[K] E) n
        ((exteriorBaseChangeEquiv K k E n).toLinearMap.baseChange l z)) := by
  have he : (exteriorBaseChangeEquiv K l E n).toLinearMap ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K k l l (⋀[K]^n E)).toLinearMap =
      _root_.exteriorPower.map n
        (TensorProduct.AlgebraTensorModule.cancelBaseChange K k l l E).toLinearMap ∘ₗ
        (exteriorBaseChangeEquiv k l (k ⊗[K] E) n).toLinearMap ∘ₗ
        (exteriorBaseChangeEquiv K k E n).toLinearMap.baseChange l := by
    apply LinearMap.restrictScalars_injective k
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.restrictScalars_injective K
    apply TensorProduct.ext
    apply LinearMap.ext
    intro b
    apply _root_.exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro x
    change exteriorBaseChangeEquiv K l E n
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K k l l (⋀[K]^n E)
        (a ⊗ₜ[k] (b ⊗ₜ[K] _root_.exteriorPower.ιMulti K n x))) =
      _root_.exteriorPower.map n
        (TensorProduct.AlgebraTensorModule.cancelBaseChange K k l l E).toLinearMap
        (exteriorBaseChangeEquiv k l (k ⊗[K] E) n
          ((exteriorBaseChangeEquiv K k E n).toLinearMap.baseChange l
            (a ⊗ₜ[k] (b ⊗ₜ[K] _root_.exteriorPower.ιMulti K n x))))
    simp only [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
      exteriorBaseChangeEquiv_tmul_ιMulti, map_smul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      _root_.exteriorPower.map_apply_ιMulti, Function.comp_def, one_smul]
  exact DFunLike.congr_fun he z

end Exterior

section DeterminantEquiv

variable (K L E : Type*) [Field K] [Field L] [Algebra K L]
  [AddCommGroup E] [Module K E]

/-- Canonical determinant scalar extension: exterior base change followed
only by the equality of the original and extended dimensions. -/
def determinantScalarExtensionEquiv :
    (L ⊗[K] (⋀[K]^(Module.finrank K E) E)) ≃ₗ[L]
      (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E)) :=
  (exteriorBaseChangeEquiv K L E (Module.finrank K E)).trans
    (exteriorPowerDegreeEquiv L (L ⊗[K] E) Module.finrank_baseChange.symm)

/-- A pure determinant tensor maps to the wedge of the rational inclusions,
with only the canonical finite-index transport. -/
theorem determinantScalarExtensionEquiv_tmul_ιMulti (a : L)
    (x : Fin (Module.finrank K E) → E) :
    determinantScalarExtensionEquiv K L E
      (a ⊗ₜ[K] _root_.exteriorPower.ιMulti K (Module.finrank K E) x) =
    a • _root_.exteriorPower.ιMulti L (Module.finrank L (L ⊗[K] E))
      (fun i => (1 : L) ⊗ₜ[K] x ((finCongr Module.finrank_baseChange.symm).symm i)) := by
  simp only [determinantScalarExtensionEquiv, LinearEquiv.trans_apply,
    exteriorBaseChangeEquiv_tmul_ιMulti, map_smul, exteriorPowerDegreeEquiv_ιMulti]

end DeterminantEquiv

section ScalarExtensionExterior

variable (K k l E : Type*) [Field K] [Field k] [Field l]
  [Algebra K k] [Algebra k l] [AddCommGroup E] [Module K E]

/-- The canonical scalar-extended wedge, valued in the scalar extension of
 the original exterior power. Applied to completions, this retains the
 original rational determinant-line presentation. -/
def scalarExtensionExteriorMap (n : ℕ) :
    AlternatingMap l (l ⊗[k] (k ⊗[K] E))
      (l ⊗[k] (k ⊗[K] (⋀[K]^n E))) (Fin n) :=
  ((exteriorBaseChangeEquiv K k E n).symm.toLinearMap.baseChange l).compAlternatingMap
    ((exteriorBaseChangeEquiv k l (k ⊗[K] E) n).symm.toLinearMap.compAlternatingMap
      (_root_.exteriorPower.ιMulti l n))

/-- Restriction of the scalar-extended wedge to the original vectors,
including the exterior unit in degree zero. -/
theorem scalarExtensionExteriorMap_one_tmul (n : ℕ) (x : Fin n → k ⊗[K] E) :
    scalarExtensionExteriorMap K k l E n (fun i => (1 : l) ⊗ₜ[k] x i) =
      (1 : l) ⊗ₜ[k] ((exteriorBaseChangeEquiv K k E n).symm
        (_root_.exteriorPower.ιMulti k n x)) := by
  change ((exteriorBaseChangeEquiv K k E n).symm.toLinearMap.baseChange l)
    ((exteriorBaseChangeEquiv k l (k ⊗[K] E) n).symm
      (_root_.exteriorPower.ιMulti l n (fun i => (1 : l) ⊗ₜ[k] x i))) = _
  rw [exteriorBaseChangeEquiv_symm_ιMulti_tmul, Finset.prod_const_one,
    LinearMap.baseChange_tmul]
  rfl

/-- Cancellation identifies the scalar-extended wedge with the wedge of
the cancelled vectors. Thus the exterior map uses the canonical field tower. -/
theorem scalarExtensionExteriorMap_cancelBaseChange [Algebra K l] [IsScalarTower K k l]
    (n : ℕ) (z : Fin n → l ⊗[k] (k ⊗[K] E)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange K k l l (⋀[K]^n E)
      (scalarExtensionExteriorMap K k l E n z) =
      (exteriorBaseChangeEquiv K l E n).symm (_root_.exteriorPower.ιMulti l n
        (fun i => TensorProduct.AlgebraTensorModule.cancelBaseChange K k l l E (z i))) := by
  apply (exteriorBaseChangeEquiv K l E n).injective
  rw [LinearEquiv.apply_symm_apply, exteriorBaseChangeEquiv_tower]
  change _root_.exteriorPower.map n
    (TensorProduct.AlgebraTensorModule.cancelBaseChange K k l l E).toLinearMap
      (exteriorBaseChangeEquiv k l (k ⊗[K] E) n
        ((exteriorBaseChangeEquiv K k E n).toLinearMap.baseChange l
          ((exteriorBaseChangeEquiv K k E n).symm.toLinearMap.baseChange l
            ((exteriorBaseChangeEquiv k l (k ⊗[K] E) n).symm
              (_root_.exteriorPower.ιMulti l n z))))) = _
  have hc (t : l ⊗[k] (⋀[k]^n (k ⊗[K] E))) :
      (exteriorBaseChangeEquiv K k E n).toLinearMap.baseChange l
        ((exteriorBaseChangeEquiv K k E n).symm.toLinearMap.baseChange l t) = t :=
    (LinearEquiv.baseChange k l _ _ (exteriorBaseChangeEquiv K k E n)).apply_symm_apply t
  rw [hc, LinearEquiv.apply_symm_apply, _root_.exteriorPower.map_apply_ιMulti]
  rfl

end ScalarExtensionExterior

section IntermediateFieldExterior

variable (K k L l E : Type*) [Field K] [Field k] [Field L] [Field l]
  [Algebra K k] [Algebra K L] [Algebra k l] [Algebra L l] [Algebra K l]
  [IsScalarTower K k l] [IsScalarTower K L l]
  [AddCommGroup E] [Module K E]

/-- The actual extended wedge is independent of the intermediate field,
through the two canonical tensor-cancellation equivalences. -/
theorem scalarExtensionExteriorMap_changeIntermediateField (n : ℕ)
    (z : Fin n → l ⊗[L] (L ⊗[K] E)) :
    (TensorProduct.AlgebraTensorModule.cancelBaseChange K k l l (⋀[K]^n E)).symm
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K L l l (⋀[K]^n E)
        (scalarExtensionExteriorMap K L l E n z)) =
    scalarExtensionExteriorMap K k l E n (fun i =>
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K k l l E).symm
        (TensorProduct.AlgebraTensorModule.cancelBaseChange K L l l E (z i))) := by
  apply (TensorProduct.AlgebraTensorModule.cancelBaseChange K k l l (⋀[K]^n E)).injective
  rw [LinearEquiv.apply_symm_apply,
    scalarExtensionExteriorMap_cancelBaseChange,
    scalarExtensionExteriorMap_cancelBaseChange]
  simp only [LinearEquiv.apply_symm_apply]

end IntermediateFieldExterior

section CompletedExterior

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (E : Type*) [AddCommGroup E] [Module K E]

/-- Wedge transport through the canonical completed scalar-extension map,
with no basis identification and including degree zero. -/
theorem completedScalarExtensionEquiv_scalarExtensionExteriorMap
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) (h : w.under K = v)
    (n : ℕ) (z : Fin n → w.Completion ⊗[L] (L ⊗[K] E)) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq v w h
    completedScalarExtensionEquiv (⋀[K]^n E) v w h
      (scalarExtensionExteriorMap K L w.Completion E n z) =
    scalarExtensionExteriorMap K v.Completion w.Completion E n
      (fun i => completedScalarExtensionEquiv E v w h (z i)) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq v w h
  let := AbsoluteValue.isScalarTower_completionOfEq v w h
  exact scalarExtensionExteriorMap_changeIntermediateField
    K v.Completion L w.Completion E n z

end CompletedExterior

section DeterminantScalarWedge

private theorem exteriorDegreeInverse_baseChange_ιMulti
    (K l E : Type*) [Field K] [Field l] [Algebra K l]
    [AddCommGroup E] [Module K E] {n m : ℕ} (h : n = m)
    (x : Fin m → l ⊗[K] E) :
    ((exteriorPowerDegreeEquiv K E h).symm.toLinearMap.baseChange l)
      ((exteriorBaseChangeEquiv K l E m).symm (_root_.exteriorPower.ιMulti l m x)) =
    (exteriorBaseChangeEquiv K l E n).symm
      (_root_.exteriorPower.ιMulti l n (fun i => x (finCongr h i))) := by
  subst m
  rw [exteriorPowerDegreeEquiv_rfl]
  change (LinearMap.id.baseChange l) _ = _
  rw [LinearMap.baseChange_id, LinearMap.id_apply]
  rfl

variable (K L l E : Type*) [Field K] [Field L] [Field l]
  [Algebra K L] [Algebra L l] [AddCommGroup E] [Module K E]

/-- The inverse completed determinant scalar map sends a completed wedge
to the actual extended wedge, with only the equality of dimensions as index transport. -/
theorem determinantScalarExtensionEquiv_symm_baseChange_ιMulti
    (z : Fin (Module.finrank L (L ⊗[K] E)) → l ⊗[L] (L ⊗[K] E)) :
    ((determinantScalarExtensionEquiv K L E).symm.toLinearMap.baseChange l)
      ((exteriorBaseChangeEquiv L l (L ⊗[K] E)
        (Module.finrank L (L ⊗[K] E))).symm
        (_root_.exteriorPower.ιMulti l (Module.finrank L (L ⊗[K] E)) z)) =
    scalarExtensionExteriorMap K L l E (Module.finrank K E)
      (fun i => z (finCongr Module.finrank_baseChange.symm i)) := by
  have he : (determinantScalarExtensionEquiv K L E).symm.toLinearMap =
      (exteriorBaseChangeEquiv K L E (Module.finrank K E)).symm.toLinearMap ∘ₗ
        (exteriorPowerDegreeEquiv L (L ⊗[K] E)
          Module.finrank_baseChange.symm).symm.toLinearMap := rfl
  rw [he, LinearMap.baseChange_comp, LinearMap.comp_apply,
    exteriorDegreeInverse_baseChange_ιMulti]
  rfl

/-- The completed scalar determinant map sends the actual extended wedge
to its wedge over the extending field. The degree transport includes rank zero. -/
theorem determinantScalarExtensionEquiv_baseChange_scalarExtensionExteriorMap
    (z : Fin (Module.finrank K E) → l ⊗[L] (L ⊗[K] E)) :
    ((determinantScalarExtensionEquiv K L E).toLinearMap.baseChange l)
      (scalarExtensionExteriorMap K L l E (Module.finrank K E) z) =
    (exteriorBaseChangeEquiv L l (L ⊗[K] E)
      (Module.finrank L (L ⊗[K] E))).symm
      (_root_.exteriorPower.ιMulti l (Module.finrank L (L ⊗[K] E))
        (fun j => z ((finCongr Module.finrank_baseChange.symm).symm j))) := by
  let e : Fin (Module.finrank K E) ≃ Fin (Module.finrank L (L ⊗[K] E)) :=
    finCongr Module.finrank_baseChange.symm
  have h := determinantScalarExtensionEquiv_symm_baseChange_ιMulti K L l E
    (fun j => z (e.symm j))
  have ht : (fun i => z (e.symm (finCongr Module.finrank_baseChange.symm i))) = z := by
    funext i
    exact congrArg z (e.symm_apply_apply i)
  rw [ht] at h
  have hc (t : l ⊗[L] (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E))) :
      ((determinantScalarExtensionEquiv K L E).toLinearMap.baseChange l)
        (((determinantScalarExtensionEquiv K L E).symm.toLinearMap.baseChange l) t) = t :=
    (LinearEquiv.baseChange L l _ _ (determinantScalarExtensionEquiv K L E)).apply_symm_apply t
  calc
    _ = ((determinantScalarExtensionEquiv K L E).toLinearMap.baseChange l)
        (((determinantScalarExtensionEquiv K L E).symm.toLinearMap.baseChange l) _) :=
      congrArg _ h.symm
    _ = _ := hc _

end DeterminantScalarWedge

section CompletedDeterminantScalarWedge

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (E : Type*) [AddCommGroup E] [Module K E]

/-- Canonically embedding an original completed wedge and then extending
the determinant equals the wedge of the embedded completed vectors. -/
theorem determinantScalarExtensionEquiv_baseChange_completed_ιMulti
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) (h : w.under K = v)
    (t : Fin (Module.finrank K E) → v.Completion ⊗[K] E) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq v w h
    ((determinantScalarExtensionEquiv K L E).toLinearMap.baseChange w.Completion)
      ((completedScalarExtensionEquiv (⋀[K]^(Module.finrank K E) E) v w h).symm
        ((1 : w.Completion) ⊗ₜ[v.Completion]
          ((exteriorBaseChangeEquiv K v.Completion E (Module.finrank K E)).symm
            (_root_.exteriorPower.ιMulti v.Completion (Module.finrank K E) t)))) =
    (exteriorBaseChangeEquiv L w.Completion (L ⊗[K] E)
      (Module.finrank L (L ⊗[K] E))).symm
      (_root_.exteriorPower.ιMulti w.Completion (Module.finrank L (L ⊗[K] E))
        (fun j => (completedScalarExtensionEquiv E v w h).symm
          ((1 : w.Completion) ⊗ₜ[v.Completion]
            t ((finCongr Module.finrank_baseChange.symm).symm j)))) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq v w h
  have hc := completedScalarExtensionEquiv_scalarExtensionExteriorMap E v w h
    (Module.finrank K E) (fun i => (completedScalarExtensionEquiv E v w h).symm
      ((1 : w.Completion) ⊗ₜ[v.Completion] t i))
  simp only [LinearEquiv.apply_symm_apply] at hc
  rw [scalarExtensionExteriorMap_one_tmul] at hc
  have he : (completedScalarExtensionEquiv (⋀[K]^(Module.finrank K E) E) v w h).symm
      ((1 : w.Completion) ⊗ₜ[v.Completion]
        ((exteriorBaseChangeEquiv K v.Completion E (Module.finrank K E)).symm
          (_root_.exteriorPower.ιMulti v.Completion (Module.finrank K E) t))) =
      scalarExtensionExteriorMap K L w.Completion E (Module.finrank K E)
        (fun i => (completedScalarExtensionEquiv E v w h).symm
          ((1 : w.Completion) ⊗ₜ[v.Completion] t i)) := by
    apply (completedScalarExtensionEquiv (⋀[K]^(Module.finrank K E) E) v w h).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hc.symm
  rw [he, determinantScalarExtensionEquiv_baseChange_scalarExtensionExteriorMap]

end CompletedDeterminantScalarWedge

namespace NormFamily

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E)

/-- Hadamard's inequality for the actual projectively extended completed
determinant line and arbitrary extended completed vectors. -/
theorem determinant_scalarExtensionProjective_Hadamard (ω : S.Ω)
    (l : Type*) [NormedField l] [NormedAlgebra (S.ϕ ω).Completion l]
    (z : Fin (Module.finrank K E) → l ⊗[(S.ϕ ω).Completion] ((S.ϕ ω).Completion ⊗[K] E)) :
    let := ξ.fibreNormedAddCommGroup ω
    let := ξ.fibreNormedSpace ω
    let := ξ.determinant.fibreNormedAddCommGroup ω
    let := ξ.determinant.fibreNormedSpace ω
    scalarExtensionProjectiveSeminorm
      (scalarExtensionExteriorMap K (S.ϕ ω).Completion l E (Module.finrank K E) z) ≤
        ∏ i, scalarExtensionProjectiveSeminorm (z i) := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := ξ.determinant.fibreNormedAddCommGroup ω
  let := ξ.determinant.fibreNormedSpace ω
  have hb (x : Fin (Module.finrank K E) → (S.ϕ ω).Completion ⊗[K] E) :
      scalarExtensionProjectiveSeminorm
        (scalarExtensionExteriorMap K (S.ϕ ω).Completion l E (Module.finrank K E)
          (fun i => (1 : l) ⊗ₜ[(S.ϕ ω).Completion] x i)) ≤ 1 * ∏ i, ‖x i‖ := by
    rw [scalarExtensionExteriorMap_one_tmul, one_mul]
    exact (scalarExtensionProjectiveSeminorm_one_tmul_le _).trans
      (ξ.determinant_norm_ιMulti_le ω x)
  have h := seminorm_multilinearMap_le_scalarExtensionProjective
    scalarExtensionProjectiveSeminorm
    (scalarExtensionExteriorMap K (S.ϕ ω).Completion l E (Module.finrank K E)).toMultilinearMap
    zero_le_one hb z
  simp only [one_mul] at h
  exact h

/-- Hadamard's inequality for the actual injectively extended determinant
line over a non-Archimedean extending field. The original fibre norm may
be non-ultrametric, and the rank may be zero. -/
theorem determinant_scalarExtensionInjective_Hadamard (ω : S.Ω)
    (l : Type*) [NormedField l] [NormedAlgebra (S.ϕ ω).Completion l]
    (hl : ∀ a b : l, ‖a + b‖ ≤ max ‖a‖ ‖b‖)
    (z : Fin (Module.finrank K E) → l ⊗[(S.ϕ ω).Completion] ((S.ϕ ω).Completion ⊗[K] E)) :
    let := ξ.fibreNormedAddCommGroup ω
    let := ξ.fibreNormedSpace ω
    let := ξ.determinant.fibreNormedAddCommGroup ω
    let := ξ.determinant.fibreNormedSpace ω
    scalarExtensionInjectiveSeminorm
      (scalarExtensionExteriorMap K (S.ϕ ω).Completion l E (Module.finrank K E) z) ≤
        ∏ i, scalarExtensionInjectiveSeminorm (z i) := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := ξ.determinant.fibreNormedAddCommGroup ω
  let := ξ.determinant.fibreNormedSpace ω
  have hb (x : Fin (Module.finrank K E) → (S.ϕ ω).Completion ⊗[K] E) :
      scalarExtensionInjectiveSeminorm
        (scalarExtensionExteriorMap K (S.ϕ ω).Completion l E (Module.finrank K E)
          (fun i => (1 : l) ⊗ₜ[(S.ϕ ω).Completion] x i)) ≤ 1 * ∏ i, ‖x i‖ := by
    rw [scalarExtensionExteriorMap_one_tmul, one_mul]
    exact (scalarExtensionInjectiveSeminorm_one_tmul_le _).trans
      (ξ.determinant_norm_ιMulti_le ω x)
  have h := seminorm_multilinearMap_le_scalarExtensionInjective
    scalarExtensionInjectiveSeminorm (scalarExtensionInjectiveSeminorm_add_le_max hl)
    (scalarExtensionExteriorMap K (S.ϕ ω).Completion l E (Module.finrank K E)).toMultilinearMap
    zero_le_one hb z
  simp only [one_mul] at h
  exact h

section AlgebraicDeterminant

variable {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- Canonically embedded completed base vectors have mixed extended norm
at most their original norm, without normalization or original ultrametricity. -/
theorem scalarExtension_norm_completed_one_tmul_le (x : S.ParameterSpaceExtension L)
    (t : (S.ϕ x.base).Completion ⊗[K] E) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    (ξ.scalarExtension (L := L)).norm x
      ((completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).symm
        ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] t)) ≤ ξ.norm x.base t := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  by_cases hx : x.base ∈ S.Ωfin
  · refine (ξ.scalarExtension_norm_of_mem_Ωfin x hx _).trans_le ?_
    change scalarExtensionInjectiveSeminorm
      (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq
        ((completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).symm
          ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] t))) ≤ _
    rw [LinearEquiv.apply_symm_apply]
    exact scalarExtensionInjectiveSeminorm_one_tmul_le t
  · refine (ξ.scalarExtension_norm_of_not_mem_Ωfin x hx _).trans_le ?_
    change scalarExtensionProjectiveSeminorm
      (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq
        ((completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).symm
          ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] t))) ≤ _
    rw [LinearEquiv.apply_symm_apply]
    exact scalarExtensionProjectiveSeminorm_one_tmul_le t

/-- The actual extended determinant contracts every canonically embedded
completed base determinant vector. The universal property incorporates
scalar-weighted wedge approximation, including the rank-zero determinant. -/
theorem determinant_scalarExtension_norm_completed_one_tmul_le
    (x : S.ParameterSpaceExtension L)
    (u : (S.ϕ x.base).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    (ξ.scalarExtension (L := L)).determinant.norm x
      (((determinantScalarExtensionEquiv K L E).toLinearMap.baseChange x.abv.Completion)
        ((completedScalarExtensionEquiv (⋀[K]^(Module.finrank K E) E)
          (S.ϕ x.base) x.abv x.restrict_eq).symm
          ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] u))) ≤
      ξ.determinant.norm x.base u := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let q : Seminorm x.abv.Completion
      (x.abv.Completion ⊗[L]
        (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E))) :=
    (ξ.scalarExtension (L := L)).determinant.norm x
  let a : x.abv.Completion ⊗[(S.ϕ x.base).Completion]
      ((S.ϕ x.base).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) →ₗ[x.abv.Completion]
      x.abv.Completion ⊗[L]
        (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E)) :=
    ((determinantScalarExtensionEquiv K L E).toLinearMap.baseChange x.abv.Completion).comp
      (completedScalarExtensionEquiv (⋀[K]^(Module.finrank K E) E)
        (S.ϕ x.base) x.abv x.restrict_eq).symm.toLinearMap
  let p : Seminorm (S.ϕ x.base).Completion
      ((S.ϕ x.base).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :=
    ((q.comp a).restrictScalars (S.ϕ x.base).Completion).comp
      (TensorProduct.mk (S.ϕ x.base).Completion x.abv.Completion
        ((S.ϕ x.base).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) 1)
  change p u ≤ _
  apply ξ.seminorm_le_determinant_of_ιMulti_le x.base p ?_ u
  intro t
  change q
    (((determinantScalarExtensionEquiv K L E).toLinearMap.baseChange x.abv.Completion)
      ((completedScalarExtensionEquiv (⋀[K]^(Module.finrank K E) E)
        (S.ϕ x.base) x.abv x.restrict_eq).symm
        ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion]
          ((exteriorBaseChangeEquiv K (S.ϕ x.base).Completion E (Module.finrank K E)).symm
            (_root_.exteriorPower.ιMulti (S.ϕ x.base).Completion (Module.finrank K E) t))))) ≤
      ∏ i, ξ.norm x.base (t i)
  rw [determinantScalarExtensionEquiv_baseChange_completed_ιMulti]
  let e : Fin (Module.finrank K E) ≃ Fin (Module.finrank L (L ⊗[K] E)) :=
    finCongr Module.finrank_baseChange.symm
  let y : Fin (Module.finrank L (L ⊗[K] E)) → x.abv.Completion ⊗[L] (L ⊗[K] E) :=
    fun j => (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).symm
      ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] t (e.symm j))
  change q ((exteriorBaseChangeEquiv L x.abv.Completion (L ⊗[K] E)
    (Module.finrank L (L ⊗[K] E))).symm
      (_root_.exteriorPower.ιMulti x.abv.Completion (Module.finrank L (L ⊗[K] E)) y)) ≤ _
  refine ((ξ.scalarExtension (L := L)).determinant_norm_ιMulti_le x y).trans ?_
  calc
    _ ≤ ∏ i, ξ.norm x.base (t (e.symm i)) :=
      Finset.prod_le_prod₀ (fun i _ => apply_nonneg _ _) fun i _ =>
        ξ.scalarExtension_norm_completed_one_tmul_le x (t (e.symm i))
    _ = ∏ i, ξ.norm x.base (t i) := e.symm.prod_comp (fun i => ξ.norm x.base (t i))

/-- Scalar extension of the actual determinant norm is bounded by the
determinant of the mixed scalar extension, on every completed determinant vector.
Finite places use the produced ultrametric extending field; rank zero is included. -/
theorem determinant_scalarExtension_norm_le (x : S.ParameterSpaceExtension L)
    (z : x.abv.Completion ⊗[L]
      (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E))) :
    (ξ.determinant.scalarExtension (L := L)).norm x
      (((determinantScalarExtensionEquiv K L E).symm.toLinearMap.baseChange
        x.abv.Completion) z) ≤
      (ξ.scalarExtension (L := L)).determinant.norm x z := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let := ξ.determinant.fibreNormedAddCommGroup x.base
  let := ξ.determinant.fibreNormedSpace x.base
  let e : Fin (Module.finrank K E) ≃ Fin (Module.finrank L (L ⊗[K] E)) :=
    finCongr Module.finrank_baseChange.symm
  let q : Seminorm x.abv.Completion
      (x.abv.Completion ⊗[L] (L ⊗[K] (⋀[K]^(Module.finrank K E) E))) :=
    (ξ.determinant.scalarExtension (L := L)).norm x
  let p : Seminorm x.abv.Completion
      (x.abv.Completion ⊗[L]
        (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E))) :=
    q.comp ((determinantScalarExtensionEquiv K L E).symm.toLinearMap.baseChange x.abv.Completion)
  let r : Seminorm x.abv.Completion (x.abv.Completion ⊗[L] (L ⊗[K] E)) :=
    (ξ.scalarExtension (L := L)).norm x
  change p z ≤ _
  apply (ξ.scalarExtension (L := L)).seminorm_le_determinant_of_ιMulti_le x p ?_ z
  intro y
  change Fin (Module.finrank L (L ⊗[K] E)) →
    x.abv.Completion ⊗[L] (L ⊗[K] E) at y
  change q
    (((determinantScalarExtensionEquiv K L E).symm.toLinearMap.baseChange
      x.abv.Completion)
      ((exteriorBaseChangeEquiv L x.abv.Completion (L ⊗[K] E)
        (Module.finrank L (L ⊗[K] E))).symm
        (_root_.exteriorPower.ιMulti x.abv.Completion
          (Module.finrank L (L ⊗[K] E)) y))) ≤ ∏ i, r (y i)
  rw [determinantScalarExtensionEquiv_symm_baseChange_ιMulti]
  change q
    (scalarExtensionExteriorMap K L x.abv.Completion E (Module.finrank K E)
      (fun i => y (e i))) ≤ ∏ i, r (y i)
  by_cases hx : x.base ∈ S.Ωfin
  · have hn (t : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
        r t = scalarExtensionInjectiveSeminorm
          (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq t) := by
      refine (ξ.scalarExtension_norm_of_mem_Ωfin x hx t).trans ?_
      rfl
    refine (ξ.determinant.scalarExtension_norm_of_mem_Ωfin x hx
      (scalarExtensionExteriorMap K L x.abv.Completion E (Module.finrank K E)
        (fun i => y (e i)))).trans_le ?_
    change scalarExtensionInjectiveSeminorm
      (completedScalarExtensionEquiv (⋀[K]^(Module.finrank K E) E)
        (S.ϕ x.base) x.abv x.restrict_eq
        (scalarExtensionExteriorMap K L x.abv.Completion E (Module.finrank K E)
          (fun i => y (e i)))) ≤ _
    rw [completedScalarExtensionEquiv_scalarExtensionExteriorMap]
    refine (ξ.determinant_scalarExtensionInjective_Hadamard x.base x.abv.Completion
      ((S.algebraicExtension L).norm_add_le_max_of_finite x
        ((AdelicStructure.mem_Ωfin_algebraicExtension_iff x).2 hx))
      (fun i => completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq
        (y (e i)))).trans_eq ?_
    calc
      _ = ∏ i, r (y (e i)) :=
        Finset.prod_congr rfl fun i _ => (hn (y (e i))).symm
      _ = ∏ i, r (y i) := e.prod_comp (fun i => r (y i))
  · have hn (t : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
        r t = scalarExtensionProjectiveSeminorm
          (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq t) := by
      refine (ξ.scalarExtension_norm_of_not_mem_Ωfin x hx t).trans ?_
      rfl
    refine (ξ.determinant.scalarExtension_norm_of_not_mem_Ωfin x hx
      (scalarExtensionExteriorMap K L x.abv.Completion E (Module.finrank K E)
        (fun i => y (e i)))).trans_le ?_
    change scalarExtensionProjectiveSeminorm
      (completedScalarExtensionEquiv (⋀[K]^(Module.finrank K E) E)
        (S.ϕ x.base) x.abv x.restrict_eq
        (scalarExtensionExteriorMap K L x.abv.Completion E (Module.finrank K E)
          (fun i => y (e i)))) ≤ _
    rw [completedScalarExtensionEquiv_scalarExtensionExteriorMap]
    refine (ξ.determinant_scalarExtensionProjective_Hadamard x.base x.abv.Completion
      (fun i => completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq
        (y (e i)))).trans_eq ?_
    calc
      _ = ∏ i, r (y (e i)) :=
        Finset.prod_congr rfl fun i _ => (hn (y (e i))).symm
      _ = ∏ i, r (y i) := e.prod_comp (fun i => r (y i))

/-- The actual extending determinant is bounded by scalar extension of the
original determinant, on every completed vector and in every rank. -/
theorem scalarExtension_determinant_norm_le (x : S.ParameterSpaceExtension L)
    (z : x.abv.Completion ⊗[L]
      (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E))) :
    (ξ.scalarExtension (L := L)).determinant.norm x z ≤
    (ξ.determinant.scalarExtension (L := L)).norm x
      (((determinantScalarExtensionEquiv K L E).symm.toLinearMap.baseChange
        x.abv.Completion) z) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.determinant.fibreNormedAddCommGroup x.base
  let := ξ.determinant.fibreNormedSpace x.base
  let q : Seminorm x.abv.Completion
      (x.abv.Completion ⊗[L]
        (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E))) :=
    (ξ.scalarExtension (L := L)).determinant.norm x
  let a : x.abv.Completion ⊗[(S.ϕ x.base).Completion]
      ((S.ϕ x.base).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) →ₗ[x.abv.Completion]
      x.abv.Completion ⊗[L]
        (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E)) :=
    ((determinantScalarExtensionEquiv K L E).toLinearMap.baseChange x.abv.Completion).comp
      (completedScalarExtensionEquiv (⋀[K]^(Module.finrank K E) E)
        (S.ϕ x.base) x.abv x.restrict_eq).symm.toLinearMap
  let y := completedScalarExtensionEquiv (⋀[K]^(Module.finrank K E) E)
    (S.ϕ x.base) x.abv x.restrict_eq
    (((determinantScalarExtensionEquiv K L E).symm.toLinearMap.baseChange x.abv.Completion) z)
  have hc : a y = z := by
    change ((determinantScalarExtensionEquiv K L E).toLinearMap.baseChange x.abv.Completion)
      ((completedScalarExtensionEquiv (⋀[K]^(Module.finrank K E) E)
        (S.ϕ x.base) x.abv x.restrict_eq).symm
        (completedScalarExtensionEquiv (⋀[K]^(Module.finrank K E) E)
          (S.ϕ x.base) x.abv x.restrict_eq
          (((determinantScalarExtensionEquiv K L E).symm.toLinearMap.baseChange
            x.abv.Completion) z))) = z
    rw [LinearEquiv.symm_apply_apply]
    exact (LinearEquiv.baseChange L x.abv.Completion _ _
      (determinantScalarExtensionEquiv K L E)).apply_symm_apply z
  have hf (u : (S.ϕ x.base).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
      q (a ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] u)) ≤ 1 * ‖u‖ := by
    rw [one_mul]
    exact ξ.determinant_scalarExtension_norm_completed_one_tmul_le x u
  change q z ≤ _
  by_cases hx : x.base ∈ S.Ωfin
  · have hq : ∀ s t : x.abv.Completion ⊗[L]
        (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E)),
        q (s + t) ≤ max (q s) (q t) :=
      ((ξ.scalarExtension (L := L)).determinant.isUltrametric_of_finrank_le_one
        (determinant_finrank (K := L) (E := L ⊗[K] E)).le)
        x ((AdelicStructure.mem_Ωfin_algebraicExtension_iff x).2 hx)
    have h := seminorm_linearMap_le_scalarExtensionInjective q hq a zero_le_one hf y
    rw [hc, one_mul] at h
    refine h.trans_eq ?_
    exact (ξ.determinant.scalarExtension_norm_of_mem_Ωfin x hx _).symm
  · have h := seminorm_linearMap_le_scalarExtensionProjective q a zero_le_one hf y
    rw [hc, one_mul] at h
    refine h.trans_eq ?_
    exact (ξ.determinant.scalarExtension_norm_of_not_mem_Ωfin x hx _).symm

/-- Determinants commute isometrically with actual mixed scalar extension
on canonically identified completed determinant lines, including rank zero. -/
theorem determinant_scalarExtension_norm_eq (x : S.ParameterSpaceExtension L)
    (z : x.abv.Completion ⊗[L]
      (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E))) :
    (ξ.scalarExtension (L := L)).determinant.norm x z =
    (ξ.determinant.scalarExtension (L := L)).norm x
      (((determinantScalarExtensionEquiv K L E).symm.toLinearMap.baseChange
        x.abv.Completion) z) :=
  le_antisymm (ξ.scalarExtension_determinant_norm_le x z)
    (ξ.determinant_scalarExtension_norm_le x z)

end AlgebraicDeterminant

section AlgebraicLine

variable {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The accepted local line formula gives exact rational-generator norms
for the actual mixed scalar-extension family, at every extending place. -/
theorem scalarExtension_norm_basis_zero (b : Module.Basis (Fin 1) K E)
    (x : S.ParameterSpaceExtension L) :
    (ξ.scalarExtension (L := L)).norm x
      ((1 : x.abv.Completion) ⊗ₜ[L] ((1 : L) ⊗ₜ[K] b 0)) =
      ξ.norm x.base ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] b 0) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  have h := scalarExtensionSeminorms_tmul_of_basis
    (b.baseChange (S.ϕ x.base).Completion) (1 : x.abv.Completion)
  simp only [Module.Basis.baseChange_apply, norm_one, one_mul] at h
  by_cases hx : x.base ∈ S.Ωfin
  · refine (ξ.scalarExtension_norm_of_mem_Ωfin x hx
      ((1 : x.abv.Completion) ⊗ₜ[L] ((1 : L) ⊗ₜ[K] b 0))).trans ?_
    change scalarExtensionInjectiveSeminorm
      (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq _) = _
    rw [completedScalarExtensionEquiv_tmul, map_one, one_mul]
    exact h.2
  · refine (ξ.scalarExtension_norm_of_not_mem_Ωfin x hx
      ((1 : x.abv.Completion) ⊗ₜ[L] ((1 : L) ⊗ₜ[K] b 0))).trans ?_
    change scalarExtensionProjectiveSeminorm
      (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq _) = _
    rw [completedScalarExtensionEquiv_tmul, map_one, one_mul]
    exact h.1

/-- The extended rational line generator has the pullback logarithmic norm. -/
theorem scalarExtension_logNorm_basis_zero (b : Module.Basis (Fin 1) K E)
    (x : S.ParameterSpaceExtension L) :
    (ξ.scalarExtension (L := L)).logNorm ((b.baseChange L) 0) x =
      ξ.logNorm (b 0) x.base := by
  change Real.log ((ξ.scalarExtension (L := L)).norm x
      ((1 : x.abv.Completion) ⊗ₜ[L] ((b.baseChange L) 0))) = _
  rw [Module.Basis.baseChange_apply]
  exact congrArg Real.log (ξ.scalarExtension_norm_basis_zero b x)

variable {ξ}

/-- An actual measurable line remains measurable under every algebraic
scalar extension, with no density or normalization condition. -/
theorem IsMeasurable.scalarExtension_of_finrank_one (hm : ξ.IsMeasurable)
    (hr : Module.finrank K E = 1) : (ξ.scalarExtension (L := L)).IsMeasurable := by
  let : MeasurableSpace (S.ParameterSpaceExtension L) :=
    AdelicStructure.Algebraic.projectiveMeasurableSpace S L
  let b := Module.finBasisOfFinrankEq K E hr
  apply ((ξ.scalarExtension (L := L)).isMeasurable_iff_norm_one_vector
    (Module.finrank_baseChange.trans hr) ((b.baseChange L).ne_zero 0)).2
  change Measurable (fun x : S.ParameterSpaceExtension L =>
    (ξ.scalarExtension (L := L)).norm x ((1 : x.abv.Completion) ⊗ₜ[L]
      ((b.baseChange L) 0)))
  have he : (fun x : S.ParameterSpaceExtension L =>
      (ξ.scalarExtension (L := L)).norm x
        ((1 : x.abv.Completion) ⊗ₜ[L] ((b.baseChange L) 0))) =
      (fun x => ξ.norm x.proj ((1 : (S.ϕ x.proj).Completion) ⊗ₜ[K] b 0)) := by
    funext x
    rw [Module.Basis.baseChange_apply]
    exact ξ.scalarExtension_norm_basis_zero b x
  rw [he]
  exact (hm (b 0)).comp (AdelicStructure.Algebraic.measurable_proj_projective S L)

/-- Integrability of the actual rational generator gives domination of
the extended line. This uses the produced extension measure identity. -/
theorem IsDominated.scalarExtension_of_finrank_one (hd : ξ.IsDominated)
    (hm : ξ.IsMeasurable) (hr : Module.finrank K E = 1) :
    (ξ.scalarExtension (L := L)).IsDominated := by
  let b := Module.finBasisOfFinrankEq K E hr
  apply ((ξ.scalarExtension (L := L)).isDominated_iff_logNorm_bounds
    (Module.finrank_baseChange.trans hr) ((b.baseChange L).ne_zero 0)).2
  apply integrable_hasIntegrableBounds
  have hi := AdelicStructure.Algebraic.integrable_comp_proj_measure S L
    (hd.integrable_logNorm hm (b 0))
  change Integrable (fun x : S.ParameterSpaceExtension L =>
    (ξ.scalarExtension (L := L)).logNorm ((b.baseChange L) 0) x)
      (AdelicStructure.Algebraic.measure S L)
  have he : (fun x : S.ParameterSpaceExtension L =>
      (ξ.scalarExtension (L := L)).logNorm ((b.baseChange L) 0) x) =
      (fun x => ξ.logNorm (b 0) x.proj) :=
    funext fun x => ξ.scalarExtension_logNorm_basis_zero b x
  rw [he]
  exact hi

end AlgebraicLine

section AlgebraicDeterminantLine

variable {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The actual extended determinant is the rational pullback along the
canonical determinant equivalence. -/
theorem determinant_scalarExtension_eq_pullback :
    (ξ.scalarExtension (L := L)).determinant =
      (ξ.determinant.scalarExtension (L := L)).pullback
        (determinantScalarExtensionEquiv K L E).symm.toLinearMap
        (determinantScalarExtensionEquiv K L E).symm.injective := by
  apply NormFamily.ext
  intro x z
  exact ξ.determinant_scalarExtension_norm_eq x z

variable {ξ}

/-- Measurability of the original determinant gives measurability of the
actual extended determinant. -/
theorem IsMeasurable.determinant_scalarExtension (hm : ξ.determinant.IsMeasurable) :
    (ξ.scalarExtension (L := L)).determinant.IsMeasurable := by
  rw [ξ.determinant_scalarExtension_eq_pullback]
  exact (hm.scalarExtension_of_finrank_one determinant_finrank).pullback
    (determinantScalarExtensionEquiv K L E).symm.toLinearMap
    (determinantScalarExtensionEquiv K L E).symm.injective

/-- Domination of the original measurable determinant transfers through the
actual determinant isometry. -/
theorem IsDominated.determinant_scalarExtension (hd : ξ.determinant.IsDominated)
    (hm : ξ.determinant.IsMeasurable) :
    (ξ.scalarExtension (L := L)).determinant.IsDominated := by
  rw [ξ.determinant_scalarExtension_eq_pullback]
  exact (hd.scalarExtension_of_finrank_one hm determinant_finrank).pullback
    (determinantScalarExtensionEquiv K L E).symm.toLinearMap
    (determinantScalarExtensionEquiv K L E).symm.injective

end AlgebraicDeterminantLine

end NormFamily

namespace AdelicVectorBundle

universe u w wL

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- Actual scalar extension of an adelic line, with both measurability
clauses and domination proved from its rational generator. -/
abbrev scalarExtensionLine (V : AdelicVectorBundle S) [hV : V.IsLine] :
    AdelicVectorBundle (S.algebraicExtension L) :=
  ofLine (V.toNormFamily.scalarExtension (L := L)) (Module.finrank_baseChange.trans hV.rank_eq_one)
    (hm := (V.isMeasurable.scalarExtension_of_finrank_one hV.rank_eq_one))
    (hd := (V.isDominated.scalarExtension_of_finrank_one V.isMeasurable hV.rank_eq_one))

/-- Scalar extension preserves the rank-one assertion. -/
instance scalarExtensionLine_isLine (V : AdelicVectorBundle S) [hV : V.IsLine] :
    (V.scalarExtensionLine (L := L)).IsLine := ⟨Module.finrank_baseChange.trans hV.rank_eq_one⟩

/-- The line part of source Proposition 4.3.14: scalar extension preserves
Arakelov degree on every algebraic extension of a proper adelic curve. -/
theorem lineDegree_scalarExtensionLine [S.IsProper] (V : AdelicVectorBundle S)
    [hV : V.IsLine] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.scalarExtensionLine (L := L)).lineDegree (hV := (V.scalarExtensionLine_isLine)) =
      V.lineDegree := by
  intro hp
  let := hp
  let b := Module.finBasisOfFinrankEq K V hV.rank_eq_one
  rw [lineDegree_eq_neg_integral _ ⟨(b.baseChange L) 0, (b.baseChange L).ne_zero 0⟩,
    lineDegree_eq_neg_integral V ⟨b 0, b.ne_zero 0⟩]
  change -(∫ x, (V.toNormFamily.scalarExtension (L := L)).logNorm ((b.baseChange L) 0) x
      ∂AdelicStructure.Algebraic.measure S L) = _
  have he : (fun x : S.ParameterSpaceExtension L =>
      (V.toNormFamily.scalarExtension (L := L)).logNorm ((b.baseChange L) 0) x) =
      (fun x => V.toNormFamily.logNorm (b 0) x.proj) :=
    funext fun x => V.toNormFamily.scalarExtension_logNorm_basis_zero b x
  rw [he, AdelicStructure.Algebraic.integral_comp_proj_measure S L (V.integrable_logNorm (b 0))]

/-- The actual determinant of the ordinary scalar extension is an adelic line.
The hypotheses establish adelicity of the original determinant; no measurability
hypothesis on the whole extended vector family is used. -/
abbrev scalarExtensionDeterminant (V : AdelicVectorBundle S)
    [hbase : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    AdelicVectorBundle (S.algebraicExtension L) :=
  ofLine (V.toNormFamily.scalarExtension (L := L)).determinant
    NormFamily.determinant_finrank
    (hm := (V.isMeasurable.determinant_of_discrete_or_countable).determinant_scalarExtension)
    (hd := NormFamily.IsDominated.determinant_scalarExtension (ξ := V.toNormFamily)
      (V.determinantOfMeasurableBase).isDominated
      (V.isMeasurable.determinant_of_discrete_or_countable))

@[simp]
theorem scalarExtensionDeterminant_toNormFamily (V : AdelicVectorBundle S)
    [hbase : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (V.scalarExtensionDeterminant (L := L)).toNormFamily =
      (V.toNormFamily.scalarExtension (L := L)).determinant := rfl

/-- The actual extended determinant has rank one, including when the
original vector space has rank zero. -/
instance scalarExtensionDeterminant_isLine (V : AdelicVectorBundle S)
    [hbase : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (V.scalarExtensionDeterminant (L := L)).IsLine :=
  ⟨NormFamily.determinant_finrank⟩

/-- The ordinary scalar extension's actual determinant-line degree equals
the original vector-bundle degree on every algebraic extension. -/
theorem lineDegree_scalarExtensionDeterminant [S.IsProper] (V : AdelicVectorBundle S)
    [hbase : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.scalarExtensionDeterminant (L := L)).lineDegree
      (hV := (V.scalarExtensionDeterminant_isLine)) = V.degree := by
  intro hp
  let := hp
  let D := V.determinantOfMeasurableBase
  let hD := V.determinantOfMeasurableBase_isLine
  let W := D.scalarExtensionLine (L := L) (hV := hD)
  let hW := D.scalarExtensionLine_isLine (L := L) (hV := hD)
  let U := V.scalarExtensionDeterminant (L := L)
  let hU := V.scalarExtensionDeterminant_isLine (L := L)
  have hd : W.lineDegree (hV := hW) = U.lineDegree (hV := hU) := by
    apply lineDegree_eq_of_norm_rational_eq W U (hV := hW) (hW := hU)
      (determinantScalarExtensionEquiv K L V)
    intro x s
    change S.ParameterSpaceExtension L at x
    change (V.toNormFamily.determinant.scalarExtension (L := L)).norm x
        ((1 : x.abv.Completion) ⊗ₜ[L] s) =
      (V.toNormFamily.scalarExtension (L := L)).determinant.norm x
        ((1 : x.abv.Completion) ⊗ₜ[L] determinantScalarExtensionEquiv K L V s)
    have h := V.toNormFamily.determinant_scalarExtension_norm_eq x
      ((1 : x.abv.Completion) ⊗ₜ[L] determinantScalarExtensionEquiv K L V s)
    have he :
        ((determinantScalarExtensionEquiv K L V).symm.toLinearMap.baseChange
          x.abv.Completion)
            ((1 : x.abv.Completion) ⊗ₜ[L] determinantScalarExtensionEquiv K L V s) =
          (1 : x.abv.Completion) ⊗ₜ[L] s := by
      rw [LinearMap.baseChange_tmul]
      exact congrArg (fun t => (1 : x.abv.Completion) ⊗ₜ[L] t)
        ((determinantScalarExtensionEquiv K L V).symm_apply_apply s)
    exact (h.trans (congrArg
      ((V.toNormFamily.determinant.scalarExtension (L := L)).norm x) he)).symm
  calc
    _ = W.lineDegree (hV := hW) := hd.symm
    _ = D.lineDegree (hV := hD) := D.lineDegree_scalarExtensionLine (hV := hD)
    _ = V.degree := rfl

end AdelicVectorBundle

end

end ArakelovGeometry
