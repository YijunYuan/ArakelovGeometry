/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.Tensor.Operator
import ArakelovGeometry.Analysis.Determinant.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Order.Lattice

/-!
# Bilinear bounds and completed tensor dual norms

The injective contraction principle applies to different finite-dimensional
factors and arbitrary ultrametric targets. No ultrametric assumption on the
factor norms is imposed.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

/-- A pure-tensor product bound contracts the injective norm for an arbitrary
finite family of factors and an ultrametric target. -/
theorem norm_linearMap_le_injective_of_ultrametric_factors
    {L : Type*} [NormedField L] [CompleteSpace L]
    {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace L (E i)]
    [∀ i, FiniteDimensional L (E i)] {W : Type*}
    [SeminormedAddCommGroup W] [NormedSpace L W]
    (f : (⨂[L] i, E i) →ₗ[L] W)
    (hW : ∀ x y : W, ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (hf : ∀ x : ∀ i, E i, ‖f (⨂ₜ[L] i, x i)‖ ≤ ∏ i, ‖x i‖)
    (z : ⨂[L] i, E i) : ‖f z‖ ≤ injectiveTensorSeminorm z := by
  classical
  have hαbound (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
      ‖f z‖ ≤ injectiveTensorSeminorm z * α⁻¹ ^ Fintype.card ι := by
    choose e he using fun i ↦ exists_finBasis_mul_dual_norm_le (L := L) (E := E i) hα hα1
    let B := Basis.piTensorProduct e
    have hC : 0 ≤ injectiveTensorSeminorm z * α⁻¹ ^ Fintype.card ι :=
      mul_nonneg (apply_nonneg _ _) (pow_nonneg (inv_nonneg.mpr hα.le) _)
    calc
      ‖f z‖ = ‖∑ p, (B.repr z) p • f (B p)‖ := by
        simpa only [map_sum, map_smul] using congrArg norm (congrArg f (B.sum_repr z)).symm
      _ ≤ injectiveTensorSeminorm z * α⁻¹ ^ Fintype.card ι := by
        have : IsUltrametricDist W :=
          IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr hW
        apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC
        intro p _
        have hp := norm_tensorDualEval_le_injective (fun i : ι ↦ (e i).coord (p i)) z
        rw [tensorDualEval_coord] at hp
        change ‖(B.repr z) p‖ ≤ injectiveTensorSeminorm z *
          ∏ i, linearMapOperatorSeminorm ((e i).coord (p i)) at hp
        have hb : ‖f (B p)‖ ≤ ∏ i, ‖e i (p i)‖ := by
          simpa only [B, Basis.piTensorProduct_apply] using hf (fun i ↦ e i (p i))
        calc
          ‖(B.repr z) p • f (B p)‖ = ‖(B.repr z) p‖ * ‖f (B p)‖ := norm_smul _ _
          _ ≤ (injectiveTensorSeminorm z * ∏ i, linearMapOperatorSeminorm ((e i).coord (p i))) *
              ∏ i, ‖e i (p i)‖ := mul_le_mul hp hb (norm_nonneg _) (by positivity)
          _ = injectiveTensorSeminorm z *
              ∏ i, ‖e i (p i)‖ * linearMapOperatorSeminorm ((e i).coord (p i)) := by
            rw [Finset.prod_mul_distrib]
            ring
          _ ≤ injectiveTensorSeminorm z * ∏ _ : ι, α⁻¹ := by
            apply mul_le_mul_of_nonneg_left _ (apply_nonneg _ _)
            exact Finset.prod_le_prod₀ (fun _ _ ↦ mul_nonneg (norm_nonneg _) (apply_nonneg _ _))
              (fun i _ ↦ (he i (p i)).2)
          _ = injectiveTensorSeminorm z * α⁻¹ ^ Fintype.card ι := by
            rw [Finset.prod_const, Finset.card_univ]
  have hlim : Filter.Tendsto (fun α : ℝ ↦ injectiveTensorSeminorm z * α⁻¹ ^ Fintype.card ι)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (injectiveTensorSeminorm z)) := by
    have hc : ContinuousAt (fun α : ℝ ↦ injectiveTensorSeminorm z * α⁻¹ ^ Fintype.card ι) 1 := by
      exact continuousAt_const.mul ((continuousAt_id.inv₀ one_ne_zero).pow _)
    simpa only [inv_one, one_pow, mul_one] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (zero_lt_one : (0 : ℝ) < 1))]
    with α hα1 hα
  exact hαbound α hα hα1

/-- The dependent-factor injective contraction also allows any nonnegative
pure-tensor bound. -/
theorem norm_linearMap_le_mul_injective_of_ultrametric_factors
    {L : Type*} [NormedField L] [CompleteSpace L]
    {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace L (E i)]
    [∀ i, FiniteDimensional L (E i)] {W : Type*}
    [SeminormedAddCommGroup W] [NormedSpace L W]
    (f : (⨂[L] i, E i) →ₗ[L] W)
    (hW : ∀ x y : W, ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x : ∀ i, E i, ‖f (⨂ₜ[L] i, x i)‖ ≤ C * ∏ i, ‖x i‖)
    (z : ⨂[L] i, E i) : ‖f z‖ ≤ C * injectiveTensorSeminorm z := by
  by_cases hzero : C = 0
  · simpa only [hzero, zero_mul] using
      norm_linearMap_le_projective_of_tprod_le f hC hf z
  have hpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hzero)
  let p : Seminorm L W := NNReal.mk C⁻¹ (inv_nonneg.mpr hC) • normSeminorm L W
  have hp (x : W) : p x = C⁻¹ * ‖x‖ := rfl
  have hpu : ∀ x y, p (x + y) ≤ max (p x) (p y) := by
    intro x y
    simp only [hp]
    rw [← mul_max_of_nonneg _ _ (inv_nonneg.mpr hC)]
    exact mul_le_mul_of_nonneg_left (hW x y) (inv_nonneg.mpr hC)
  have hpf : ∀ x : ∀ i, E i, p (f (⨂ₜ[L] i, x i)) ≤ ∏ i, ‖x i‖ := by
    intro x
    rw [hp, inv_mul_le_iff₀ hpos]
    exact hf x
  have hbound : p (f z) ≤ injectiveTensorSeminorm z := by
    let m : Module L W := inferInstance
    let : SeminormedAddCommGroup W := p.toAddGroupSeminorm.toSeminormedAddCommGroup
    let : Module L W := m
    let : NormedSpace L W := ⟨fun a x ↦ (map_smul_eq_mul p a x).le⟩
    exact norm_linearMap_le_injective_of_ultrametric_factors f hpu hpf z
  rw [hp, inv_mul_le_iff₀ hpos] at hbound
  exact hbound

/-- Pullback along a linear isometric equivalence preserves the operator
norm, including over trivially valued complete fields. -/
theorem linearMapOperatorSeminorm_comp_isometryEquiv
    {L : Type*} [NormedField L] [CompleteSpace L]
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace L V]
    [FiniteDimensional L V] [NormedAddCommGroup W] [NormedSpace L W]
    [FiniteDimensional L W] (e : V ≃ₗᵢ[L] W) (f : W →ₗ[L] L) :
    linearMapOperatorSeminorm (f.comp e.toLinearEquiv.toLinearMap) =
      linearMapOperatorSeminorm f := by
  rw [linearMapOperatorSeminorm_eq_sSup, linearMapOperatorSeminorm_eq_sSup]
  congr 1
  ext r
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨e x, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, e.norm_map]
  · rintro ⟨y, rfl⟩
    refine ⟨e.symm y, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      e.apply_symm_apply, e.symm.norm_map]

/-- The actual injective tensor seminorm is invariant under isometries of
all its finite-dimensional factors. -/
theorem injectiveTensorSeminorm_congr_linearIsometryEquiv
    {L : Type*} [NormedField L] [CompleteSpace L]
    {ι : Type*} [Fintype ι] {V W : ι → Type*}
    [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace L (V i)]
    [∀ i, FiniteDimensional L (V i)]
    [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace L (W i)]
    [∀ i, FiniteDimensional L (W i)] (e : ∀ i, V i ≃ₗᵢ[L] W i)
    (z : ⨂[L] i, V i) :
    injectiveTensorSeminorm (PiTensorProduct.congr (fun i ↦ (e i).toLinearEquiv) z) =
      injectiveTensorSeminorm z := by
  have heval (φ : ∀ i, Module.Dual L (W i)) :
      tensorDualEval φ (PiTensorProduct.congr (fun i ↦ (e i).toLinearEquiv) z) =
        tensorDualEval (fun i ↦ (φ i).comp (e i).toLinearEquiv.toLinearMap) z := by
    have he : (tensorDualEval φ).comp
        (PiTensorProduct.congr (fun i ↦ (e i).toLinearEquiv)).toLinearMap =
        tensorDualEval (fun i ↦ (φ i).comp (e i).toLinearEquiv.toLinearMap) := by
      apply PiTensorProduct.ext
      ext x
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, PiTensorProduct.congr_tprod, tensorDualEval_tprod]
    exact LinearMap.congr_fun he z
  rw [injectiveTensorSeminorm_eq_sSup, injectiveTensorSeminorm_eq_sSup]
  congr 1
  ext r
  constructor
  · rintro ⟨φ, rfl⟩
    refine ⟨fun i ↦ (φ i).comp (e i).toLinearEquiv.toLinearMap, ?_⟩
    simp only [heval, linearMapOperatorSeminorm_comp_isometryEquiv]
  · rintro ⟨φ, rfl⟩
    let ψ i := (φ i).comp (e i).symm.toLinearEquiv.toLinearMap
    refine ⟨ψ, ?_⟩
    have hc : (fun i ↦ (ψ i).comp (e i).toLinearEquiv.toLinearMap) = φ := by
      funext i
      ext x
      simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply]
    simp only [heval, hc, ψ, linearMapOperatorSeminorm_comp_isometryEquiv]

section BinaryDual

variable {L : Type*} [NormedField L] [CompleteSpace L]
  {E : Unit ⊕ Unit → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace L (E i)] [∀ i, FiniteDimensional L (E i)]

omit [CompleteSpace L] [∀ i, FiniteDimensional L (E i)] in
/-- Dual tensor evaluation can be curried and tested successively by the
two bidual functionals. -/
theorem tensorDualEval_dual_eq_curry
    (φ : ∀ i, Module.Dual L (Module.Dual L (E i)))
    (z : ⨂[L] i, Module.Dual L (E i)) :
    PiTensorProduct.dualDistrib (⨂ₜ[L] i, φ i) z = φ (.inl ())
      ((φ (.inr ())).comp
        (dualTensorHom L (E (.inl ())) (Module.Dual L (E (.inr ())))
          (binaryTensorEquiv L (fun i ↦ Module.Dual L (E i)) z))) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod a x =>
    have hc : (φ (.inr ())).comp
        (dualTensorHom L (E (.inl ())) (Module.Dual L (E (.inr ())))
          (x (.inl ()) ⊗ₜ[L] x (.inr ()))) =
        φ (.inr ()) (x (.inr ())) • x (.inl ()) := by
      ext y
      simp only [LinearMap.comp_apply, dualTensorHom_apply, map_smul,
        LinearMap.smul_apply, smul_eq_mul]
      exact mul_comm _ _
    simp only [map_smul, PiTensorProduct.dualDistrib_apply, binaryTensorEquiv_tprod,
      LinearMap.comp_smul, hc, Fintype.prod_sum_type, Fintype.prod_unique, smul_eq_mul]
    rw [mul_comm (φ (.inl ()) (x (.inl ())))]
  | add z t hz ht =>
    simpa only [map_add, LinearMap.comp_add] using congrArg₂ (· + ·) hz ht

/-- The injective norm on a tensor of the two operator-normed duals is
characterized by its bilinear bound on the original spaces. -/
theorem injectiveTensorSeminorm_dual_le_iff
    (z : ⨂[L] i, Module.Dual L (E i)) {C : ℝ} (hC : 0 ≤ C) :
    let := fun i ↦ linearDualNormedAddCommGroup (k := L) (E := E i)
    let := fun i ↦ linearDualNormedSpace (k := L) (E := E i)
    injectiveTensorSeminorm z ≤ C ↔
      ∀ (x : E (.inl ())) (y : E (.inr ())),
        ‖dualTensorHom L (E (.inl ())) (Module.Dual L (E (.inr ())))
          (binaryTensorEquiv L (fun i ↦ Module.Dual L (E i)) z) x y‖ ≤
            C * ‖x‖ * ‖y‖ := by
  intro dualGroups dualSpaces
  let := dualGroups
  let := dualSpaces
  let B := dualTensorHom L (E (.inl ())) (Module.Dual L (E (.inr ())))
    (binaryTensorEquiv L (fun i ↦ Module.Dual L (E i)) z)
  have heval (x : E (.inl ())) (y : E (.inr ())) :
      tensorDualEval (Sum.rec (fun _ ↦ Module.Dual.eval L _ x)
        (fun _ ↦ Module.Dual.eval L _ y)) z = B x y := by
    rw [tensorDualEval, tensorDualEval_dual_eq_curry]
    rfl
  have hevnorm (i : Unit ⊕ Unit) (x : E i) :
      linearMapOperatorSeminorm (Module.Dual.eval L (E i) x) ≤ ‖x‖ := by
    apply linearMapOperatorSeminorm_le _ (norm_nonneg x)
    intro f
    change ‖f x‖ ≤ ‖x‖ * linearMapOperatorSeminorm f
    simpa only [mul_comm] using norm_linearMap_apply_le f x
  constructor
  · intro h x y
    have hv := norm_tensorDualEval_le_injective
      (Sum.rec (fun _ ↦ Module.Dual.eval L _ x) (fun _ ↦ Module.Dual.eval L _ y)) z
    simp only [heval, Fintype.prod_sum_type, Fintype.prod_unique] at hv
    apply hv.trans
    calc
      injectiveTensorSeminorm z *
          (linearMapOperatorSeminorm (Module.Dual.eval L _ x) *
            linearMapOperatorSeminorm (Module.Dual.eval L _ y)) ≤
          C * (‖x‖ * ‖y‖) :=
        mul_le_mul h (mul_le_mul (hevnorm _ x) (hevnorm _ y)
          (apply_nonneg _ _) (norm_nonneg _)) (by positivity) hC
      _ = _ := (mul_assoc _ _ _).symm
  · intro h
    have hB (x : E (.inl ())) : ‖B x‖ ≤ C * ‖x‖ := by
      change linearMapOperatorSeminorm (B x) ≤ _
      apply linearMapOperatorSeminorm_le _ (mul_nonneg hC (norm_nonneg x))
      exact h x
    apply (injectiveTensorSeminorm_le_iff z C).mpr
    intro φ
    let g := (φ (.inr ())).comp B
    have hg : linearMapOperatorSeminorm g ≤
        linearMapOperatorSeminorm (φ (.inr ())) * C := by
      apply linearMapOperatorSeminorm_le _ (mul_nonneg (apply_nonneg _ _) hC)
      intro x
      calc
        ‖g x‖ ≤ linearMapOperatorSeminorm (φ (.inr ())) * ‖B x‖ :=
          norm_linearMap_apply_le (φ (.inr ())) (B x)
        _ ≤ linearMapOperatorSeminorm (φ (.inr ())) * (C * ‖x‖) :=
          mul_le_mul_of_nonneg_left (hB x) (apply_nonneg _ _)
        _ = _ := (mul_assoc _ _ _).symm
    have hv : ‖tensorDualEval φ z‖ ≤ C * ∏ i, linearMapOperatorSeminorm (φ i) := by
      rw [tensorDualEval, tensorDualEval_dual_eq_curry]
      change ‖φ (.inl ()) g‖ ≤ _
      calc
        ‖φ (.inl ()) g‖ ≤ linearMapOperatorSeminorm (φ (.inl ())) * ‖g‖ :=
          norm_linearMap_apply_le _ _
        _ ≤ linearMapOperatorSeminorm (φ (.inl ())) *
            (linearMapOperatorSeminorm (φ (.inr ())) * C) :=
          mul_le_mul_of_nonneg_left hg (apply_nonneg _ _)
        _ = _ := by simp only [Fintype.prod_sum_type, Fintype.prod_unique]; ring
    by_cases hd : (∏ i, linearMapOperatorSeminorm (φ i)) = 0
    · simpa only [hd, div_zero] using hC
    · exact (div_le_iff₀ (lt_of_le_of_ne
        (Finset.prod_nonneg fun i _ ↦ apply_nonneg _ _) (Ne.symm hd))).mpr hv

end BinaryDual

end

end ArakelovGeometry
