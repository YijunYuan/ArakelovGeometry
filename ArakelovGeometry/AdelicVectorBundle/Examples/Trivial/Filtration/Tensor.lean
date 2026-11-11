/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.LinearAlgebra.Filtration.TensorGraded
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Norm.AdaptedBasis
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Norm.BidualHN
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Quotient
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Dual
public import ArakelovGeometry.AdelicVectorBundle.Tensor.PairNorm
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Domination

/-!
# Actual epsilon tensor norms and trivial-place filtrations

The canonical binary injective norm realizes the intrinsic tensor convolution.
Single adapted bases in the two factors suffice.
-/

@[expose] public section

open scoped TensorProduct DirectSum
open Module

namespace ArakelovGeometry.NormFamily

open AdelicStructure

noncomputable section

universe u v
variable {K : Type u} [Field K] {E V : Type v}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (ξ : NormFamily (singleTrivialPlace K) E) (η : NormFamily (singleTrivialPlace K) V)

/-- The actual binary epsilon norm is ultrametric at the trivial place. -/
theorem injectiveTensorPair_isUltrametric : (ξ.injectiveTensorPair η).IsUltrametric := by
  intro ω hω x y
  change (injectiveTensor (tensorPairFactors ξ η)).norm ω
      ((binaryTensorEquiv K (BinaryTensorFactors E V)).symm.toLinearMap.baseChange _ (x + y)) ≤ _
  rw [map_add]
  exact injectiveTensor_isUltrametric (tensorPairFactors ξ η) ω hω _ _

/-- The actual epsilon norm on rational pure tensors is bounded by the product norm. -/
theorem trivialSeminorm_injectiveTensorPair_tmul_le (x : E) (y : V) :
    (ξ.injectiveTensorPair η).trivialSeminorm (x ⊗ₜ[K] y) ≤
      ξ.trivialSeminorm x * η.trivialSeminorm y := by
  classical
  let C := (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
  rw [trivialSeminorm_apply, trivialSeminorm_apply, trivialSeminorm_apply]
  apply (injectiveTensorPair_norm_le_projectiveTensorPair_norm ξ η PUnit.unit _).trans
  have h := projectiveTensorPair_norm_tmul_completed_le ξ η PUnit.unit
    ((1 : C) ⊗ₜ[K] x) ((1 : C) ⊗ₜ[K] y)
  change (ξ.projectiveTensorPair η).norm PUnit.unit
    ((TensorProduct.AlgebraTensorModule.distribBaseChange K C E V).symm
      (((1 : C) ⊗ₜ[K] x) ⊗ₜ[C] ((1 : C) ⊗ₜ[K] y))) ≤ _ at h
  simp only [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul, one_mul] at h
  exact h

/-- The canonical dual tensor functional has at most the product of the actual dual norms. -/
theorem trivialSeminorm_injectiveTensorPair_dual_tmul_le
    (ℓ : Module.Dual K E) (m : Module.Dual K V) :
    (ξ.injectiveTensorPair η).dual.trivialSeminorm
      (TensorProduct.dualDistrib K E V (ℓ ⊗ₜ[K] m)) ≤
        ξ.dual.trivialSeminorm ℓ * η.dual.trivialSeminorm m := by
  classical
  let C := (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
  rw [trivialSeminorm_apply, trivialSeminorm_apply, trivialSeminorm_apply]
  have h := injectiveTensorPair_dual_norm_tmul_le ξ η PUnit.unit
    ((1 : C) ⊗ₜ[K] ℓ) ((1 : C) ⊗ₜ[K] m)
  change (ξ.injectiveTensorPair η).dual.norm PUnit.unit
    ((TensorProduct.dualDistrib K E V).baseChange C
      ((TensorProduct.AlgebraTensorModule.distribBaseChange K C (Dual K E) (Dual K V)).symm
        (((1 : C) ⊗ₜ[K] ℓ) ⊗ₜ[C] ((1 : C) ⊗ₜ[K] m)))) ≤ _ at h
  simp only [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul, one_mul,
    LinearMap.baseChange_tmul] at h
  exact h

variable {ι κ : Type*} (b : Basis ι K E) (c : Basis κ K V)

omit η [FiniteDimensional K E] in
/-- A single ball-adapted basis bounds each nonzero coordinate's basis radius. -/
theorem trivialSeminorm_basis_le_of_adapted (hξ : ξ.IsUltrametric)
    (hb : ∀ t x, x ∈ ξ.trivialFiltration hξ t ↔
      ∀ i, b.repr x i ≠ 0 → b i ∈ ξ.trivialFiltration hξ t)
    (x : E) (i : ι) (hi : b.repr x i ≠ 0) :
    ξ.trivialSeminorm (b i) ≤ ξ.trivialSeminorm x := by
  classical
  have hx : x ≠ 0 := by intro h; simp [h] at hi
  have hp : 0 < ξ.trivialSeminorm x := by
    rw [trivialSeminorm_apply]
    exact ξ.norm_rational_pos PUnit.unit hx
  have hm := (hb (-Real.log (ξ.trivialSeminorm x)) x).mp
    ((ξ.mem_trivialFiltration_iff_le_neg_log hξ _ x hx).mpr le_rfl) i hi
  simpa only [mem_trivialFiltration, neg_neg, Real.exp_log hp] using hm

omit η [FiniteDimensional K E] in
/-- The original logarithmic basis weights describe every factor step exactly. -/
theorem trivialFiltration_eq_span_neg_log_of_adapted (hξ : ξ.IsUltrametric)
    (hb : ∀ t x, x ∈ ξ.trivialFiltration hξ t ↔
      ∀ i, b.repr x i ≠ 0 → b i ∈ ξ.trivialFiltration hξ t) (t : ℝ) :
    ξ.trivialFiltration hξ t = Submodule.span K
      (b '' {i | t ≤ -Real.log (ξ.trivialSeminorm (b i))}) := by
  ext x
  rw [b.mem_span_image, hb]
  constructor
  · intro hx i hi
    exact (ξ.mem_trivialFiltration_iff_le_neg_log hξ t (b i) (b.ne_zero i)).mp
      (hx i (Finsupp.mem_support_iff.mp hi))
  · intro hx i hi
    exact (ξ.mem_trivialFiltration_iff_le_neg_log hξ t (b i) (b.ne_zero i)).mpr
      (hx (Finsupp.mem_support_iff.mpr hi))

/-- Nonzero tensor coordinates give the sharp lower bound for the actual epsilon norm. -/
theorem trivialSeminorm_injectiveTensorPair_coordinate_le
    (hb : ∀ x i, b.repr x i ≠ 0 → ξ.trivialSeminorm (b i) ≤ ξ.trivialSeminorm x)
    (hc : ∀ y j, c.repr y j ≠ 0 → η.trivialSeminorm (c j) ≤ η.trivialSeminorm y)
    (x : E ⊗[K] V) (i : ι) (j : κ) (hij : (b.tensorProduct c).repr x (i, j) ≠ 0) :
    ξ.trivialSeminorm (b i) * η.trivialSeminorm (c j) ≤
      (ξ.injectiveTensorPair η).trivialSeminorm x := by
  classical
  let C := (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
  have hbi : 0 < ξ.trivialSeminorm (b i) := by
    rw [trivialSeminorm_apply]
    exact ξ.norm_rational_pos PUnit.unit (b.ne_zero i)
  have hcj : 0 < η.trivialSeminorm (c j) := by
    rw [trivialSeminorm_apply]
    exact η.norm_rational_pos PUnit.unit (c.ne_zero j)
  have hdb := ξ.trivialSeminorm_dual_le_inv_of_ge_away_kernel (b.coord i) hbi (hb · i)
  have hdc := η.trivialSeminorm_dual_le_inv_of_ge_away_kernel (c.coord j) hcj (hc · j)
  have he : (TensorProduct.dualDistrib K E V) (b.coord i ⊗ₜ[K] c.coord j) =
      (b.tensorProduct c).coord (i, j) := by
    apply TensorProduct.ext'
    intro v w
    simp only [TensorProduct.dualDistrib_apply, Basis.coord_apply,
      Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, mul_comm]
  have hd := ξ.trivialSeminorm_injectiveTensorPair_dual_tmul_le η (b.coord i) (c.coord j)
  rw [he] at hd
  have hdual := hd.trans (mul_le_mul hdb hdc
    (apply_nonneg η.dual.trivialSeminorm _) (inv_nonneg.mpr hbi.le))
  have hev := (ξ.injectiveTensorPair η).norm_dual_tmul_apply_tmul_le PUnit.unit
    (1 : C) (1 : C) ((b.tensorProduct c).coord (i, j)) x
  change ‖(1 : C) * 1 * algebraMap K C ((b.tensorProduct c).coord (i, j) x)‖ ≤ _ at hev
  rw [one_mul, one_mul, norm_trivialCompletion K, trivialCompletionAlgEquiv_algebraMap,
    Basis.coord_apply, AbsoluteValue.trivial_apply hij] at hev
  change 1 ≤ (ξ.injectiveTensorPair η).dual.trivialSeminorm
    ((b.tensorProduct c).coord (i, j)) * (ξ.injectiveTensorPair η).trivialSeminorm x at hev
  have hh := hev.trans (mul_le_mul_of_nonneg_right hdual
    (apply_nonneg (ξ.injectiveTensorPair η).trivialSeminorm x))
  calc
    _ = (ξ.trivialSeminorm (b i) * η.trivialSeminorm (c j)) * 1 := (mul_one _).symm
    _ ≤ (ξ.trivialSeminorm (b i) * η.trivialSeminorm (c j)) *
        ((ξ.trivialSeminorm (b i))⁻¹ * (η.trivialSeminorm (c j))⁻¹ *
          (ξ.injectiveTensorPair η).trivialSeminorm x) :=
      mul_le_mul_of_nonneg_left hh (mul_nonneg hbi.le hcj.le)
    _ = _ := by field_simp

/-- The intrinsic convolution is contained in the actual epsilon ball at each threshold. -/
theorem tensorFiltration_le_trivialFiltration_injectiveTensorPair
    (hξ : ξ.IsUltrametric) (hη : η.IsUltrametric) (γ : ℝ) :
    Submodule.tensorFiltration (ξ.trivialFiltration hξ) (η.trivialFiltration hη) γ ≤
      (ξ.injectiveTensorPair η).trivialFiltration (ξ.injectiveTensorPair_isUltrametric η) γ := by
  apply iSup_le
  intro t
  apply iSup_le
  intro u
  apply iSup_le
  intro h
  rintro _ ⟨x, rfl⟩
  induction x with
  | tmul x y =>
    change (ξ.injectiveTensorPair η).trivialSeminorm (x.val ⊗ₜ[K] y.val) ≤ Real.exp (-γ)
    calc
      _ ≤ ξ.trivialSeminorm x.val * η.trivialSeminorm y.val :=
        ξ.trivialSeminorm_injectiveTensorPair_tmul_le η _ _
      _ ≤ Real.exp (-t) * Real.exp (-u) :=
        mul_le_mul x.property y.property (apply_nonneg η.trivialSeminorm _) (Real.exp_pos _).le
      _ = Real.exp (-(t + u)) := by rw [← Real.exp_add, neg_add]
      _ ≤ _ := Real.exp_le_exp.mpr (neg_le_neg h)
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

/-- Arbitrary given factor filtrations from actual norms have exactly the epsilon tensor balls. -/
theorem trivialFiltration_injectiveTensorPair
    (hξ : ξ.IsUltrametric) (hη : η.IsUltrametric) (γ : ℝ) :
    (ξ.injectiveTensorPair η).trivialFiltration (ξ.injectiveTensorPair_isUltrametric η) γ =
      Submodule.tensorFiltration (ξ.trivialFiltration hξ) (η.trivialFiltration hη) γ := by
  classical
  apply le_antisymm
  · obtain ⟨b, hb⟩ := ξ.exists_basis_adapted_trivialFiltration hξ
    obtain ⟨c, hc⟩ := η.exists_basis_adapted_trivialFiltration hη
    let w := fun i ↦ -Real.log (ξ.trivialSeminorm (b i))
    let z := fun j ↦ -Real.log (η.trivialSeminorm (c j))
    have hF := ξ.trivialFiltration_eq_span_neg_log_of_adapted b hξ hb
    have hG := η.trivialFiltration_eq_span_neg_log_of_adapted c hη hc
    rw [Submodule.tensorFiltration_eq_span_tensorProduct b c w z hF hG]
    intro x hx
    apply (b.tensorProduct c).mem_span_image.mpr
    intro ij hij
    have hcoord := ξ.trivialSeminorm_injectiveTensorPair_coordinate_le η b c
      (ξ.trivialSeminorm_basis_le_of_adapted b hξ hb)
      (η.trivialSeminorm_basis_le_of_adapted c hη hc) x ij.1 ij.2
      (Finsupp.mem_support_iff.mp hij)
    have hbi : 0 < ξ.trivialSeminorm (b ij.1) := by
      rw [trivialSeminorm_apply]
      exact ξ.norm_rational_pos PUnit.unit (b.ne_zero ij.1)
    have hcj : 0 < η.trivialSeminorm (c ij.2) := by
      rw [trivialSeminorm_apply]
      exact η.norm_rational_pos PUnit.unit (c.ne_zero ij.2)
    have hbound := hcoord.trans hx
    change γ ≤ -Real.log (ξ.trivialSeminorm (b ij.1)) +
      -Real.log (η.trivialSeminorm (c ij.2))
    have hlog := Real.log_le_log (mul_pos hbi hcj) hbound
    rw [Real.log_mul hbi.ne' hcj.ne', Real.log_exp] at hlog
    linarith
  · exact ξ.tensorFiltration_le_trivialFiltration_injectiveTensorPair η hξ hη γ

/-- The tensor basis retains the sums of the two original logarithmic weights. -/
theorem trivialFiltration_injectiveTensorPair_eq_span
    (hξ : ξ.IsUltrametric) (hη : η.IsUltrametric)
    (hb : ∀ t x, x ∈ ξ.trivialFiltration hξ t ↔
      ∀ i, b.repr x i ≠ 0 → b i ∈ ξ.trivialFiltration hξ t)
    (hc : ∀ t y, y ∈ η.trivialFiltration hη t ↔
      ∀ j, c.repr y j ≠ 0 → c j ∈ η.trivialFiltration hη t) (γ : ℝ) :
    (ξ.injectiveTensorPair η).trivialFiltration (ξ.injectiveTensorPair_isUltrametric η) γ =
      Submodule.span K ((b.tensorProduct c) '' {ij |
        γ ≤ -Real.log (ξ.trivialSeminorm (b ij.1)) +
          -Real.log (η.trivialSeminorm (c ij.2))}) := by
  rw [ξ.trivialFiltration_injectiveTensorPair η hξ hη]
  exact Submodule.tensorFiltration_eq_span_tensorProduct b c _ _
    (ξ.trivialFiltration_eq_span_neg_log_of_adapted b hξ hb)
    (η.trivialFiltration_eq_span_neg_log_of_adapted c hη hc) γ

/-- The actual epsilon norm is the coordinate maximum of the products of the original radii. -/
theorem trivialSeminorm_injectiveTensorPair_eq_sup
    (hξ : ξ.IsUltrametric) (hη : η.IsUltrametric)
    (hb : ∀ t x, x ∈ ξ.trivialFiltration hξ t ↔
      ∀ i, b.repr x i ≠ 0 → b i ∈ ξ.trivialFiltration hξ t)
    (hc : ∀ t y, y ∈ η.trivialFiltration hη t ↔
      ∀ j, c.repr y j ≠ 0 → c j ∈ η.trivialFiltration hη t) (x : E ⊗[K] V) :
    (ξ.injectiveTensorPair η).trivialSeminorm x =
      ((((b.tensorProduct c).repr x).support.sup fun ij ↦
        ⟨ξ.trivialSeminorm (b ij.1) * η.trivialSeminorm (c ij.2),
          mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)⟩ : NNReal) : ℝ) := by
  classical
  let s := ((b.tensorProduct c).repr x).support
  let f : ι × κ → NNReal := fun ij ↦
    ⟨ξ.trivialSeminorm (b ij.1) * η.trivialSeminorm (c ij.2),
      mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)⟩
  let M := s.sup f
  have hl : M ≤ (⟨(ξ.injectiveTensorPair η).trivialSeminorm x,
      apply_nonneg _ _⟩ : NNReal) := by
    apply Finset.sup_le
    intro ij hij
    exact ξ.trivialSeminorm_injectiveTensorPair_coordinate_le η b c
      (ξ.trivialSeminorm_basis_le_of_adapted b hξ hb)
      (η.trivialSeminorm_basis_le_of_adapted c hη hc) x ij.1 ij.2
      (Finsupp.mem_support_iff.mp hij)
  apply le_antisymm _ (show (M : ℝ) ≤ (ξ.injectiveTensorPair η).trivialSeminorm x from hl)
  by_cases hx : x = 0
  · subst x
    rw [map_zero]
    exact M.property
  have hs : s.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun h ↦ hx ((b.tensorProduct c).repr.map_eq_zero_iff.mp h))
  obtain ⟨ij, hij⟩ := hs
  have hbi : 0 < ξ.trivialSeminorm (b ij.1) := by
    rw [trivialSeminorm_apply]
    exact ξ.norm_rational_pos PUnit.unit (b.ne_zero ij.1)
  have hcj : 0 < η.trivialSeminorm (c ij.2) := by
    rw [trivialSeminorm_apply]
    exact η.norm_rational_pos PUnit.unit (c.ne_zero ij.2)
  have hM : 0 < (M : ℝ) := (mul_pos hbi hcj).trans_le
    (show (f ij : ℝ) ≤ (M : ℝ) from Finset.le_sup (f := f) hij)
  have hxball : x ∈ (ξ.injectiveTensorPair η).trivialFiltration
      (ξ.injectiveTensorPair_isUltrametric η) (-Real.log M) := by
    apply (Submodule.span_le.mpr ?_) ((b.tensorProduct c).mem_span_repr_support x)
    rintro _ ⟨ij, hij, rfl⟩
    change (ξ.injectiveTensorPair η).trivialSeminorm ((b.tensorProduct c) ij) ≤
      Real.exp (-(-Real.log M))
    rw [Basis.tensorProduct_apply', neg_neg, Real.exp_log hM]
    exact (ξ.trivialSeminorm_injectiveTensorPair_tmul_le η _ _).trans
      (show (f ij : ℝ) ≤ (M : ℝ) from Finset.le_sup (f := f) hij)
  simpa only [mem_trivialFiltration, neg_neg, Real.exp_log hM] using hxball

/-- The actual quotient of the epsilon norm has the image of the original tensor filtration. -/
theorem trivialFiltration_pushforward_injectiveTensorPair
    {Q : Type*} [AddCommGroup Q] [Module K Q]
    (hξ : ξ.IsUltrametric) (hη : η.IsUltrametric)
    (q : E ⊗[K] V →ₗ[K] Q) (hq : Function.Surjective q) (γ : ℝ) :
    ((ξ.injectiveTensorPair η).pushforward q hq).trivialFiltration
      ((ξ.injectiveTensorPair_isUltrametric η).pushforward q hq) γ =
      (Submodule.tensorFiltration (ξ.trivialFiltration hξ) (η.trivialFiltration hη) γ).map q := by
  rw [trivialFiltration_pushforward _ (ξ.injectiveTensorPair_isUltrametric η),
    trivialFiltration_injectiveTensorPair ξ η hξ hη]

/-- The canonical map from all pair grades to the grade of the actual quotient epsilon norm. -/
noncomputable def trivialTensorQuotientGradedMap
    {Q : Type*} [AddCommGroup Q] [Module K Q]
    (hξ : ξ.IsUltrametric) (hη : η.IsUltrametric)
    (q : E ⊗[K] V →ₗ[K] Q) (hq : Function.Surjective q) (γ : ℝ) :
    (⨁ p : {p : ℝ × ℝ // p.1 + p.2 = γ},
      Submodule.FiltrationGraded (ξ.trivialFiltration hξ) p.val.1 ⊗[K]
        Submodule.FiltrationGraded (η.trivialFiltration hη) p.val.2) →ₗ[K]
      Submodule.FiltrationGraded
        (((ξ.injectiveTensorPair η).pushforward q hq).trivialFiltration
          ((ξ.injectiveTensorPair_isUltrametric η).pushforward q hq)) γ :=
  (Submodule.filtrationGradedMap q (fun t ↦ by
    rw [ξ.trivialFiltration_pushforward_injectiveTensorPair η hξ hη q hq t]
    exact Submodule.le_comap_map _ _) γ).comp
      (Submodule.tensorFiltrationGradedSum (ξ.antitone_trivialFiltration hξ)
        (η.antitone_trivialFiltration hη) γ)

/-- The canonical map to an actual quotient-norm grade is surjective without removing collisions. -/
theorem trivialTensorQuotientGradedMap_surjective
    {Q : Type*} [AddCommGroup Q] [Module K Q]
    (hξ : ξ.IsUltrametric) (hη : η.IsUltrametric)
    (q : E ⊗[K] V →ₗ[K] Q) (hq : Function.Surjective q) (γ : ℝ) :
    Function.Surjective (ξ.trivialTensorQuotientGradedMap η hξ hη q hq γ) := by
  obtain ⟨b, hb⟩ := ξ.exists_basis_adapted_trivialFiltration hξ
  obtain ⟨c, hc⟩ := η.exists_basis_adapted_trivialFiltration hη
  apply Function.Surjective.comp
    (Submodule.filtrationGradedMap_surjective q _ γ
      (ξ.trivialFiltration_pushforward_injectiveTensorPair η hξ hη q hq γ).symm)
  exact Submodule.tensorFiltrationGradedSum_surjective b c _ _
    (ξ.antitone_trivialFiltration hξ) (η.antitone_trivialFiltration hη)
    (ξ.trivialFiltration_eq_span_neg_log_of_adapted b hξ hb)
    (η.trivialFiltration_eq_span_neg_log_of_adapted c hη hc) γ

end

section FiniteFamily

variable {K : Type*} [Field K] {J : Type*} [Fintype J] {M : J → Type*}
  [∀ j, AddCommGroup (M j)] [∀ j, Module K (M j)]
  [∀ j, FiniteDimensional K (M j)]
  (ν : ∀ j, NormFamily (singleTrivialPlace K) (M j))

/-- The existing finite epsilon norm has the pure-tensor product bound at the trivial place. -/
theorem trivialSeminorm_injectiveTensor_tprod_le (x : ∀ j, M j) :
    (injectiveTensor ν).trivialSeminorm (⨂ₜ[K] j, x j) ≤ ∏ j, (ν j).trivialSeminorm (x j) := by
  classical
  simp only [trivialSeminorm_apply]
  exact (injectiveTensor_norm_le_projectiveTensor_norm ν PUnit.unit _).trans
    (projectiveTensor_norm_rational_tprod_le ν x PUnit.unit)

variable {κ : J → Type*} [∀ j, Finite (κ j)] (b : ∀ j, Basis (κ j) K (M j))

/-- Each nonzero tuple coordinate bounds the actual finite epsilon norm from below. -/
theorem trivialSeminorm_injectiveTensor_coordinate_le
    (hb : ∀ j x i, (b j).repr x i ≠ 0 →
      (ν j).trivialSeminorm (b j i) ≤ (ν j).trivialSeminorm x)
    (x : ⨂[K] j, M j) (p : ∀ j, κ j) (hp : (Basis.piTensorProduct b).repr x p ≠ 0) :
    (∏ j, (ν j).trivialSeminorm (b j (p j))) ≤ (injectiveTensor ν).trivialSeminorm x := by
  classical
  let C := (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
  let r := fun j ↦ (ν j).trivialSeminorm (b j (p j))
  have hr (j : J) : 0 < r j := by
    rw [show r j = (ν j).trivialSeminorm (b j (p j)) from rfl, trivialSeminorm_apply]
    exact (ν j).norm_rational_pos PUnit.unit ((b j).ne_zero _)
  let : ∀ j, Fintype (κ j) := fun j ↦ Fintype.ofFinite (κ j)
  have hd (j : J) : (ν j).dual.trivialSeminorm ((b j).dualBasis (p j)) ≤ (r j)⁻¹ := by
    simpa only [Basis.coe_dualBasis] using
      (ν j).trivialSeminorm_dual_le_inv_of_ge_away_kernel ((b j).coord (p j)) (hr j) (hb j · _)
  have he := norm_tensor_coordinate_le_injective b ν PUnit.unit p ((1 : C) ⊗ₜ[K] x)
  change ‖((Basis.piTensorProduct b).baseChange C).equivFun ((1 : C) ⊗ₜ[K] x) p‖ ≤ _ at he
  rw [Basis.equivFun_apply, Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one,
    norm_trivialCompletion K, trivialCompletionAlgEquiv_algebraMap,
    AbsoluteValue.trivial_apply hp] at he
  change 1 ≤ (∏ j, (ν j).dual.trivialSeminorm ((b j).dualBasis (p j))) *
    (injectiveTensor ν).trivialSeminorm x at he
  have hdprod : (∏ j, (ν j).dual.trivialSeminorm ((b j).dualBasis (p j))) ≤
      ∏ j, (r j)⁻¹ :=
    Finset.prod_le_prod₀ (fun j _ ↦ apply_nonneg _ _) (fun j _ ↦ hd j)
  have hbound := he.trans (mul_le_mul_of_nonneg_right hdprod
    (apply_nonneg (injectiveTensor ν).trivialSeminorm x))
  rw [Finset.prod_inv_distrib] at hbound
  have hprod : 0 < ∏ j, r j := Finset.prod_pos (fun j _ ↦ hr j)
  have hm := mul_le_mul_of_nonneg_left hbound hprod.le
  simpa only [mul_one, ← mul_assoc, mul_inv_cancel₀ hprod.ne', one_mul] using hm

/-- Finite-family epsilon balls are tensor-basis spans with the original sums of weights. -/
theorem trivialFiltration_injectiveTensor_eq_span
    (hν : ∀ j, (ν j).IsUltrametric)
    (hb : ∀ j t x, x ∈ (ν j).trivialFiltration (hν j) t ↔
      ∀ i, (b j).repr x i ≠ 0 → b j i ∈ (ν j).trivialFiltration (hν j) t) (γ : ℝ) :
    (injectiveTensor ν).trivialFiltration (injectiveTensor_isUltrametric ν) γ =
      Submodule.span K (Basis.piTensorProduct b ''
        {p | γ ≤ ∑ j, -Real.log ((ν j).trivialSeminorm (b j (p j)))}) := by
  classical
  have hrad (p : ∀ j, κ j) :
      Real.exp (-(∑ j, -Real.log ((ν j).trivialSeminorm (b j (p j))))) =
        ∏ j, (ν j).trivialSeminorm (b j (p j)) := by
    rw [Finset.sum_neg_distrib, neg_neg, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro j _
    apply Real.exp_log
    rw [trivialSeminorm_apply]
    exact (ν j).norm_rational_pos PUnit.unit ((b j).ne_zero _)
  apply le_antisymm
  · intro x hx
    apply (Basis.piTensorProduct b).mem_span_image.mpr
    intro p hp
    have hl := trivialSeminorm_injectiveTensor_coordinate_le ν b
      (fun j ↦ (ν j).trivialSeminorm_basis_le_of_adapted (b j) (hν j) (hb j))
      x p (Finsupp.mem_support_iff.mp hp)
    rw [← hrad] at hl
    exact neg_le_neg_iff.mp (Real.exp_le_exp.mp (hl.trans hx))
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    change (injectiveTensor ν).trivialSeminorm (Basis.piTensorProduct b p) ≤ Real.exp (-γ)
    rw [Basis.piTensorProduct_apply]
    apply (trivialSeminorm_injectiveTensor_tprod_le ν _).trans
    rw [← hrad]
    exact Real.exp_le_exp.mpr (neg_le_neg hp)

/-- The existing finite-family epsilon norm realizes the intrinsic convolution on all tuples. -/
theorem trivialFiltration_injectiveTensor
    (hν : ∀ j, (ν j).IsUltrametric) (γ : ℝ) :
    (injectiveTensor ν).trivialFiltration (injectiveTensor_isUltrametric ν) γ =
      Submodule.piTensorFiltration (fun j ↦ (ν j).trivialFiltration (hν j)) γ := by
  classical
  choose b hb using fun j ↦ (ν j).exists_basis_adapted_trivialFiltration (hν j)
  rw [trivialFiltration_injectiveTensor_eq_span ν b hν hb]
  exact (Submodule.piTensorFiltration_eq_span b _
    (fun j ↦ (ν j).trivialFiltration_eq_span_neg_log_of_adapted (b j) (hν j) (hb j)) γ).symm

omit [∀ j, Finite (κ j)] in
/-- Any prescribed adapted factor weights give the same original sums in the actual epsilon ball. -/
theorem trivialFiltration_injectiveTensor_eq_span_of_weights
    (hν : ∀ j, (ν j).IsUltrametric) (w : ∀ j, κ j → ℝ)
    (hF : ∀ j t, (ν j).trivialFiltration (hν j) t =
      Submodule.span K (b j '' {i | t ≤ w j i})) (γ : ℝ) :
    (injectiveTensor ν).trivialFiltration (injectiveTensor_isUltrametric ν) γ =
      Submodule.span K (Basis.piTensorProduct b '' {p | γ ≤ ∑ j, w j (p j)}) := by
  rw [trivialFiltration_injectiveTensor ν hν]
  exact Submodule.piTensorFiltration_eq_span b w hF γ

omit [∀ j, Finite (κ j)] in
/-- Actual quotient epsilon balls retain tuple weights and allow their images to vanish. -/
theorem trivialFiltration_pushforward_injectiveTensor_eq_span_of_weights
    {Q : Type*} [AddCommGroup Q] [Module K Q]
    (hν : ∀ j, (ν j).IsUltrametric) (w : ∀ j, κ j → ℝ)
    (hF : ∀ j t, (ν j).trivialFiltration (hν j) t =
      Submodule.span K (b j '' {i | t ≤ w j i}))
    (q : (⨂[K] j, M j) →ₗ[K] Q) (hq : Function.Surjective q) (γ : ℝ) :
    ((injectiveTensor ν).pushforward q hq).trivialFiltration
      ((injectiveTensor_isUltrametric ν).pushforward q hq) γ =
      Submodule.span K ((fun p ↦ q (Basis.piTensorProduct b p)) ''
        {p | γ ≤ ∑ j, w j (p j)}) := by
  rw [trivialFiltration_pushforward _ (injectiveTensor_isUltrametric ν),
    trivialFiltration_injectiveTensor_eq_span_of_weights ν b hν w hF,
    Submodule.map_span, Set.image_image]

end FiniteFamily

end ArakelovGeometry.NormFamily
