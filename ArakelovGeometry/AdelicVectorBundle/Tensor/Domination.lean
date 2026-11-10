/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Strong
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicVectorBundle.NormFamily.BasisComparison
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Domination of actual finite tensor norms

Completed tensor-basis coordinates are bounded by products of actual dual
norms. Together with the projective pure-tensor bound, this gives the
source's comparison with a mixed rational basis norm.
-/

@[expose] public section

open MeasureTheory Filter
open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w wι wκ

noncomputable section

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {ι : Type wι} [Fintype ι] {E : ι → Type w}
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)]
  {κ : ι → Type wκ} [∀ i, Fintype (κ i)]
  (b : ∀ i, Module.Basis (κ i) K (E i))
  (ξ : ∀ i, NormFamily S (E i))

omit [Fintype ι] [∀ i, Fintype (κ i)] [∀ i, FiniteDimensional K (E i)] in
/-- The completed tensor identification respects the actual tensor-basis coordinates. -/
theorem tensorBaseChange_equivFun [Finite ι] [∀ i, Finite (κ i)]
    (ω : S.Ω) (j : ∀ i, κ i)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (Basis.piTensorProduct (fun i ↦ (b i).baseChange (S.ϕ ω).Completion)).equivFun
        (tensorBaseChangeEquiv K (S.ϕ ω).Completion E z) j =
      ((Basis.piTensorProduct b).baseChange (S.ϕ ω).Completion).equivFun z j := by
  classical
  let B := (Basis.piTensorProduct b).baseChange (S.ϕ ω).Completion
  let C := Basis.piTensorProduct (fun i ↦ (b i).baseChange (S.ϕ ω).Completion)
  have he : (C.coord j).comp (tensorBaseChangeEquiv K (S.ϕ ω).Completion E).toLinearMap =
      B.coord j := by
    apply B.ext
    intro k
    have hk : tensorBaseChangeEquiv K (S.ϕ ω).Completion E (B k) = C k := by
      simp [B, C, Module.Basis.baseChange_apply, Basis.piTensorProduct_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hk]
    simp
  exact LinearMap.congr_fun he z

variable [∀ i, DecidableEq (κ i)]

omit [∀ i, Fintype (κ i)] in
/-- Products of dual basis norms bound every completed tensor coordinate. -/
theorem norm_tensor_coordinate_le_injective [∀ i, Finite (κ i)] (ω : S.Ω) (j : ∀ i, κ i)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    ‖((Basis.piTensorProduct b).baseChange (S.ϕ ω).Completion).equivFun z j‖ ≤
      (∏ i, (ξ i).dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (b i).dualBasis (j i))) *
        (injectiveTensor ξ).norm ω z := by
  classical
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedSpace ω
  let φ := fun i ↦ dualBaseChangeEquiv K (S.ϕ ω).Completion (E i)
    ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (b i).dualBasis (j i))
  have he (i : ι) : φ i = ((b i).baseChange (S.ϕ ω).Completion).coord (j i) := by
    apply LinearMap.ext
    intro x
    exact dualBaseChange_one_dualBasis_apply (b i) ω (j i) x
  have hval : tensorDualEval φ (tensorBaseChangeEquiv K (S.ϕ ω).Completion E z) =
      ((Basis.piTensorProduct b).baseChange (S.ϕ ω).Completion).equivFun z j := by
    have hφ : φ = fun i ↦ ((b i).baseChange (S.ϕ ω).Completion).coord (j i) := funext he
    rw [hφ, tensorDualEval_coord]
    exact tensorBaseChange_equivFun b ω j z
  have hp : 0 < ∏ i, linearMapOperatorSeminorm (φ i) := by
    apply Finset.prod_pos
    intro i _
    exact (ξ i).dual.norm_rational_pos ω ((b i).dualBasis.ne_zero (j i))
  have h := tensorDualRatioSeminorm_le_injective φ
    (tensorBaseChangeEquiv K (S.ϕ ω).Completion E z)
  rw [tensorDualRatioSeminorm_apply, hval, div_le_iff₀ hp] at h
  change _ ≤ (∏ i, linearMapOperatorSeminorm (φ i)) *
    ArakelovGeometry.injectiveTensorSeminorm (tensorBaseChangeEquiv K (S.ϕ ω).Completion E z)
  rwa [mul_comm] at h

/-- Rational pure tensors satisfy the projective product bound. -/
theorem projectiveTensor_norm_rational_tprod_le (x : ∀ i, E i) (ω : S.Ω) :
    (projectiveTensor ξ).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (⨂ₜ[K] i, x i)) ≤
      ∏ i, (ξ i).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x i) := by
  simpa only [tensorBaseChangeEquiv_symm_tprod_tmul, Finset.prod_const_one] using
    projectiveTensor_norm_tprod_le ξ ω (fun i ↦ (1 : (S.ϕ ω).Completion) ⊗ₜ[K] x i)

/-- A common bound on each factor's actual dual basis controls the tensor's
coordinate maximum. Zero-dimensional and empty families are included. -/
theorem ofBasis_tensor_norm_le_mul_of_dual_bounds [DecidableEq ι] (ω : S.Ω)
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hb : ∀ i j, (ξ i).dual.norm ω
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (b i).dualBasis j) ≤ C i)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (ofBasis S (⨂[K] i, E i) (Basis.piTensorProduct b)).norm ω z ≤
      (∏ i, C i) * (injectiveTensor ξ).norm ω z := by
  classical
  rw [ofBasis_norm]
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (Finset.prod_nonneg (fun i _ ↦ hC i)) ((injectiveTensor ξ).norm_nonneg ω z))).mpr
  intro j
  exact (norm_tensor_coordinate_le_injective b ξ ω j z).trans
    (mul_le_mul_of_nonneg_right
      (Finset.prod_le_prod₀ (fun i _ ↦ (ξ i).dual.norm_nonneg ω _) (fun i _ ↦ hb i (j i)))
      ((injectiveTensor ξ).norm_nonneg ω z))

/-- Norms between the actual injective and projective constructions, ultrametric
at finite places, are strongly dominated when every factor is dominated.
This is the common coordinate argument for source Proposition 4.1.19(5). -/
theorem isStronglyDominated_tensor_of_bounds
    (τ : NormFamily S (⨂[K] i, E i)) (hu : τ.IsUltrametric)
    (hlo : ∀ ω z, (injectiveTensor ξ).norm ω z ≤ τ.norm ω z)
    (hhi : ∀ ω z, τ.norm ω z ≤ (projectiveTensor ξ).norm ω z)
    (hd : ∀ i, (ξ i).IsDominated) (hfin : S.v S.Ωinf < ⊤) :
    τ.IsStronglyDominated := by
  classical
  let b := fun i ↦ Module.finBasis K (E i)
  let B := Basis.piTensorProduct b
  choose A hA hA0 hAb using fun i ↦
    IsUpperDominated.exists_basis_norm_bound (ξ := ξ i) (b i) (hd i).1
  choose D hD hD0 hDb using fun i ↦
    IsUpperDominated.exists_basis_norm_bound (ξ := (ξ i).dual) (b i).dualBasis (hd i).2
  let a := fun ω ↦ ∑ i, A i ω
  let d := fun ω ↦ ∑ i, D i ω
  have haI : Integrable a S.v := integrable_finsetSum _ (fun i _ ↦ hA i)
  have hdI : Integrable d S.v := integrable_finsetSum _ (fun i _ ↦ hD i)
  have ha0 : ∀ ω, 0 ≤ a ω := fun ω ↦ Finset.sum_nonneg (fun i _ ↦ hA0 i ω)
  have hd0 : ∀ ω, 0 ≤ d ω := fun ω ↦ Finset.sum_nonneg (fun i _ ↦ hD0 i ω)
  let R := S.Ωinf.indicator (fun _ ↦ Real.log
    (Fintype.card (∀ i, Fin (Module.finrank K (E i))) : ℝ))
  have hRI : Integrable R S.v :=
    (integrable_indicator_iff S.measurableSet_Ωinf).mpr (integrableOn_const hfin.ne)
  have hR0 : ∀ ω, 0 ≤ R ω := Set.indicator_nonneg (fun _ _ ↦ Real.log_natCast_nonneg _)
  apply (isStronglyDominated_iff_localDist_ofBasisMixed_of_measure_lt_top B τ hfin).mpr
  refine ⟨⟨fun ω ↦ a ω + d ω + R ω, (haI.add hdI).add hRI, ?_⟩,
    ⟨0, integrable_zero _ _ _, Eventually.of_forall (τ.localDist_nonneg _)⟩⟩
  filter_upwards [ae_all_iff.mpr hAb, ae_all_iff.mpr hDb] with ω ha hb
  have hprimal : ∀ j, τ.norm ω ((B.baseChange (S.ϕ ω).Completion) j) ≤ Real.exp (a ω) := by
    intro j
    rw [Module.Basis.baseChange_apply]
    calc
      τ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] B j) ≤
          (projectiveTensor ξ).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] B j) := hhi ω _
      _ ≤ ∏ i, (ξ i).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (b i) (j i)) := by
        simpa only [B, Basis.piTensorProduct_apply] using
          projectiveTensor_norm_rational_tprod_le ξ (fun i ↦ (b i) (j i)) ω
      _ ≤ ∏ i, Real.exp (A i ω) := Finset.prod_le_prod₀
        (fun i _ ↦ (ξ i).norm_nonneg ω _) (fun i _ ↦ by
          simpa only [Module.Basis.baseChange_apply] using ha i (j i))
      _ = Real.exp (a ω) := (Real.exp_sum _ _).symm
  have hcoordinate (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
      (ofBasis S (⨂[K] i, E i) B).norm ω z ≤ Real.exp (d ω) * τ.norm ω z := by
    have hb' : ∀ i j, (ξ i).dual.norm ω
        ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (b i).dualBasis j) ≤ Real.exp (D i ω) := by
      simpa only [Module.Basis.baseChange_apply] using hb
    have ht := ofBasis_tensor_norm_le_mul_of_dual_bounds b ξ ω
      (fun i ↦ Real.exp (D i ω)) (fun i ↦ (Real.exp_pos _).le) hb' z
    rw [← Real.exp_sum] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left (hlo ω z) (Real.exp_pos _).le)
  apply (τ.localDist_le_iff_norm_le (ofBasisMixed S (⨂[K] i, E i) B) ω
    (add_nonneg (add_nonneg (ha0 ω) (hd0 ω)) (hR0 ω))).mpr
  intro z
  constructor
  · exact (norm_le_mul_of_basis_norm_le B τ hu ω (Real.exp_pos _).le hprimal z).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hd0 ω, hR0 ω]))
        ((ofBasisMixed S (⨂[K] i, E i) B).norm_nonneg ω z))
  · have hm : (ofBasisMixed S (⨂[K] i, E i) B).norm ω z ≤
        Real.exp (R ω) * (ofBasis S (⨂[K] i, E i) B).norm ω z := by
      dsimp only [R]
      by_cases hω : ω ∈ S.Ωinf
      · rw [Set.indicator_of_mem hω]
        exact ofBasisMixed_norm_le_exp_log_card_mul B ω z
      · rw [Set.indicator_of_notMem hω, Real.exp_zero, one_mul,
          ofBasisMixed_norm_of_finite B ω (not_not.mp hω)]
    calc
      (ofBasisMixed S (⨂[K] i, E i) B).norm ω z ≤
          Real.exp (R ω) * (Real.exp (d ω) * τ.norm ω z) :=
        hm.trans (mul_le_mul_of_nonneg_left (hcoordinate z) (Real.exp_pos _).le)
      _ = Real.exp (d ω + R ω) * τ.norm ω z := by rw [← mul_assoc, ← Real.exp_add, add_comm]
      _ ≤ Real.exp (a ω + d ω + R ω) * τ.norm ω z :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [ha0 ω])) (τ.norm_nonneg ω z)

/-- The injective tensor norm is a lower bound for the mixed norm at every place. -/
theorem injectiveTensor_norm_le_mixedTensor_norm (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (injectiveTensor ξ).norm ω z ≤ (mixedTensor ξ).norm ω z := by
  by_cases hω : ω ∈ S.Ωfin
  · rw [mixedTensor_norm_of_mem_Ωfin ξ ω hω]
  · rw [mixedTensor_norm_of_not_mem_Ωfin ξ ω hω]
    exact injectiveTensor_norm_le_projectiveTensor_norm ξ ω z

/-- The projective tensor norm is an upper bound for the mixed norm at every place. -/
theorem mixedTensor_norm_le_projectiveTensor_norm (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (mixedTensor ξ).norm ω z ≤ (projectiveTensor ξ).norm ω z := by
  by_cases hω : ω ∈ S.Ωfin
  · rw [mixedTensor_norm_of_mem_Ωfin ξ ω hω]
    exact injectiveTensor_norm_le_projectiveTensor_norm ξ ω z
  · rw [mixedTensor_norm_of_not_mem_Ωfin ξ ω hω]

/-- The actual injective tensor family of finitely many dominated factors is
strongly dominated, including an empty family or a zero-dimensional factor. -/
theorem IsDominated.strong_injectiveTensor (hd : ∀ i, (ξ i).IsDominated)
    (hfin : S.v S.Ωinf < ⊤) : (injectiveTensor ξ).IsStronglyDominated :=
  isStronglyDominated_tensor_of_bounds ξ (injectiveTensor ξ) (injectiveTensor_isUltrametric ξ)
    (fun _ _ ↦ le_rfl) (injectiveTensor_norm_le_projectiveTensor_norm ξ) hd hfin

/-- The actual mixed tensor family of finitely many dominated factors is
strongly dominated; no measurability or strong domination of factors is assumed. -/
theorem IsDominated.strong_mixedTensor (hd : ∀ i, (ξ i).IsDominated)
    (hfin : S.v S.Ωinf < ⊤) : (mixedTensor ξ).IsStronglyDominated :=
  isStronglyDominated_tensor_of_bounds ξ (mixedTensor ξ) (mixedTensor_isUltrametric ξ)
    (injectiveTensor_norm_le_mixedTensor_norm ξ)
    (mixedTensor_norm_le_projectiveTensor_norm ξ) hd hfin

end
end ArakelovGeometry.NormFamily
