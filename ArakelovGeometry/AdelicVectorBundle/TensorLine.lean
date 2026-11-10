/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.Tensor
import ArakelovGeometry.AdelicVectorBundle.Line
import Mathlib.LinearAlgebra.PiTensorProduct.Finite

/-!
# Tensor norms on lines

The actual projective, injective and mixed tensor norms coincide on finite
tensor products of lines. Their value on a rational generator is the product
of the given generator norms. The empty tensor family is included.
-/

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w wι

noncomputable section

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}

/-- Norm families on a line agree if they agree on one rational generator. -/
theorem eq_of_finrank_one_norm_rational_eq
    {V : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ξ η : NormFamily S V) (hr : Module.finrank K V = 1) {x : V} (hx : x ≠ 0)
    (he : ∀ ω, ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) =
      η.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x)) : ξ = η := by
  ext ω y
  have hd : Module.finrank (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] V) = 1 :=
    Module.finrank_baseChange.trans hr
  have hx' : (1 : (S.ϕ ω).Completion) ⊗ₜ[K] x ≠ 0 := by
    intro hz
    have hp := ξ.norm_rational_pos ω hx
    rw [hz, ξ.norm_zero] at hp
    exact (lt_irrefl 0) hp
  obtain ⟨a, rfl⟩ := exists_smul_eq_of_finrank_one hd hx' y
  simp only [norm_smul, he ω]

variable {ι : Type wι} [Fintype ι]
  {E : ι → Type w} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)]

omit [Fintype ι] [∀ i, FiniteDimensional K (E i)] in
/-- A finite tensor product of rational lines has dimension one. -/
theorem tensor_finrank_one [Finite ι] (hr : ∀ i, Module.finrank K (E i) = 1) :
    Module.finrank K (⨂[K] i, E i) = 1 := by
  classical
  let := Fintype.ofFinite ι
  let : ∀ i, Nontrivial (E i) := fun i ↦
    Module.nontrivial_of_finrank_pos (by rw [hr i]; exact zero_lt_one)
  choose x hx using fun i ↦ exists_ne (0 : E i)
  let b := fun i ↦ FiniteDimensional.basisSingleton (Fin 1) (hr i) (x i) (hx i)
  rw [Module.finrank_eq_card_basis (Basis.piTensorProduct b)]
  simp

omit [Fintype ι] [∀ i, FiniteDimensional K (E i)] in
/-- Nonzero rational generators have a nonzero tensor product, also for the empty family. -/
theorem tensor_generators_ne_zero [Finite ι] (hr : ∀ i, Module.finrank K (E i) = 1)
    (x : ∀ i, E i) (hx : ∀ i, x i ≠ 0) : (⨂ₜ[K] i, x i) ≠ 0 := by
  classical
  let := Fintype.ofFinite ι
  let b := fun i ↦ FiniteDimensional.basisSingleton (Fin 1) (hr i) (x i) (hx i)
  simpa only [Basis.piTensorProduct_apply, b, FiniteDimensional.basisSingleton_apply] using
    (Basis.piTensorProduct b).ne_zero (fun _ ↦ 0)

/-- Exact generator formula for all three actual tensor norms on rational lines. -/
theorem tensor_norm_rational_generators (ξ : ∀ i, NormFamily S (E i))
    (hr : ∀ i, Module.finrank K (E i) = 1) (x : ∀ i, E i) (hx : ∀ i, x i ≠ 0)
    (ω : S.Ω) :
    (injectiveTensor ξ).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (⨂ₜ[K] i, x i)) =
        ∏ i, (ξ i).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x i) ∧
    (projectiveTensor ξ).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (⨂ₜ[K] i, x i)) =
        ∏ i, (ξ i).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x i) ∧
    (mixedTensor ξ).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (⨂ₜ[K] i, x i)) =
        ∏ i, (ξ i).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x i) := by
  classical
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedSpace ω
  choose ℓ hℓ using fun i ↦ Module.Projective.exists_dual_eq_one K (hx i)
  let φ := fun i ↦ dualBaseChangeEquiv K (S.ϕ ω).Completion (E i)
    ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ i)
  have hφ (i : ι) : linearMapOperatorSeminorm (φ i) =
      ((ξ i).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x i))⁻¹ := by
    change (ξ i).dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ i) = _
    rw [(ξ i).dual_norm_rational_eq_div (hr i) (hx i), hℓ i, map_one, one_div]
  have hval : tensorDualEval φ (⨂ₜ[(S.ϕ ω).Completion] i,
      (1 : (S.ϕ ω).Completion) ⊗ₜ[K] x i) = 1 := by
    simp only [tensorDualEval_tprod, φ, dualBaseChangeEquiv_tmul_apply_tmul,
      hℓ, map_one, one_mul, Finset.prod_const_one]
  have hlo : (∏ i, (ξ i).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x i)) ≤
      (injectiveTensor ξ).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (⨂ₜ[K] i, x i)) := by
    change _ ≤ ArakelovGeometry.injectiveTensorSeminorm
      (tensorBaseChangeEquiv K (S.ϕ ω).Completion E _)
    rw [tensorBaseChangeEquiv_tmul_tprod, one_smul]
    have h := tensorDualRatioSeminorm_le_injective φ
      (⨂ₜ[(S.ϕ ω).Completion] i, (1 : (S.ϕ ω).Completion) ⊗ₜ[K] x i)
    simpa only [tensorDualRatioSeminorm_apply, hval, norm_one, hφ,
      Finset.prod_inv_distrib, one_div, inv_inv] using h
  have hhi : (projectiveTensor ξ).norm ω
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (⨂ₜ[K] i, x i)) ≤
      ∏ i, (ξ i).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x i) := by
    simpa only [tensorBaseChangeEquiv_symm_tprod_tmul, Finset.prod_const_one] using
      projectiveTensor_norm_tprod_le ξ ω (fun i ↦ (1 : (S.ϕ ω).Completion) ⊗ₜ[K] x i)
  have hmid := injectiveTensor_norm_le_projectiveTensor_norm ξ ω
    ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (⨂ₜ[K] i, x i))
  have hi := le_antisymm (hmid.trans hhi) hlo
  have hp := le_antisymm hhi (hlo.trans hmid)
  refine ⟨hi, hp, ?_⟩
  by_cases hω : ω ∈ S.Ωfin
  · simpa only [mixedTensor_norm_of_mem_Ωfin ξ ω hω] using hi
  · simpa only [mixedTensor_norm_of_not_mem_Ωfin ξ ω hω] using hp

/-- Projective and injective tensor norms coincide on a finite family of lines. -/
theorem projectiveTensor_eq_injectiveTensor_of_finrank_one
    (ξ : ∀ i, NormFamily S (E i)) (hr : ∀ i, Module.finrank K (E i) = 1) :
    projectiveTensor ξ = injectiveTensor ξ := by
  let : ∀ i, Nontrivial (E i) := fun i ↦
    Module.nontrivial_of_finrank_pos (by rw [hr i]; exact zero_lt_one)
  choose x hx using fun i ↦ exists_ne (0 : E i)
  apply eq_of_finrank_one_norm_rational_eq _ _ (tensor_finrank_one hr)
    (tensor_generators_ne_zero hr x hx)
  intro ω
  exact (tensor_norm_rational_generators ξ hr x hx ω).2.1.trans
    (tensor_norm_rational_generators ξ hr x hx ω).1.symm

/-- The mixed tensor norm has the same value on lines at every place. -/
theorem mixedTensor_eq_injectiveTensor_of_finrank_one
    (ξ : ∀ i, NormFamily S (E i)) (hr : ∀ i, Module.finrank K (E i) = 1) :
    mixedTensor ξ = injectiveTensor ξ := by
  let : ∀ i, Nontrivial (E i) := fun i ↦
    Module.nontrivial_of_finrank_pos (by rw [hr i]; exact zero_lt_one)
  choose x hx using fun i ↦ exists_ne (0 : E i)
  apply eq_of_finrank_one_norm_rational_eq _ _ (tensor_finrank_one hr)
    (tensor_generators_ne_zero hr x hx)
  intro ω
  exact (tensor_norm_rational_generators ξ hr x hx ω).2.2.trans
    (tensor_norm_rational_generators ξ hr x hx ω).1.symm

/-- A finite tensor product of measurable lines is measurable, including the empty family. -/
theorem IsMeasurable.injectiveTensor_of_finrank_one {ξ : ∀ i, NormFamily S (E i)}
    (hξ : ∀ i, (ξ i).IsMeasurable) (hr : ∀ i, Module.finrank K (E i) = 1) :
    (injectiveTensor ξ).IsMeasurable := by
  classical
  let : ∀ i, Nontrivial (E i) := fun i ↦
    Module.nontrivial_of_finrank_pos (by rw [hr i]; exact zero_lt_one)
  choose x hx using fun i ↦ exists_ne (0 : E i)
  apply ((injectiveTensor ξ).isMeasurable_iff_norm_one_vector (tensor_finrank_one hr)
    (tensor_generators_ne_zero hr x hx)).2
  simp only [(tensor_norm_rational_generators ξ hr x hx _).1]
  exact Finset.measurable_prod Finset.univ (fun i _ ↦ hξ i (x i))

/-- Measurability of the projective tensor family of lines. -/
theorem IsMeasurable.projectiveTensor_of_finrank_one {ξ : ∀ i, NormFamily S (E i)}
    (hξ : ∀ i, (ξ i).IsMeasurable) (hr : ∀ i, Module.finrank K (E i) = 1) :
    (projectiveTensor ξ).IsMeasurable := by
  rw [projectiveTensor_eq_injectiveTensor_of_finrank_one ξ hr]
  exact IsMeasurable.injectiveTensor_of_finrank_one hξ hr

/-- Measurability of the mixed tensor family of lines. -/
theorem IsMeasurable.mixedTensor_of_finrank_one {ξ : ∀ i, NormFamily S (E i)}
    (hξ : ∀ i, (ξ i).IsMeasurable) (hr : ∀ i, Module.finrank K (E i) = 1) :
    (mixedTensor ξ).IsMeasurable := by
  rw [mixedTensor_eq_injectiveTensor_of_finrank_one ξ hr]
  exact IsMeasurable.injectiveTensor_of_finrank_one hξ hr

/-- The logarithmic norm of a tensor generator is the sum of its factor logarithms. -/
theorem injectiveTensor_logNorm_generators (ξ : ∀ i, NormFamily S (E i))
    (hr : ∀ i, Module.finrank K (E i) = 1) (x : ∀ i, E i) (hx : ∀ i, x i ≠ 0)
    (ω : S.Ω) : (injectiveTensor ξ).logNorm (⨂ₜ[K] i, x i) ω =
      ∑ i, (ξ i).logNorm (x i) ω := by
  classical
  simp only [logNorm, (tensor_norm_rational_generators ξ hr x hx ω).1]
  exact Real.log_prod (fun i _ ↦ ((ξ i).norm_rational_pos ω (hx i)).ne')

/-- Domination of a finite tensor product of lines uses the actual generator formula. -/
theorem IsDominated.injectiveTensor_of_finrank_one {ξ : ∀ i, NormFamily S (E i)}
    (hξ : ∀ i, (ξ i).IsDominated) (hr : ∀ i, Module.finrank K (E i) = 1) :
    (injectiveTensor ξ).IsDominated := by
  classical
  let : ∀ i, Nontrivial (E i) := fun i ↦
    Module.nontrivial_of_finrank_pos (by rw [hr i]; exact zero_lt_one)
  choose x hx using fun i ↦ exists_ne (0 : E i)
  apply ((injectiveTensor ξ).isDominated_iff_logNorm_bounds (tensor_finrank_one hr)
    (tensor_generators_ne_zero hr x hx)).2
  have he : (injectiveTensor ξ).logNorm (⨂ₜ[K] i, x i) =
      fun ω ↦ ∑ i, (ξ i).logNorm (x i) ω :=
    funext (injectiveTensor_logNorm_generators ξ hr x hx)
  rw [he]
  exact hasIntegrableBounds_finset_sum Finset.univ _ (fun i _ ↦ (hξ i).logNorm_bounds (hx i))

/-- Domination of the projective tensor family of lines. -/
theorem IsDominated.projectiveTensor_of_finrank_one {ξ : ∀ i, NormFamily S (E i)}
    (hξ : ∀ i, (ξ i).IsDominated) (hr : ∀ i, Module.finrank K (E i) = 1) :
    (projectiveTensor ξ).IsDominated := by
  rw [projectiveTensor_eq_injectiveTensor_of_finrank_one ξ hr]
  exact IsDominated.injectiveTensor_of_finrank_one hξ hr

/-- Domination of the mixed tensor family of lines. -/
theorem IsDominated.mixedTensor_of_finrank_one {ξ : ∀ i, NormFamily S (E i)}
    (hξ : ∀ i, (ξ i).IsDominated) (hr : ∀ i, Module.finrank K (E i) = 1) :
    (mixedTensor ξ).IsDominated := by
  rw [mixedTensor_eq_injectiveTensor_of_finrank_one ξ hr]
  exact IsDominated.injectiveTensor_of_finrank_one hξ hr

omit [Fintype ι] [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
    [∀ i, FiniteDimensional K (E i)] in
/-- Measurability of a positive tensor power detects measurability of its line. -/
theorem isMeasurable_injectiveTensor_power_iff
    {V : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ξ : NormFamily S V) (hr : Module.finrank K V = 1) (n : ℕ) (hn : n ≠ 0) :
    (injectiveTensor (fun _ : Fin n ↦ ξ)).IsMeasurable ↔ ξ.IsMeasurable := by
  refine ⟨?_, fun h ↦ IsMeasurable.injectiveTensor_of_finrank_one (fun _ ↦ h) (fun _ ↦ hr)⟩
  intro h
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hr]; exact zero_lt_one)
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have he : ξ.logNorm x = fun ω ↦
      (injectiveTensor (fun _ : Fin n ↦ ξ)).logNorm (⨂ₜ[K] _ : Fin n, x) ω / (n : ℝ) := by
    ext ω
    rw [injectiveTensor_logNorm_generators _ (fun _ ↦ hr) _ (fun _ ↦ hx)]
    simp [Nat.cast_ne_zero.mpr hn]
  have hm : Measurable (ξ.logNorm x) := by
    rw [he]
    exact (h.logNorm _).div_const _
  apply (ξ.isMeasurable_iff_norm_one_vector hr hx).2
  convert hm.exp using 1
  ext ω
  exact (Real.exp_log (ξ.norm_rational_pos ω hx)).symm

omit [Fintype ι] [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
    [∀ i, FiniteDimensional K (E i)] in
/-- The positive-power measurability criterion also holds for projective norms. -/
theorem isMeasurable_projectiveTensor_power_iff
    {V : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ξ : NormFamily S V) (hr : Module.finrank K V = 1) (n : ℕ) (hn : n ≠ 0) :
    (projectiveTensor (fun _ : Fin n ↦ ξ)).IsMeasurable ↔ ξ.IsMeasurable := by
  rw [projectiveTensor_eq_injectiveTensor_of_finrank_one _ (fun _ ↦ hr)]
  exact isMeasurable_injectiveTensor_power_iff ξ hr n hn

omit [Fintype ι] [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
    [∀ i, FiniteDimensional K (E i)] in
/-- The positive-power measurability criterion for the source mixed tensor norms. -/
theorem isMeasurable_mixedTensor_power_iff
    {V : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ξ : NormFamily S V) (hr : Module.finrank K V = 1) (n : ℕ) (hn : n ≠ 0) :
    (mixedTensor (fun _ : Fin n ↦ ξ)).IsMeasurable ↔ ξ.IsMeasurable := by
  rw [mixedTensor_eq_injectiveTensor_of_finrank_one _ (fun _ ↦ hr)]
  exact isMeasurable_injectiveTensor_power_iff ξ hr n hn

end
end ArakelovGeometry.NormFamily
