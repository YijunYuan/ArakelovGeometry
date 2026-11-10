/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.CountableTensorMeasurable

/-!
# Countable injective tensor and exterior-power formulas

Completed product evaluations extend from dense rational dual tuples.
The resulting countable supremum gives injective and mixed tensor
measurability and, by quotient, exterior-power measurability.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

universe u v w wι wκ

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {ι : Type wι} [Fintype ι] {E : ι → Type w}
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)]
  (ξ : ∀ i, NormFamily S (E i))

omit [Fintype ι] in
/-- The completed product pairing agrees with the original rational tensor pairing. -/
theorem tensorDualEval_rational [Finite ι] (ℓ : ∀ i, Module.Dual K (E i))
    (z : ⨂[K] i, E i) (ω : S.Ω) :
    PiTensorProduct.dualDistrib (⨂ₜ[(S.ϕ ω).Completion] i,
        dualBaseChangeEquiv K (S.ϕ ω).Completion (E i)
          ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ i))
      (tensorBaseChangeEquiv K (S.ϕ ω).Completion E
        ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] z)) =
      algebraMap K (S.ϕ ω).Completion (PiTensorProduct.dualDistrib (⨂ₜ[K] i, ℓ i) z) := by
  let := Fintype.ofFinite ι
  induction z using PiTensorProduct.induction_on with
  | smul_tprod a x =>
    rw [← TensorProduct.smul_tmul]
    simp only [Algebra.smul_def, mul_one,
      tensorBaseChangeEquiv_tmul_tprod, map_smul, PiTensorProduct.dualDistrib_apply,
      dualBaseChangeEquiv_tmul_apply_tmul, one_mul, map_mul, map_prod]
    rfl
  | add x y hx hy =>
    simp only [TensorProduct.tmul_add, map_add, hx, hy]

omit [Fintype ι] in
/-- A completed tensor evaluated on a tuple of completed dual vectors is
continuous for the actual dual norms, including over trivially valued fields. -/
theorem continuous_completed_tensorDualEval [Finite ι] (ω : S.Ω)
    (z : ⨂[(S.ϕ ω).Completion] i, (S.ϕ ω).Completion ⊗[K] E i) :
    letI : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] Module.Dual K (E i)) :=
      fun i => (ξ i).dual.fibreNormedAddCommGroup ω
    Continuous (fun φ : ∀ i, (S.ϕ ω).Completion ⊗[K] Module.Dual K (E i) =>
      PiTensorProduct.dualDistrib (⨂ₜ[(S.ϕ ω).Completion] i,
        dualBaseChangeEquiv K (S.ϕ ω).Completion (E i) (φ i)) z) := by
  let := Fintype.ofFinite ι
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] Module.Dual K (E i)) :=
    fun i => (ξ i).dual.fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion
      ((S.ϕ ω).Completion ⊗[K] Module.Dual K (E i)) :=
    fun i => (ξ i).dual.fibreNormedSpace ω
  have heval (i : ι) (x : (S.ϕ ω).Completion ⊗[K] E i) :
      Continuous (fun φ : (S.ϕ ω).Completion ⊗[K] Module.Dual K (E i) =>
        dualBaseChangeEquiv K (S.ϕ ω).Completion (E i) φ x) :=
    (linearMapToNormedAddGroupHom ((LinearMap.applyₗ x).comp
      (dualBaseChangeEquiv K (S.ϕ ω).Completion (E i)).toLinearMap)).continuous
  induction z using PiTensorProduct.induction_on with
  | smul_tprod a x =>
    simp only [map_smul, PiTensorProduct.dualDistrib_apply, smul_eq_mul]
    exact continuous_const.mul (continuous_finsetProd _
      (fun i _ => (heval i (x i)).comp (continuous_apply i)))
  | add x y hx hy =>
    simp only [map_add]
    exact hx.add hy

variable {κ : ι → Type wκ} [∀ i, Fintype (κ i)]

/-- The actual injective norm is the supremum over one dense rational dual
coordinate set. Zero dual vectors are admitted and contribute zero ratios. -/
theorem injectiveTensor_norm_eq_iSup_basisSubfield
    (b : ∀ i, Module.Basis (κ i) K (Module.Dual K (E i)))
    (K₀ : Subfield K) (ω : S.Ω) (hK₀ : S.IsDenseSubfieldAt K₀ ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (injectiveTensor ξ).norm ω z = ⨆ c : ∀ i, κ i → K₀,
      ‖PiTensorProduct.dualDistrib (⨂ₜ[(S.ϕ ω).Completion] i,
          dualBaseChangeEquiv K (S.ϕ ω).Completion (E i)
            ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] basisSubfieldMap (b i) K₀ (c i)))
        (tensorBaseChangeEquiv K (S.ϕ ω).Completion E z)‖ /
        ∏ i, (ξ i).dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K]
          basisSubfieldMap (b i) K₀ (c i)) := by
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i => (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i => (ξ i).fibreNormedSpace ω
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] Module.Dual K (E i)) :=
    fun i => (ξ i).dual.fibreNormedAddCommGroup ω
  let A : (∀ i, (S.ϕ ω).Completion ⊗[K] Module.Dual K (E i)) → (S.ϕ ω).Completion :=
    fun φ => PiTensorProduct.dualDistrib (⨂ₜ[(S.ϕ ω).Completion] i,
      dualBaseChangeEquiv K (S.ϕ ω).Completion (E i) (φ i))
        (tensorBaseChangeEquiv K (S.ϕ ω).Completion E z)
  let D : (∀ i, (S.ϕ ω).Completion ⊗[K] Module.Dual K (E i)) → ℝ :=
    fun φ => ∏ i, (ξ i).dual.norm ω (φ i)
  let r : (∀ i, κ i → K₀) → ∀ i, (S.ϕ ω).Completion ⊗[K] Module.Dual K (E i) :=
    fun c i => (1 : (S.ϕ ω).Completion) ⊗ₜ[K] basisSubfieldMap (b i) K₀ (c i)
  let R : (∀ i, κ i → K₀) → ℝ := fun c => ‖A (r c)‖ / D (r c)
  have hD (φ) : 0 ≤ D φ := Finset.prod_nonneg fun i _ => (ξ i).dual.norm_nonneg ω _
  have hA (φ) : ‖A φ‖ ≤ D φ * (projectiveTensor ξ).norm ω z :=
    norm_tensorDualEval_le_projective
      (fun i => dualBaseChangeEquiv K (S.ϕ ω).Completion (E i) (φ i))
      (tensorBaseChangeEquiv K (S.ϕ ω).Completion E z)
  have hR (c) : R c ≤ (injectiveTensor ξ).norm ω z :=
    (tensorDualRatioSeminorm_apply _ _).symm.le.trans
      (tensorDualRatioSeminorm_le_injective
        (fun i => dualBaseChangeEquiv K (S.ϕ ω).Completion (E i) (r c i))
          (tensorBaseChangeEquiv K (S.ϕ ω).Completion E z))
  have hb : BddAbove (Set.range R) := ⟨(injectiveTensor ξ).norm ω z,
    by rintro _ ⟨c, rfl⟩; exact hR c⟩
  have h0 : 0 ≤ ⨆ c, R c := Real.iSup_nonneg fun c =>
    div_nonneg (_root_.norm_nonneg _) (hD _)
  have hAc : Continuous A := continuous_completed_tensorDualEval ξ ω _
  have hDc : Continuous D := by
    change Continuous (fun φ : ∀ i, (S.ϕ ω).Completion ⊗[K] Module.Dual K (E i) =>
      ∏ i, ‖φ i‖)
    fun_prop
  have hd : DenseRange r := DenseRange.piMap fun i =>
    (ξ i).dual.denseRange_basisSubfieldMap (b i) K₀ ω hK₀
  have hclosed (φ) : ‖A φ‖ ≤ (⨆ c, R c) * D φ := by
    apply hd.induction_on (p := fun φ => ‖A φ‖ ≤ (⨆ c, R c) * D φ) φ
      (isClosed_le hAc.norm (continuous_const.mul hDc))
    intro c
    by_cases hzero : D (r c) = 0
    · simpa only [hzero, zero_mul, mul_zero] using hA (r c)
    · exact (div_le_iff₀ (lt_of_le_of_ne (hD _) (Ne.symm hzero))).mp (le_ciSup hb c)
  change (injectiveTensor ξ).norm ω z = ⨆ c, R c
  apply le_antisymm
  · apply (ArakelovGeometry.injectiveTensorSeminorm_le_iff _ _).mpr
    intro φ
    let ψ := fun i => (dualBaseChangeEquiv K (S.ϕ ω).Completion (E i)).symm (φ i)
    have H := div_le_of_le_mul₀ (hD ψ) h0 (hclosed ψ)
    simpa only [A, D, ψ, dual, dualSeminorm, Seminorm.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, tensorDualEval] using H
  · exact ciSup_le hR

/-- On a rational tensor the countable injective formula uses only rational
absolute values and rational dual-norm evaluations. -/
theorem injectiveTensor_norm_rational_eq_iSup_basisSubfield
    (b : ∀ i, Module.Basis (κ i) K (Module.Dual K (E i)))
    (K₀ : Subfield K) (ω : S.Ω) (hK₀ : S.IsDenseSubfieldAt K₀ ω)
    (z : ⨂[K] i, E i) :
    (injectiveTensor ξ).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] z) =
      ⨆ c : ∀ i, κ i → K₀,
        (S.ϕ ω) (PiTensorProduct.dualDistrib
          (⨂ₜ[K] i, basisSubfieldMap (b i) K₀ (c i)) z) /
          ∏ i, (ξ i).dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K]
            basisSubfieldMap (b i) K₀ (c i)) := by
  rw [injectiveTensor_norm_eq_iSup_basisSubfield ξ b K₀ ω hK₀]
  simp only [tensorDualEval_rational, S.norm_algebraMap_eq_absValue]

/-- The common countable dense subfield makes the actual injective tensor
family measurable whenever its factors are measurable. -/
theorem IsMeasurable.injectiveTensor_of_common_countable_dense_subfield
    (hξ : ∀ i, (ξ i).IsMeasurable) (hS : S.HasCommonCountableDenseSubfield) :
    (injectiveTensor ξ).IsMeasurable := by
  obtain ⟨K₀, hcount, hdense⟩ := hS
  let : Countable K₀ := hcount
  let b := fun i => Module.finBasis K (Module.Dual K (E i))
  have hdual (i : ι) := (hξ i).dual_of_countable_dense_subfield K₀ hdense
  intro z
  simp_rw [injectiveTensor_norm_rational_eq_iSup_basisSubfield ξ b K₀ _ (hdense _) z]
  exact Measurable.iSup fun c => (S.measurable_absValue _).div
    (Finset.measurable_prod _ (fun i _ => hdual i (basisSubfieldMap (b i) K₀ (c i))))

/-- Pasting injective and projective norms on the measurable finite-place
locus gives measurability of the source's mixed tensor family. -/
theorem IsMeasurable.mixedTensor_of_common_countable_dense_subfield
    (hξ : ∀ i, (ξ i).IsMeasurable) (hS : S.HasCommonCountableDenseSubfield) :
    (mixedTensor ξ).IsMeasurable := by
  classical
  have hε := IsMeasurable.injectiveTensor_of_common_countable_dense_subfield ξ hξ hS
  have hπ := IsMeasurable.projectiveTensor_of_common_countable_dense_subfield ξ hξ hS
  intro z
  have he : (fun ω => (mixedTensor ξ).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] z)) =
      S.Ωfin.piecewise
        (fun ω => (injectiveTensor ξ).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] z))
        (fun ω => (projectiveTensor ξ).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] z)) := by
    funext ω
    by_cases hω : ω ∈ S.Ωfin
    · rw [mixedTensor_norm_of_mem_Ωfin ξ ω hω, Set.piecewise_eq_of_mem S.Ωfin _ _ hω]
    · rw [mixedTensor_norm_of_not_mem_Ωfin ξ ω hω,
        Set.piecewise_eq_of_notMem S.Ωfin _ _ hω]
  rw [he]
  have hfin : MeasurableSet S.Ωfin := by
    convert S.measurableSet_Ωinf.compl using 1
    ext ω
    exact not_not.symm
  exact Measurable.piecewise hfin (hε z) (hπ z)

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.NormFamily

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Every actual exterior-power family is measurable as a quotient of the
mixed tensor power. Degree zero and zero-dimensional spaces are included. -/
theorem IsMeasurable.exteriorPower_of_common_countable_dense_subfield
    {ξ : NormFamily S E} (hξ : ξ.IsMeasurable) (hS : S.HasCommonCountableDenseSubfield)
    (n : ℕ) : (ξ.exteriorPower n).IsMeasurable := by
  have ht := IsMeasurable.mixedTensor_of_common_countable_dense_subfield
    (fun _ : Fin n => ξ) (fun _ => hξ) hS
  exact ht.pushforward_of_common_countable_dense_subfield
    (tensorToExterior K E n) (tensorToExterior_surjective K E n) hS

end ArakelovGeometry.NormFamily
