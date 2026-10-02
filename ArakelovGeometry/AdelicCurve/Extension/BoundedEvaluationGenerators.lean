/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Extension.Separable.Measurability
import ArakelovGeometry.ExternalResults.AbsoluteValueRootBounds
import ArakelovGeometry.ExternalResults.BoundedFunctionalMonotoneClass

/-!
# Bounded multiplicative generators of extension places

Bounded evaluations localized by bounded measurable base functions generate the
parameter-space sigma algebra, as used in Chen–Moriwaki, Theorem 3.3.4.
-/

open MeasureTheory Filter Topology
namespace ArakelovGeometry.AdelicStructure.ParameterSpaceExtension
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (AS : AdelicStructure K)

/-- Bounded evaluation products with a bounded nonnegative measurable base factor. -/
def boundedEvaluationGenerators : Set (ParameterSpaceExtension AS L → ℝ) :=
  {f | (∃ M : ℝ, ∀ x, |f x| ≤ M) ∧
    ∃ b : L, ∃ φ : AS.Ω → ℝ, Measurable φ ∧ (∀ ω, 0 ≤ φ ω) ∧
      (∃ M : ℝ, ∀ ω, |φ ω| ≤ M) ∧ f = fun x ↦ x.ϕ b * φ x.proj}

/-- The constant one is a bounded evaluation generator. -/
theorem one_mem_boundedEvaluationGenerators :
    (1 : ParameterSpaceExtension AS L → ℝ) ∈ boundedEvaluationGenerators AS := by
  refine ⟨⟨1, by simp⟩, 1, fun _ ↦ 1, measurable_const, fun _ ↦ zero_le_one,
    ⟨1, by simp⟩, ?_⟩
  ext x
  simp

/-- Bounded evaluation generators form a multiplicative family. -/
theorem mul_mem_boundedEvaluationGenerators {f g : ParameterSpaceExtension AS L → ℝ}
    (hf : f ∈ boundedEvaluationGenerators AS) (hg : g ∈ boundedEvaluationGenerators AS) :
    f * g ∈ boundedEvaluationGenerators AS := by
  rcases hf with ⟨⟨M, hM⟩, b, φ, hφ, hφ0, ⟨N, hN⟩, rfl⟩
  rcases hg with ⟨⟨P, hP⟩, c, ψ, hψ, hψ0, ⟨Q, hQ⟩, rfl⟩
  refine ⟨⟨|M| * |P|, fun x ↦ ?_⟩, b * c, φ * ψ, hφ.mul hψ,
    fun ω ↦ mul_nonneg (hφ0 ω) (hψ0 ω), ⟨|N| * |Q|, fun ω ↦ ?_⟩, ?_⟩
  · change |(x.ϕ b * φ x.proj) * (x.ϕ c * ψ x.proj)| ≤ _
    rw [abs_mul]
    exact mul_le_mul ((hM x).trans (le_abs_self M)) ((hP x).trans (le_abs_self P))
      (abs_nonneg _) (abs_nonneg _)
  · change |φ ω * ψ ω| ≤ _
    rw [abs_mul]
    exact mul_le_mul ((hN ω).trans (le_abs_self N)) ((hQ ω).trans (le_abs_self Q))
      (abs_nonneg _) (abs_nonneg _)
  · ext x
    simp only [Pi.mul_apply, map_mul]
    ring

private theorem measurable_base_eval (a : K) : Measurable (fun ω ↦ AS.ϕ ω a) := by
  by_cases ha : a = 0
  · simp [ha]
  · have h : (fun ω ↦ AS.ϕ ω a) = fun ω ↦ Real.exp (Real.log (AS.ϕ ω a)) := by
      funext ω
      exact (Real.exp_log ((AS.ϕ ω).pos ha)).symm
    rw [h]
    exact (AS.measurable_log a ha).exp

private theorem exists_measurable_eval_bound [Algebra.IsAlgebraic K L] (b : L) :
    ∃ B : AS.Ω → ℝ, Measurable B ∧
      ∀ x : ParameterSpaceExtension AS L, x.ϕ b ≤ B x.proj := by
  classical
  let p := minpoly K b
  let M := fun ω ↦ 1 + ∑ i ∈ Finset.range p.natDegree, AS.ϕ ω (p.coeff i)
  have hM : Measurable M := measurable_const.add
    (Finset.measurable_fun_sum _ fun i _ ↦ measurable_base_eval AS (p.coeff i))
  refine ⟨fun ω ↦ (p.natDegree : ℝ) * M ω, measurable_const.mul hM, fun x ↦ ?_⟩
  apply x.ϕ.apply_root_le_degree_mul (minpoly.monic (Algebra.IsIntegral.isIntegral b))
    (minpoly.aeval K b)
  · dsimp [M]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ (AS.ϕ x.proj).nonneg _)
  · intro i hi
    have hr : x.ϕ (algebraMap K L (p.coeff i)) = AS.ϕ x.proj (p.coeff i) :=
      congrArg (fun v : AbsoluteValue K ℝ ↦ v (p.coeff i)) (ϕ_restriction AS L x)
    rw [hr]
    exact (Finset.single_le_sum (fun j _ ↦ (AS.ϕ x.proj).nonneg _)
      (Finset.mem_range.mpr hi)).trans (le_add_of_nonneg_left zero_le_one)

/-- Bounded evaluation generators generate the full extension parameter sigma algebra. -/
theorem measurableSpace_eq_iSup_comap_boundedEvaluationGenerators [Algebra.IsAlgebraic K L] :
    (inferInstance : MeasurableSpace (ParameterSpaceExtension AS L)) =
      ⨆ g : boundedEvaluationGenerators AS (L := L),
        MeasurableSpace.comap g.val inferInstance := by
  classical
  let m : MeasurableSpace (ParameterSpaceExtension AS L) :=
    ⨆ g : boundedEvaluationGenerators AS (L := L),
      MeasurableSpace.comap g.val inferInstance
  have hgen (f : ParameterSpaceExtension AS L → ℝ) (hf : f ∈ boundedEvaluationGenerators AS) :
      @Measurable _ ℝ m _ f :=
    Measurable.of_comap_le (le_iSup_of_le ⟨f, hf⟩ le_rfl)
  have hind (A : Set AS.Ω) (hA : MeasurableSet A) :
      (fun x : ParameterSpaceExtension AS L ↦ x.ϕ 1 * (A.indicator fun _ ↦ (1 : ℝ)) x.proj)
        ∈ boundedEvaluationGenerators AS := by
    refine ⟨⟨1, fun x ↦ ?_⟩, 1, A.indicator fun _ ↦ 1, measurable_const.indicator hA,
      Set.indicator_nonneg (fun _ _ ↦ zero_le_one), ⟨1, fun ω ↦ ?_⟩, rfl⟩
    · by_cases hx : x.proj ∈ A <;> simp [hx]
    · by_cases hω : ω ∈ A <;> simp [hω]
  apply le_antisymm
  · change MeasurableSpace.comap (proj (AS := AS) (L := L)) AS.A ⊔
      (⨆ b : L, MeasurableSpace.comap (fun x : ParameterSpaceExtension AS L ↦ x.ϕ b)
        inferInstance) ≤ m
    apply sup_le
    · apply Measurable.comap_le
      intro A hA
      have hm := hgen _ (hind A hA)
      have hi : @Measurable (ParameterSpaceExtension AS L) ℝ m _
          ((proj ⁻¹' A).indicator fun _ ↦ (1 : ℝ)) := by
        simpa only [map_one, one_mul, ← Set.indicator_comp_right, Function.comp_def] using hm
      exact (measurable_indicator_const_iff (1 : ℝ)).mp hi
    · apply iSup_le
      intro b
      obtain ⟨B, hB, hbound⟩ := exists_measurable_eval_bound AS b
      let A (n : ℕ) := {ω | B ω ≤ (n : ℝ)}
      have hA (n : ℕ) : MeasurableSet (A n) := measurableSet_le hB measurable_const
      let u (n : ℕ) (x : ParameterSpaceExtension AS L) :=
        x.ϕ b * ((A n).indicator fun _ ↦ (1 : ℝ)) x.proj
      have hu (n : ℕ) : u n ∈ boundedEvaluationGenerators AS := by
        refine ⟨⟨(n : ℝ), fun x ↦ ?_⟩, b, (A n).indicator fun _ ↦ 1,
          measurable_const.indicator (hA n), Set.indicator_nonneg (fun _ _ ↦ zero_le_one),
          ⟨1, fun ω ↦ ?_⟩, rfl⟩
        · by_cases hx : x.proj ∈ A n
          · simpa only [u, Set.indicator_of_mem hx, mul_one, abs_of_nonneg (x.ϕ.nonneg b)]
              using (hbound x).trans hx
          · simp [u, Set.indicator_of_notMem hx]
        · by_cases hω : ω ∈ A n <;> simp [hω]
      have hlim : Tendsto u atTop (𝓝 (fun x : ParameterSpaceExtension AS L ↦ x.ϕ b)) := by
        apply tendsto_pi_nhds.mpr
        intro x
        apply tendsto_const_nhds.congr'
        filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (B x.proj))]
          with n hn
        simp [u, A, hn]
      exact (@measurable_of_tendsto_metrizable _ _ m _ _ _ _ u _ (fun n ↦ hgen _ (hu n))
        hlim).comap_le
  · apply iSup_le
    rintro ⟨g, hg⟩
    rcases hg with ⟨_, b, φ, hφ, _, _, rfl⟩
    exact ((measurable_eval AS L b).mul (hφ.comp (measurable_proj AS L))).comap_le

variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- The bounded monotone-class argument makes bounded measurable fibre averages measurable. -/
theorem measurable_fibreIntegral_of_bounded {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Measurable f) (hfb : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    Measurable (fibreIntegral AS L f) := by
  let H : Submodule ℝ (ParameterSpaceExtension AS L → ℝ) := {
    carrier := {f | Measurable (fibreIntegral AS L f)}
    zero_mem' := by
      change Measurable fun ω : AS.Ω ↦
        ∫ _x : ExtensionFiber AS L ω, (0 : ℝ) ∂fibreProbabilityMeasure AS L ω
      simp only [integral_zero]
      exact measurable_const
    add_mem' := fun hf hg ↦ by
      change Measurable (fibreIntegral AS L (_ + _))
      rw [fibreIntegral_add]
      exact hf.add hg
    smul_mem' := fun c f hf ↦ by
      change Measurable (fibreIntegral AS L (c • f))
      rw [fibreIntegral_smul]
      exact hf.const_smul c }
  have hCH : boundedEvaluationGenerators AS (L := L) ⊆ (H : Set _) := by
    rintro g ⟨_, b, φ, hφ, _, _, rfl⟩
    change Measurable (fibreIntegral AS L (fun x ↦ x.ϕ b * φ x.proj))
    have heq : (fun x : ParameterSpaceExtension AS L ↦ x.ϕ b * φ x.proj) =
        fun x ↦ φ x.proj * x.ϕ b := by
      ext x
      exact mul_comm _ _
    rw [heq, fibreIntegral_comp_proj_mul]
    exact hφ.mul (measurable_fibreIntegral_eval AS L b)
  apply MeasureTheory.measurable_mem_of_bounded_pointwise_closed H
    (C := boundedEvaluationGenerators AS)
    (fun {_ _} hu _ huf ↦ measurable_of_tendsto_metrizable hu
      (tendsto_pi_nhds.mpr fun ω ↦
        tendsto_fibreIntegral AS L _ _ (fun x ↦ tendsto_pi_nhds.mp huf x) ω))
    (fun _ hf ↦ hf.1) (one_mem_boundedEvaluationGenerators AS)
    (fun _ hf _ hg ↦ mul_mem_boundedEvaluationGenerators AS hf hg) hCH _ hfb
  rw [← measurableSpace_eq_iSup_comap_boundedEvaluationGenerators AS]
  exact hf

/-- Truncation removes the bound from the bounded-generator proof of fibre measurability. -/
theorem measurable_fibreIntegral_via_bounded_generators {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Measurable f) : Measurable (fibreIntegral AS L f) := by
  let u (n : ℕ) (x : ParameterSpaceExtension AS L) := max (-(n : ℝ)) (min n (f x))
  have hu (n : ℕ) : Measurable (fibreIntegral AS L (u n)) :=
    measurable_fibreIntegral_of_bounded AS (measurable_const.max (measurable_const.min hf))
      ⟨n, fun x ↦ abs_le.mpr ⟨le_max_left _ _, max_le (by linarith [Nat.cast_nonneg (α := ℝ) n])
        (min_le_left _ _)⟩⟩
  apply measurable_of_tendsto_metrizable hu
  apply tendsto_pi_nhds.mpr
  intro ω
  apply tendsto_fibreIntegral AS L
  intro x
  apply tendsto_const_nhds.congr'
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop |f x|)] with n hn
  have hx := abs_le.mp hn
  simp only [u, min_eq_right hx.2, max_eq_right hx.1]
end ArakelovGeometry.AdelicStructure.ParameterSpaceExtension
