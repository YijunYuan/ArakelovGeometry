/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.TensorNorm
public import ArakelovGeometry.Analysis.UltrametricDual

/-!
# Pure tensors for ultrametric injective norms

Approximate norming functionals on each factor prove the exact crossnorm
identity by letting their loss decrease to one. No norm-attaining extension
or spherical completeness is assumed.
-/

@[expose] public section

open Filter
open scoped TensorProduct Topology

namespace ArakelovGeometry

variable {L ι : Type*} [NormedField L] [CompleteSpace L] [Fintype ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace L (E i)]
  [∀ i, FiniteDimensional L (E i)] [∀ i, IsUltrametricDist (E i)]

/-- The injective norm of a pure tensor is exactly the product norm for
finite-dimensional ultrametric factors, including zero and empty factors. -/
theorem injectiveTensorSeminorm_tprod_eq_of_ultrametric (x : ∀ i, E i) :
    injectiveTensorSeminorm (⨂ₜ[L] i, x i) = ∏ i, ‖x i‖ := by
  classical
  apply le_antisymm
  · exact (injectiveTensorSeminorm_le_projective _).trans
      (PiTensorProduct.projectiveSeminorm_tprod_le x)
  by_cases hx : ∀ i, x i ≠ 0
  · have hp : 0 < ∏ i, ‖x i‖ := Finset.prod_pos fun i _ => norm_pos_iff.mpr (hx i)
    have hA (A : ℝ) (hA : 1 < A) :
        ∏ i, ‖x i‖ ≤ injectiveTensorSeminorm (⨂ₜ[L] i, x i) * A ^ Fintype.card ι := by
      choose φ hφ hnorm using fun i => exists_ultrametric_norming_functional (L := L) (hx i) hA
      have hφpos (i : ι) : 0 < linearMapOperatorSeminorm (φ i) := by
        apply lt_of_le_of_ne (apply_nonneg _ _)
        intro heq
        have hz := (linearMapOperatorSeminorm_eq_zero_iff (φ i)).mp heq.symm
        have := hφ i
        simp only [hz, LinearMap.zero_apply] at this
        exact zero_ne_one this
      have hd : 0 < ∏ i, linearMapOperatorSeminorm (φ i) :=
        Finset.prod_pos fun i _ => hφpos i
      have heval : tensorDualEval φ (⨂ₜ[L] i, x i) = 1 := by
        simp only [tensorDualEval_tprod, hφ, Finset.prod_const_one]
      have hr := tensorDualRatioSeminorm_le_injective φ (⨂ₜ[L] i, x i)
      rw [tensorDualRatioSeminorm_apply, heval, norm_one] at hr
      have hr' := (div_le_iff₀ hd).mp hr
      have hd' : (∏ i, linearMapOperatorSeminorm (φ i)) ≤
          A ^ Fintype.card ι / ∏ i, ‖x i‖ := by
        calc
          _ ≤ ∏ i, A / ‖x i‖ := Finset.prod_le_prod₀ (fun i _ => (hφpos i).le)
            (fun i _ => hnorm i)
          _ = _ := by rw [Finset.prod_div_distrib]; simp only [Finset.prod_const,
            Finset.card_univ]
      have hr'' := hr'.trans (mul_le_mul_of_nonneg_left hd'
        (apply_nonneg injectiveTensorSeminorm _))
      rw [← mul_div_assoc] at hr''
      simpa only [one_mul] using (le_div_iff₀ hp).mp hr''
    have ht : Tendsto
        (fun A : ℝ => injectiveTensorSeminorm (⨂ₜ[L] i, x i) * A ^ Fintype.card ι)
        (𝓝[>] 1) (𝓝 (injectiveTensorSeminorm (⨂ₜ[L] i, x i))) := by
      have hc : Continuous (fun A : ℝ =>
          injectiveTensorSeminorm (⨂ₜ[L] i, x i) * A ^ Fintype.card ι) :=
        (continuous_id.pow (Fintype.card ι)).const_mul _
      simpa only [one_pow, mul_one] using
        (hc.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto ht (Filter.Eventually.mono self_mem_nhdsWithin
      fun A h => hA A h)
  · push Not at hx
    obtain ⟨i, hi⟩ := hx
    have ht : (⨂ₜ[L] j, x j) = 0 := (PiTensorProduct.tprod L).map_coord_zero i hi
    rw [ht, map_zero]
    exact le_of_eq (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, norm_zero]))

/-- The projective norm has the same exact pure-tensor formula for ultrametric
factors; the injective lower bound supplies the nontrivial direction. -/
theorem projectiveSeminorm_tprod_eq_of_ultrametric (x : ∀ i, E i) :
    PiTensorProduct.projectiveSeminorm (⨂ₜ[L] i, x i) = ∏ i, ‖x i‖ := by
  apply le_antisymm (PiTensorProduct.projectiveSeminorm_tprod_le x)
  exact (injectiveTensorSeminorm_tprod_eq_of_ultrametric x).symm.le.trans
    (injectiveTensorSeminorm_le_projective _)

end ArakelovGeometry
