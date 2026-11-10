/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldLatticeLambda
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldNormalizationHermitian
import ArakelovGeometry.AdelicVectorBundle.LogarithmicMinimaFinite

/-!
# Finite endpoints for the actual integral-basis invariant

The proper actual number-field curve and its produced usual Archimedean
completions give finite ordinary minima. The integral-basis lower comparison
then bounds the actual lattice invariant above; coherence supplies the lower
endpoint. No endpoint or small-vector separation certificate is assumed.
-/

noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

open AdelicStructure NormFamily

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- The genuine proper normalized curve and its usual completed fields
exclude the upper endpoint for every positive ordinary index. -/
theorem normalizedNumberField_logarithmicMinimum_ne_top
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    {i : ℕ} (hi : 1 ≤ i) : V.logarithmicMinimum i ≠ ⊤ := by
  let := normalizedNumberFieldAdelicStructure_isProper (K := K)
  exact V.logarithmicMinimum_ne_top
    (Or.inr (Or.inl ⟨
      inferInstanceAs (Countable {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}),
      inferInstanceAs (DiscreteMeasurableSpace
        {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})⟩))
    normalizedNumberFieldArchimedeanCompletions hi

/-- Positive rank and the actual last-minimum comparison exclude an
infinite integral-basis threshold supremum, without coherence. -/
theorem latticeLambda_ne_top_of_finrank_pos
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hr : 0 < Module.finrank K E) : V.toNormFamily.latticeLambda ≠ ⊤ := by
  intro htop
  have h := V.degree_mul_latticeLambda_le_minimalLogarithmicMinimum
  rw [htop, EReal.coe_mul_top_of_pos (Nat.cast_pos.mpr Module.finrank_pos)] at h
  exact V.normalizedNumberField_logarithmicMinimum_ne_top hr
    (top_le_iff.mp h)

/-- Coherence supplies a real lower endpoint and the actual finite ordinary
minimum supplies the upper endpoint. The real value is produced. -/
theorem latticeLambda_eq_coe_of_coherent
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hc : V.toNormFamily.HasFiniteNormExceptions)
    (hr : 0 < Module.finrank K E) :
    V.toNormFamily.latticeLambda = (V.toNormFamily.latticeLambda.toReal : EReal) :=
  (EReal.coe_toReal (V.latticeLambda_ne_top_of_finrank_pos hr)
    hc.latticeLambda_ne_bot).symm

/-- The actual first ordinary minimum gives a finite uniform upper bound
on every nonzero rational vector's degree. -/
theorem vectorDegree_le_normalizedNumberField_firstMinimum
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hr : 0 < Module.finrank K E) (s : {x : E // x ≠ 0}) :
    V.vectorDegree s ≤ V.maximalLogarithmicMinimum.toReal := by
  have hs := V.coe_le_logarithmicMinimum_of_linearIndependent
    (fun _ : Fin 1 => s) (linearIndependent_unique_iff.mpr s.property) (fun _ => le_rfl)
  have he := EReal.coe_toReal (V.normalizedNumberField_logarithmicMinimum_ne_top (i := 1) le_rfl)
    (V.logarithmicMinimum_ne_bot hr)
  change (V.maximalLogarithmicMinimum.toReal : EReal) = V.maximalLogarithmicMinimum at he
  change (V.vectorDegree s : EReal) ≤ V.maximalLogarithmicMinimum at hs
  rw [← he] at hs
  exact EReal.coe_le_coe_iff.mp hs

/-- A genuine infinite place witnesses positivity of the actual
Archimedean maximum on every nonzero rational vector. -/
theorem archimedeanMaxNorm_pos
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    {x : E} (hx : x ≠ 0) : 0 < V.toNormFamily.archimedeanMaxNorm x := by
  let w : NumberField.InfinitePlace K := Classical.choice inferInstance
  have h := (V.toNormFamily.archimedeanMaxNorm_le_iff x
    (V.toNormFamily.archimedeanMaxNorm_nonneg x)).mp le_rfl
    (normalizedInfinitePlacePoint w) (normalizedInfinitePlacePoint_mem_inf w)
  exact (V.toNormFamily.norm_rational_pos (normalizedInfinitePlacePoint w) hx).trans_le h

/-- The finite first minimum produces a uniform positive lower bound for
the Archimedean size of every nonzero actual integral vector. -/
theorem exists_pos_le_archimedeanMaxNorm_of_globalUnitBall
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hr : 0 < Module.finrank K E) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ V.toNormFamily.globalUnitBall,
      x ≠ 0 → c ≤ V.toNormFamily.archimedeanMaxNorm x := by
  let d : ℝ := Module.finrank ℚ K
  let μ : ℝ := V.maximalLogarithmicMinimum.toReal
  have hd : 0 < d := Nat.cast_pos.mpr Module.finrank_pos
  refine ⟨Real.exp (-(μ / d)), Real.exp_pos _, fun x hx hnx => ?_⟩
  by_contra h
  let p : ℝ := V.toNormFamily.archimedeanMaxNorm x
  have hp : 0 < p := V.archimedeanMaxNorm_pos hnx
  have hlt : p < Real.exp (-(μ / d)) := lt_of_not_ge h
  have hlog := Real.log_lt_log hp hlt
  rw [Real.log_exp] at hlog
  have hmul : μ < d * (-Real.log p) := by
    calc
      μ = d * (μ / d) := (mul_div_cancel₀ μ hd.ne').symm
      _ < d * (-Real.log p) := mul_lt_mul_of_pos_left (by linarith) hd
  have hbound := V.toNormFamily.vectorDegree_ge_of_integral_archimedean_bound
    V.isDominated V.isMeasurable ⟨x, hnx⟩ hx
    (a := -Real.log p) (by rw [neg_neg, Real.exp_log hp])
  have hupper := V.vectorDegree_le_normalizedNumberField_firstMinimum hr ⟨x, hnx⟩
  exact (not_lt_of_ge (hbound.trans hupper)) hmul

end ArakelovGeometry.AdelicVectorBundle

namespace ArakelovGeometry.NormFamily

open AdelicStructure

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- The source coherent dominated family has a finite actual integral-basis
invariant in every positive rank. Both measurability clauses follow from the
actual discrete place space. -/
theorem HasFiniteNormExceptions.latticeLambda_eq_coe
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hc : ξ.HasFiniteNormExceptions) (hd : ξ.IsDominated)
    (hr : 0 < Module.finrank K E) :
    ξ.latticeLambda = (ξ.latticeLambda.toReal : EReal) := by
  let normalizedDiscrete : DiscreteMeasurableSpace
      (normalizedNumberFieldAdelicStructure K).Ω := inferInstanceAs
    (DiscreteMeasurableSpace {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
  let V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E :=
    { toNormFamily := ξ
      isMeasurable := ξ.isMeasurable_of_discrete
      dual_isMeasurable := ξ.dual.isMeasurable_of_discrete
      isDominated := hd }
  exact V.latticeLambda_eq_coe_of_coherent hc hr

/-- The same literal integral ball admits a positive Archimedean separation
constant under domination. No integral basis or finite-generation witness is
required as an extra input. -/
theorem exists_pos_le_archimedeanMaxNorm_of_isDominated
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hd : ξ.IsDominated) (hr : 0 < Module.finrank K E) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ ξ.globalUnitBall,
      x ≠ 0 → c ≤ ξ.archimedeanMaxNorm x := by
  let normalizedDiscrete : DiscreteMeasurableSpace
      (normalizedNumberFieldAdelicStructure K).Ω := inferInstanceAs
    (DiscreteMeasurableSpace {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
  let V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E :=
    { toNormFamily := ξ
      isMeasurable := ξ.isMeasurable_of_discrete
      dual_isMeasurable := ξ.dual.isMeasurable_of_discrete
      isDominated := hd }
  exact V.exists_pos_le_archimedeanMaxNorm_of_globalUnitBall hr

end ArakelovGeometry.NormFamily
