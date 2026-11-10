/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Defs
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import ArakelovGeometry.AdelicCurve.Extension.RootBounds
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Uniform envelopes for arbitrary extending-place choices

The coefficient estimate in Chen–Moriwaki, Proposition 4.1.15, is uniform
in every extension of each absolute value. No measurable choice is needed.
-/

@[expose] public section

open MeasureTheory

namespace ArakelovGeometry.AdelicStructure

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] (S : AdelicStructure K)

/-- A single algebraic coefficient has a nonnegative integrable exponential
bound simultaneously at every extension of every base place, including zero. -/
theorem exists_algebraic_absValue_exp_bound (a : L) :
    ∃ A : S.Ω → ℝ, Integrable A S.v ∧ (∀ ω, 0 ≤ A ω) ∧
      ∀ (ω : S.Ω) (w : AbsoluteValue L ℝ), w.under K = S.ϕ ω →
        w a ≤ Real.exp (A ω) := by
  let p := minpoly K a
  have hp : p.Monic := minpoly.monic (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  let A : S.Ω → ℝ := fun ω =>
    Real.log (p.natDegree : ℝ) * S.κ ω + S.coefficientLogBound p ω
  refine ⟨A, S.integrable_logarithmicRootBound p,
    S.logarithmicRootBound_nonneg p hp, ?_⟩
  intro ω w hw
  by_cases ha : a = 0
  · simpa only [ha, map_zero] using (Real.exp_pos (A ω)).le
  · exact (Real.log_le_iff_le_exp (w.pos ha)).mp
      (S.log_apply_le_rootBound p hp a (minpoly.aeval K a) ha ω w hw)

/-- Finitely many algebraic coefficients share one nonnegative integrable
bound at all extending places. The index type may be empty. -/
theorem exists_algebraic_coefficients_exp_bound {ι : Type*} [Finite ι] (a : ι → L) :
    ∃ A : S.Ω → ℝ, Integrable A S.v ∧ (∀ ω, 0 ≤ A ω) ∧
      ∀ (ω : S.Ω) (w : AbsoluteValue L ℝ), w.under K = S.ϕ ω →
        ∀ i, w (a i) ≤ Real.exp (A ω) := by
  classical
  let := Fintype.ofFinite ι
  choose A hA hA0 hbound using fun i => S.exists_algebraic_absValue_exp_bound (a i)
  refine ⟨fun ω => ∑ i, A i ω, integrable_finsetSum _ (fun i _ => hA i),
    fun ω => Finset.sum_nonneg (fun i _ => hA0 i ω), ?_⟩
  intro ω w hw i
  exact (hbound i ω w hw).trans (Real.exp_le_exp.mpr
    (Finset.single_le_sum (fun j _ => hA0 j ω) (Finset.mem_univ i)))

/-- Both signs of every nonzero algebraic logarithm have one integrable
bound, uniformly in all extending places. -/
theorem exists_algebraic_abs_log_bound (a : L) :
    ∃ A : S.Ω → ℝ, Integrable A S.v ∧ (∀ ω, 0 ≤ A ω) ∧
      ∀ (ω : S.Ω) (w : AbsoluteValue L ℝ), w.under K = S.ϕ ω →
        |Real.log (w a)| ≤ A ω := by
  obtain ⟨A, hA, hA0, ha⟩ := S.exists_algebraic_absValue_exp_bound a
  obtain ⟨B, hB, hB0, hb⟩ := S.exists_algebraic_absValue_exp_bound a⁻¹
  refine ⟨A + B, hA.add hB, fun ω => add_nonneg (hA0 ω) (hB0 ω), ?_⟩
  intro ω w hw
  by_cases ha0 : a = 0
  · simpa only [ha0, map_zero, Real.log_zero, abs_zero, Pi.add_apply] using
      add_nonneg (hA0 ω) (hB0 ω)
  · apply abs_le.mpr
    have hu := (Real.log_le_iff_le_exp (w.pos ha0)).mpr (ha ω w hw)
    have hl := (Real.log_le_iff_le_exp (w.pos (inv_ne_zero ha0))).mpr (hb ω w hw)
    rw [map_inv₀, Real.log_inv] at hl
    change -(A ω + B ω) ≤ Real.log (w a) ∧ Real.log (w a) ≤ A ω + B ω
    constructor <;> linarith [hA0 ω, hB0 ω]

end ArakelovGeometry.AdelicStructure
