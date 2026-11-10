/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.ExternalResults.AbsoluteValueFinite
public import Mathlib.Topology.Compactness.Compact

/-!
# Compact spaces of extending absolute values

For an algebraic extension, evaluation embeds the extending absolute values as a closed
subset of a product of finite subsets of the real line.
-/

@[expose] public section

namespace AbsoluteValue
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The equations and inequalities defining extending absolute values form a closed locus. -/
theorem isClosed_range_extensions (v : AbsoluteValue K ℝ) :
    IsClosed (Set.range (fun w : {w : AbsoluteValue L ℝ // w.under K = v} ↦
      (w.val : L → ℝ))) := by
  let S : Set (L → ℝ) := {f | f 0 = 0 ∧ f 1 = 1 ∧
    (∀ a, 0 ≤ f a) ∧ (∀ a b, f (a * b) = f a * f b) ∧
    (∀ a b, f (a + b) ≤ f a + f b) ∧ ∀ a : K, f (algebraMap K L a) = v a}
  have hS : Set.range (fun w : {w : AbsoluteValue L ℝ // w.under K = v} ↦
      (w.val : L → ℝ)) = S := by
    ext f
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨map_zero _, map_one _, w.val.nonneg, map_mul _, w.val.add_le, ?_⟩
      intro a
      exact congrArg (fun v : AbsoluteValue K ℝ ↦ v a) w.property
    · rintro ⟨h0, h1, hnonneg, hmul, hadd, hrestrict⟩
      let w : AbsoluteValue L ℝ := {
        toFun := f
        map_mul' := hmul
        nonneg' := hnonneg
        eq_zero' := fun a ↦ by
          constructor
          · intro ha
            by_contra hane
            have hm := hmul a a⁻¹
            rw [mul_inv_cancel₀ hane, h1, ha, zero_mul] at hm
            exact one_ne_zero hm
          · rintro rfl
            exact h0
        add_le' := hadd }
      have hw : w.under K = v := by
        ext a
        exact hrestrict a
      exact ⟨⟨w, hw⟩, rfl⟩
  rw [hS]
  have hnonneg : IsClosed {f : L → ℝ | ∀ a, 0 ≤ f a} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a ↦ isClosed_le continuous_const (continuous_apply a)
  have hmul : IsClosed {f : L → ℝ | ∀ a b, f (a * b) = f a * f b} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a ↦ isClosed_iInter fun b ↦
      isClosed_eq (continuous_apply (a * b)) ((continuous_apply a).mul (continuous_apply b))
  have hadd : IsClosed {f : L → ℝ | ∀ a b, f (a + b) ≤ f a + f b} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a ↦ isClosed_iInter fun b ↦
      isClosed_le (continuous_apply (a + b)) ((continuous_apply a).add (continuous_apply b))
  have hrestrict : IsClosed {f : L → ℝ | ∀ a : K, f (algebraMap K L a) = v a} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun a ↦ isClosed_eq (continuous_apply _) continuous_const
  exact (isClosed_eq (continuous_apply 0) continuous_const).inter
    ((isClosed_eq (continuous_apply 1) continuous_const).inter
      (hnonneg.inter (hmul.inter (hadd.inter hrestrict))))

/-- An algebraic element has only finitely many values among the extensions of an absolute value. -/
theorem finite_range_extensions_apply [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ) (a : L) :
    (Set.range (fun w : {w : AbsoluteValue L ℝ // w.under K = v} ↦ w.val a)).Finite := by
  let E := IntermediateField.adjoin K ({a} : Set L)
  let b : E := ⟨a, IntermediateField.subset_adjoin K ({a} : Set L) (Set.mem_singleton a)⟩
  have : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional
      ((Algebra.IsAlgebraic.isAlgebraic (R := K) a).isIntegral)
  have hfin := finite_extensions (L := E) v
  refine (hfin.image fun u ↦ u b).subset ?_
  rintro _ ⟨w, rfl⟩
  refine ⟨w.val.under E, ?_, rfl⟩
  exact w.property

/-- Extending absolute values form a compact set for pointwise convergence on an algebraic field. -/
theorem isCompact_range_extensions [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ) :
    IsCompact (Set.range (fun w : {w : AbsoluteValue L ℝ // w.under K = v} ↦
      (w.val : L → ℝ))) := by
  have hcomp := isCompact_pi_infinite fun a : L ↦ (finite_range_extensions_apply v a).isCompact
  apply hcomp.of_isClosed_subset (isClosed_range_extensions v)
  rintro _ ⟨w, rfl⟩ a
  exact ⟨w, rfl⟩
end AbsoluteValue
