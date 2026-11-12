/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Countable
public import ArakelovGeometry.AdelicVectorBundle.Minima.Basic

import ArakelovGeometry.AdelicVectorBundle.Minima.Basis
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Ordinary minima of genuine restricted adelic bundles

The accepted measurable-base constructor supplies actual restriction primal and
dual regularity. Restriction preserves actual vector degrees. An ordinary
minimum is the supremum of last minima over genuine restricted rank-index
subspaces. No threshold attainment or finite-value minimum is assumed.
The source indices are positive and at most rank; natural-index zero and
above-rank cases use the explicit auxiliary conventions. These producers do
not assert the whole source 4.3.70 intersection-of-sums formula.
-/

@[expose] public section

noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle

universe u v w
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Actual vector degrees agree under the genuine completed restriction norm. -/
theorem vectorDegree_restrictOfMeasurableBase (V : AdelicVectorBundle S E)
    (U : Submodule K E)
    [hS : S.HasMeasurableBase]
    (s : {x : U // x ≠ 0}) :
    (V.restrictOfMeasurableBase U).vectorDegree s =
      V.vectorDegree ⟨s.val.val, by
        intro h
        exact s.property (Subtype.ext h)⟩ := by
  rfl

/-- Independent high-degree vectors in a genuine restriction remain such
vectors in the ambient bundle, hence bound each ordinary minimum. -/
theorem logarithmicMinimum_restrictOfMeasurableBase_le (V : AdelicVectorBundle S E)
    (U : Submodule K E)
    [hS : S.HasMeasurableBase] (i : ℕ) :
    (V.restrictOfMeasurableBase U).logarithmicMinimum i ≤ V.logarithmicMinimum i := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  obtain ⟨s, hli, hs⟩ :=
    ((V.restrictOfMeasurableBase U).le_finrank_degreeThresholdSpan_iff i t).mp ht
  let g : Fin i → {x : E // x ≠ 0} := fun j => ⟨(s j).val.val, by
    intro h
    exact (s j).property (Subtype.ext h)⟩
  apply V.coe_le_logarithmicMinimum_of_linearIndependent g
  · exact hli.map' U.subtype (Submodule.ker_subtype U)
  · intro j
    simpa only [vectorDegree_restrictOfMeasurableBase] using hs j

/-- Each ordinary minimum is the supremum of last minima of actual restricted
rank-index subspaces. Natural index zero and above-rank cases are auxiliary. -/
theorem logarithmicMinimum_eq_iSup_restrict_minimalLogarithmicMinimum
    (V : AdelicVectorBundle S E)
    [hS : S.HasMeasurableBase] (i : ℕ) :
    V.logarithmicMinimum i =
      ⨆ (U : Submodule K E) (_ : Module.finrank K U = i),
        (V.restrictOfMeasurableBase U).minimalLogarithmicMinimum := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    obtain ⟨s, hli, hs⟩ := (V.le_finrank_degreeThresholdSpan_iff i t).mp ht
    let U := Submodule.span K (Set.range fun j => (s j).val)
    have hr : Module.finrank K U = i := by simpa [U] using finrank_span_eq_card hli
    let g : Fin i → U := fun j => ⟨(s j).val, Submodule.subset_span ⟨j, rfl⟩⟩
    have hliU : LinearIndependent K g := linearIndependent_span hli
    let f : Fin i → {x : U // x ≠ 0} := fun j => ⟨g j, by
      intro h
      exact (s j).property (congrArg Subtype.val h)⟩
    have hf : ∀ j, t ≤ (V.restrictOfMeasurableBase U).vectorDegree (f j) := by
      intro j
      rw [V.vectorDegree_restrictOfMeasurableBase U]
      exact hs j
    have hb := (V.restrictOfMeasurableBase U).coe_le_logarithmicMinimum_of_linearIndependent
      f hliU hf
    have hbmin : (t : EReal) ≤ (V.restrictOfMeasurableBase U).minimalLogarithmicMinimum := by
      simpa [minimalLogarithmicMinimum, hr] using hb
    exact hbmin.trans (le_iSup_of_le U (le_iSup_of_le hr le_rfl))
  · apply iSup_le
    intro U
    apply iSup_le
    intro hU
    simpa [minimalLogarithmicMinimum, hU] using
      V.logarithmicMinimum_restrictOfMeasurableBase_le U i

/-- The first ordinary minimum is the supremum over genuine restricted lines. -/
theorem maximalLogarithmicMinimum_eq_iSup_restrict_lines (V : AdelicVectorBundle S E)
    [hS : S.HasMeasurableBase] :
    V.maximalLogarithmicMinimum =
      ⨆ (U : Submodule K E) (_ : Module.finrank K U = 1),
        (V.restrictOfMeasurableBase U).minimalLogarithmicMinimum :=
  V.logarithmicMinimum_eq_iSup_restrict_minimalLogarithmicMinimum 1

/-- The actual full restriction has the ambient last minimum, including rank zero. -/
theorem minimalLogarithmicMinimum_restrict_top (V : AdelicVectorBundle S E)
    [hS : S.HasMeasurableBase] :
    (V.restrictOfMeasurableBase ⊤).minimalLogarithmicMinimum =
      V.minimalLogarithmicMinimum := by
  apply le_antisymm
  · change (V.restrictOfMeasurableBase ⊤).logarithmicMinimum
      (Module.finrank K (⊤ : Submodule K E)) ≤ V.logarithmicMinimum (Module.finrank K E)
    rw [finrank_top]
    exact V.logarithmicMinimum_restrictOfMeasurableBase_le ⊤ (Module.finrank K E)
  · change V.logarithmicMinimum (Module.finrank K E) ≤
      (V.restrictOfMeasurableBase ⊤).minimalLogarithmicMinimum
    rw [V.logarithmicMinimum_eq_iSup_restrict_minimalLogarithmicMinimum]
    apply iSup_le
    intro U
    apply iSup_le
    intro hU
    have htop : U = ⊤ := Submodule.eq_top_of_finrank_eq hU
    rw [htop]

end ArakelovGeometry.AdelicVectorBundle
