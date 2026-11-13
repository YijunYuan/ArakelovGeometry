/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Minima.Absolute.Basic

import ArakelovGeometry.AdelicVectorBundle.Minima.Basis
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual basis formula for the last logarithmic minimum

The full-rank threshold characterization yields actual bases, including
the empty basis in rank zero. Taking their smallest vector degree gives
the last logarithmic minimum as an extended-real supremum. No attainment,
properness, or finite upper bound is assumed. The absolute version uses
the prescribed actual ordinary algebraic-closure bundle.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle

universe u w
variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- An attained full-rank threshold supplies an actual basis with the
same degree bound, also when that basis is empty. -/
theorem finrank_le_degreeThresholdSpan_iff_exists_basis (V : AdelicVectorBundle S)
    (t : ℝ) :
    Module.finrank K V ≤ Module.finrank K (V.degreeThresholdSpan t) ↔
      ∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
        ∀ i, t ≤ V.vectorDegree ⟨b i, b.ne_zero i⟩ := by
  classical
  constructor
  · intro ht
    obtain ⟨s, hli, hs⟩ :=
      (V.le_finrank_degreeThresholdSpan_iff (Module.finrank K V) t).mp ht
    let b := basisOfLinearIndependentOfCardEqFinrank'
      (fun i => (s i).val) hli (by simp)
    refine ⟨b, fun i => ?_⟩
    simpa only [b, coe_basisOfLinearIndependentOfCardEqFinrank'] using hs i
  · rintro ⟨b, hb⟩
    exact (V.le_finrank_degreeThresholdSpan_iff (Module.finrank K V) t).mpr
      ⟨fun i => ⟨b i, b.ne_zero i⟩, b.linearIndependent, hb⟩

/-- A real threshold spans the whole space precisely when an actual basis
has at least that vector degree at each index. -/
theorem degreeThresholdSpan_eq_top_iff_exists_basis (V : AdelicVectorBundle S)
    (t : ℝ) :
    V.degreeThresholdSpan t = ⊤ ↔
      ∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
        ∀ i, t ≤ V.vectorDegree ⟨b i, b.ne_zero i⟩ := by
  rw [← V.finrank_le_degreeThresholdSpan_iff_exists_basis t]
  constructor
  · intro ht
    simpa only [finrank_top] using Submodule.finrank_mono ht.ge
  · intro ht
    exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ht)

/-- The last logarithmic minimum is the supremum, over actual rational
bases, of their smallest actual vector degree. The empty infimum is top. -/
theorem minimalLogarithmicMinimum_eq_iSup_basis_iInf_vectorDegree
    (V : AdelicVectorBundle S) :
    V.minimalLogarithmicMinimum =
      ⨆ b : Module.Basis (Fin (Module.finrank K V)) K V,
        ⨅ i, (V.vectorDegree ⟨b i, b.ne_zero i⟩ : EReal) := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    obtain ⟨b, hb⟩ := (V.finrank_le_degreeThresholdSpan_iff_exists_basis t).mp ht
    exact le_iSup_of_le b (le_iInf fun i => EReal.coe_le_coe_iff.mpr (hb i))
  · apply iSup_le
    intro b
    apply EReal.ge_of_forall_gt_iff_ge.mp
    intro t ht
    apply V.coe_le_logarithmicMinimum_of_finrank_le
    apply (V.finrank_le_degreeThresholdSpan_iff_exists_basis t).mpr
    refine ⟨b, fun i => ?_⟩
    exact EReal.coe_le_coe_iff.mp (ht.le.trans (iInf_le _ i))

/-- Absolute last minima have the same basis formula on the actual
ordinary algebraic-closure scalar bundle, with original regularity only. -/
theorem absoluteMinimalLogarithmicMinimum_eq_iSup_basis_iInf_vectorDegree
    (V : AdelicVectorBundle S)
    [hreg : S.HasRegularBase]
    [hN : S.IsArchimedeanNormalized] :
    V.absoluteMinimalLogarithmicMinimum =
      ⨆ b : Module.Basis
        (Fin (Module.finrank (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] V)))
        (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] V),
        ⨅ i, ((V.ordinaryScalarExtension (L := AlgebraicClosure K)).vectorDegree
          ⟨b i, b.ne_zero i⟩ : EReal) := by
  simpa only [minimalLogarithmicMinimum, Module.finrank_baseChange,
    absoluteMinimalLogarithmicMinimum, absoluteLogarithmicMinimum] using
    minimalLogarithmicMinimum_eq_iSup_basis_iInf_vectorDegree
      (V.ordinaryScalarExtension (L := AlgebraicClosure K))

end ArakelovGeometry.AdelicVectorBundle
