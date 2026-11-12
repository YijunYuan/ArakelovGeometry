/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.AbsoluteInvariants.RegularBase

import ArakelovGeometry.AdelicVectorBundle.Minima.Basis
import ArakelovGeometry.AdelicVectorBundle.Minima.FiltrationRank
import Mathlib.CategoryTheory.Category.Init

/-!
# Native scalar restrictions and the actual minima filtration

The actual native restriction constructor produces adelicity from original
regularity. It does not require regularity of the scalar place space. These
bundles realize the source subspace sum/intersection formula on the actual
ordinary algebraic scalar bundle, including its algebraic-closure specialization.
No properness, finite minimum, or threshold attainment is assumed.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S E)
  [hreg : S.HasRegularBase]
  [hN : S.IsArchimedeanNormalized]

/-- The actual native restriction retains the ambient scalar vector degree. -/
theorem vectorDegree_scalarExtensionRestrictionOfRegularBase
    (A : Submodule L (L ⊗[K] E)) (s : {x : A // x ≠ 0}) :
    (V.scalarExtensionRestrictionOfRegularBase A).vectorDegree s =
      (V.ordinaryScalarExtension (L := L)).vectorDegree
        ⟨s.val.val, by intro h; exact s.property (Subtype.ext h)⟩ := rfl

/-- Included native high-degree vectors generate an ambient threshold subspace. -/
theorem degreeThresholdSpan_nativeRestriction_map_le
    (A : Submodule L (L ⊗[K] E)) (t : ℝ) :
    ((V.scalarExtensionRestrictionOfRegularBase A).degreeThresholdSpan t).map
      A.subtype ≤ (V.ordinaryScalarExtension (L := L)).degreeThresholdSpan t := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro x ⟨hx, ht⟩
  change (x : L ⊗[K] E) ∈
    (V.ordinaryScalarExtension (L := L)).degreeThresholdSpan t
  have hne : (x : L ⊗[K] E) ≠ 0 := by
    intro h
    exact hx (Subtype.ext h)
  apply (V.ordinaryScalarExtension (L := L)).mem_degreeThresholdSpan ⟨x.val, hne⟩
  rw [← V.vectorDegree_scalarExtensionRestrictionOfRegularBase A ⟨x, hx⟩]
  exact ht

/-- Included actual native completed cuts lie in the ambient scalar cut. -/
theorem minimaFiltration_nativeRestriction_map_le
    (A : Submodule L (L ⊗[K] E)) (t : ℝ) :
    ((V.scalarExtensionRestrictionOfRegularBase A).minimaFiltration t).map
      A.subtype ≤ (V.ordinaryScalarExtension (L := L)).minimaFiltration t := by
  apply le_iInf
  intro ε
  apply le_iInf
  intro hε
  exact (Submodule.map_mono
    (minimaFiltration_le_degreeThresholdSpan
      (V.scalarExtensionRestrictionOfRegularBase A) t hε)).trans
        (V.degreeThresholdSpan_nativeRestriction_map_le A (t - ε))

omit [IsAlgClosed L] in
omit hreg hN in
private theorem nativeMinimaFiltrationThresholdRefinement
    (W : AdelicVectorBundle (S.algebraicExtension L) (L ⊗[K] E))
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ W.minimaFiltration t = W.degreeThresholdSpan (t - δ) := by
  obtain ⟨δ₀, hδ₀, hΦ⟩ := W.exists_minimaFiltration_eq_degreeThresholdSpan t
  have hδ : 0 < min δ₀ ε := lt_min hδ₀ hε
  refine ⟨min δ₀ ε, hδ, min_le_right _ _,
    le_antisymm (W.minimaFiltration_le_degreeThresholdSpan t hδ) ?_⟩
  exact (W.degreeThresholdSpan_antitone
    (sub_le_sub_left (min_le_left δ₀ ε) t)).trans hΦ.symm.le

/-- Original regularity supplies a genuine native cut restriction whose
actual last minimum is at least the cut, including a zero cut. -/
theorem coe_le_minimalLogarithmicMinimum_nativeRestriction_minimaFiltration (t : ℝ) :
    (t : EReal) ≤
      minimalLogarithmicMinimum (V.scalarExtensionRestrictionOfRegularBase
        ((V.ordinaryScalarExtension (L := L)).minimaFiltration t)) := by
  classical
  let W := V.ordinaryScalarExtension (L := L)
  let A := W.minimaFiltration t
  let R := V.scalarExtensionRestrictionOfRegularBase A
  apply (R.le_finrank_minimaFiltration_iff (Module.finrank L A) t).mp
  apply (R.le_finrank_minimaFiltration_iff_forall_exists_linearIndependent
    (Module.finrank L A) t).mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε, hΦ⟩ := nativeMinimaFiltrationThresholdRefinement W t hε
  have hr : Module.finrank L A ≤ Module.finrank L (W.degreeThresholdSpan (t - δ)) :=
    (congrArg (fun F : Submodule L (L ⊗[K] E) => Module.finrank L F) hΦ).le
  obtain ⟨s, hli, hs⟩ :=
    (W.le_finrank_degreeThresholdSpan_iff (Module.finrank L A) (t - δ)).mp hr
  let g : Fin (Module.finrank L A) → A := fun j => ⟨(s j).val, by
    change (s j).val ∈ W.minimaFiltration t
    rw [hΦ]
    exact W.mem_degreeThresholdSpan (s j) (hs j)⟩
  have hlig : LinearIndependent L g := LinearIndependent.of_comp A.subtype hli
  let f : Fin (Module.finrank L A) → {x : A // x ≠ 0} := fun j => ⟨g j, by
    intro h
    exact (s j).property (congrArg Subtype.val h)⟩
  refine ⟨f, hlig, ?_⟩
  intro j
  rw [V.vectorDegree_scalarExtensionRestrictionOfRegularBase]
  exact (sub_le_sub_left hδε t).trans (hs j)

/-- The exact scalar cut is the sum of actual native nonzero subspaces with
native restricted last minimum at least the cut. -/
theorem minimaFiltration_eq_iSup_nativeRestriction_minimum (t : ℝ) :
    (V.ordinaryScalarExtension (L := L)).minimaFiltration t =
      ⨆ (A : Submodule L (L ⊗[K] E)) (_ : A ≠ ⊥)
        (_ : (t : EReal) ≤
          (V.scalarExtensionRestrictionOfRegularBase A).minimalLogarithmicMinimum),
          A := by
  classical
  apply le_antisymm
  · by_cases hΦ : (V.ordinaryScalarExtension (L := L)).minimaFiltration t = ⊥
    · rw [hΦ]
      exact bot_le
    · exact le_iSup_of_le ((V.ordinaryScalarExtension (L := L)).minimaFiltration t)
        (le_iSup_of_le hΦ (le_iSup_of_le
          (V.coe_le_minimalLogarithmicMinimum_nativeRestriction_minimaFiltration t)
          le_rfl))
  · apply iSup_le
    intro A
    apply iSup_le
    intro _
    apply iSup_le
    intro hmin
    have htop := (minimaFiltration_eq_top_iff
      (V.scalarExtensionRestrictionOfRegularBase A) t).mpr hmin
    have hm := V.minimaFiltration_nativeRestriction_map_le A t
    rw [htop, Submodule.map_subtype_top] at hm
    exact hm

/-- The literal source 4.3.70 intersection of subspace sums holds for the
actual scalar bundle with native restrictions under original regularity only. -/
theorem minimaFiltration_eq_iInf_iSup_nativeRestriction_minimum (t : ℝ) :
    (V.ordinaryScalarExtension (L := L)).minimaFiltration t =
      ⨅ (ε : ℝ) (_ : 0 < ε),
        ⨆ (A : Submodule L (L ⊗[K] E)) (_ : A ≠ ⊥)
          (_ : ((t - ε : ℝ) : EReal) ≤
            (V.scalarExtensionRestrictionOfRegularBase A).minimalLogarithmicMinimum),
          A := by
  simp_rw [← V.minimaFiltration_eq_iSup_nativeRestriction_minimum]
  let W := V.ordinaryScalarExtension (L := L)
  apply le_antisymm
  · apply le_iInf
    intro ε
    apply le_iInf
    intro hε
    exact W.minimaFiltration_antitone (sub_le_self t hε.le)
  · rw [W.minimaFiltration_eq_iInf_lt t]
    apply le_iInf
    intro u
    apply le_iInf
    intro hu
    have hε : 0 < t - u := sub_pos.mpr hu
    have h : (⨅ (ε : ℝ) (_ : 0 < ε), W.minimaFiltration (t - ε)) ≤
        W.minimaFiltration (t - (t - u)) :=
      iInf_le_of_le (t - u) (iInf_le_of_le hε le_rfl)
    convert h using 1
    congr 1
    ring

end ArakelovGeometry.AdelicVectorBundle
