/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Minima.Basic
import ArakelovGeometry.AdelicVectorBundle.Minima.Basis
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Rank of the actual completed logarithmic minima filtration

Finite-dimensional descending threshold spans stabilize at each left-completed
cut. Their actual rank is characterized by the supremum logarithmic minima,
including unbounded and empty cuts, without assuming threshold attainment.
The source indices are `1 ≤ i ≤ finrank K E`; the statements at natural index
zero or above rank are auxiliary extensions. Counts use only source indices.
-/

@[expose] public section

noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle

universe u w
variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Each actual left-completed cut is an actual relaxed threshold span.
This is subspace stabilization, not attainment of degrees at the cut itself. -/
theorem exists_minimaFiltration_eq_degreeThresholdSpan (V : AdelicVectorBundle S)
    (t : ℝ) : ∃ ε : ℝ, 0 < ε ∧ V.minimaFiltration t = V.degreeThresholdSpan (t - ε) := by
  classical
  let : Nonempty {ε : ℝ // 0 < ε} := ⟨⟨1, zero_lt_one⟩⟩
  let f : {ε : ℝ // 0 < ε} → ℕ := fun ε =>
    Module.finrank K (V.degreeThresholdSpan (t - ε.val))
  let ε₀ := Function.argmin f
  refine ⟨ε₀.val, ε₀.property,
    le_antisymm (V.minimaFiltration_le_degreeThresholdSpan t ε₀.property) ?_⟩
  apply le_iInf
  intro ε
  apply le_iInf
  intro hε
  rcases le_total ε₀.val ε with hle | hle
  · exact V.degreeThresholdSpan_antitone (sub_le_sub_left hle t)
  · have hspan := V.degreeThresholdSpan_antitone (sub_le_sub_left hle t)
    have hr : Module.finrank K (V.degreeThresholdSpan (t - ε₀.val)) ≤
        Module.finrank K (V.degreeThresholdSpan (t - ε)) :=
      Function.argmin_le f ⟨ε, hε⟩
    exact (Submodule.eq_of_le_of_finrank_le hspan hr).symm.le

/-- Actual completed filtration rank is characterized by the extended supremum
minimum. The natural-index endpoint extensions are also covered. -/
theorem le_finrank_minimaFiltration_iff (V : AdelicVectorBundle S) (i : ℕ) (t : ℝ) :
    i ≤ Module.finrank K (V.minimaFiltration t) ↔ (t : EReal) ≤ V.logarithmicMinimum i := by
  constructor
  · intro hi
    apply EReal.ge_of_forall_gt_iff_ge.mp
    intro u hu
    have hut : u < t := EReal.coe_lt_coe_iff.mp hu
    have hε : 0 < t - u := sub_pos.mpr hut
    have hr := hi.trans (Submodule.finrank_mono
      (V.minimaFiltration_le_degreeThresholdSpan t hε))
    have hb := V.coe_le_logarithmicMinimum_of_finrank_le hr
    convert hb using 1
    congr 1
    ring
  · intro ht
    obtain ⟨ε, hε, hΦ⟩ := V.exists_minimaFiltration_eq_degreeThresholdSpan t
    rw [hΦ]
    have hlt : ((t - ε : ℝ) : EReal) < V.logarithmicMinimum i :=
      (EReal.coe_lt_coe_iff.mpr (sub_lt_self t hε)).trans_le ht
    rw [logarithmicMinimum, lt_iSup_iff] at hlt
    obtain ⟨u, hu⟩ := hlt
    obtain ⟨hri, hu⟩ := lt_iSup_iff.mp hu
    exact hri.trans (Submodule.finrank_mono (V.degreeThresholdSpan_antitone
      (EReal.coe_lt_coe_iff.mp hu).le))

/-- The actual completed rank is detected by independent high-degree families
at every relaxed threshold. These families may depend on the relaxation. -/
theorem le_finrank_minimaFiltration_iff_forall_exists_linearIndependent
    (V : AdelicVectorBundle S) (i : ℕ) (t : ℝ) :
    i ≤ Module.finrank K (V.minimaFiltration t) ↔
      ∀ ε : ℝ, 0 < ε → ∃ s : Fin i → {x : V // x ≠ 0},
        LinearIndependent K (fun j => (s j).val) ∧
        ∀ j, t - ε ≤ V.vectorDegree (s j) := by
  constructor
  · intro hi ε hε
    exact (V.le_finrank_degreeThresholdSpan_iff i (t - ε)).mp
      (hi.trans (Submodule.finrank_mono (V.minimaFiltration_le_degreeThresholdSpan t hε)))
  · intro h
    obtain ⟨ε, hε, hΦ⟩ := V.exists_minimaFiltration_eq_degreeThresholdSpan t
    rw [hΦ]
    exact (V.le_finrank_degreeThresholdSpan_iff i (t - ε)).mpr (h ε hε)

/-- The actual filtration rank counts only valid source minimum indices. -/
theorem finrank_minimaFiltration_eq_card (V : AdelicVectorBundle S) (t : ℝ) :
    Module.finrank K (V.minimaFiltration t) =
      ((Finset.Icc 1 (Module.finrank K V)).filter
        (fun i => (t : EReal) ≤ V.logarithmicMinimum i)).card := by
  classical
  have hset : (Finset.Icc 1 (Module.finrank K V)).filter
      (fun i => (t : EReal) ≤ V.logarithmicMinimum i) =
      Finset.Icc 1 (Module.finrank K (V.minimaFiltration t)) := by
    ext i
    rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc,
      ← V.le_finrank_minimaFiltration_iff i t]
    constructor
    · rintro ⟨⟨hi, _⟩, hΦ⟩
      exact ⟨hi, hΦ⟩
    · rintro ⟨hi, hΦ⟩
      exact ⟨⟨hi, hΦ.trans (Submodule.finrank_le _)⟩, hΦ⟩
  rw [hset]
  simp

/-- A real filtration cut is zero exactly when it is above the first minimum.
This also holds for the rank-zero first-minimum convention. -/
theorem minimaFiltration_eq_bot_iff (V : AdelicVectorBundle S) (t : ℝ) :
    V.minimaFiltration t = ⊥ ↔ V.logarithmicMinimum 1 < (t : EReal) := by
  constructor
  · intro hΦ
    apply lt_of_not_ge
    intro ht
    have hr := (V.le_finrank_minimaFiltration_iff 1 t).mpr ht
    rw [hΦ, finrank_bot] at hr
    omega
  · intro hmin
    apply Submodule.finrank_eq_zero.mp
    have hn : ¬ 1 ≤ Module.finrank K (V.minimaFiltration t) := by
      intro hr
      exact (not_le_of_gt hmin) ((V.le_finrank_minimaFiltration_iff 1 t).mp hr)
    omega

/-- A real filtration cut is the whole space exactly when it is at most the
last minimum, including the rank-zero last-minimum convention. -/
theorem minimaFiltration_eq_top_iff (V : AdelicVectorBundle S) (t : ℝ) :
    V.minimaFiltration t = ⊤ ↔
      (t : EReal) ≤ V.logarithmicMinimum (Module.finrank K V) := by
  constructor
  · intro hΦ
    apply (V.le_finrank_minimaFiltration_iff (Module.finrank K V) t).mp
    rw [hΦ, finrank_top]
  · intro ht
    have hr := (V.le_finrank_minimaFiltration_iff (Module.finrank K V) t).mpr ht
    exact Submodule.eq_top_of_finrank_eq (Nat.le_antisymm (Submodule.finrank_le _) hr)

/-- Source page 4.3.69's completed-filtration supremum formula, with auxiliary
natural-index endpoints also covered. -/
theorem logarithmicMinimum_eq_iSup_finrank_minimaFiltration (V : AdelicVectorBundle S)
    (i : ℕ) :
    V.logarithmicMinimum i =
      ⨆ (t : ℝ) (_ : i ≤ Module.finrank K (V.minimaFiltration t)), (t : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    have hΦ := ht.trans (Submodule.finrank_mono (V.degreeThresholdSpan_le_minimaFiltration t))
    exact le_iSup_of_le t (le_iSup_of_le hΦ le_rfl)
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    exact (V.le_finrank_minimaFiltration_iff i t).mp ht

end ArakelovGeometry.AdelicVectorBundle
