/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.LogarithmicMinima

/-!
# Independent vectors in ordinary logarithmic threshold spans

The dimension of the actual degree threshold span is characterized by independent
nonzero rational vectors of at least that degree. The source range is
`1 ≤ i ≤ finrank K E`; the index-zero empty family is an auxiliary extension.
Attainment at a threshold is distinguished from the supremum defining a minimum.
-/

noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle

universe u v w
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Source Definition 4.3.69's attained-threshold characterization. The source
indices are positive and at most rank; `i = 0` also allows the empty family. -/
theorem le_finrank_degreeThresholdSpan_iff (V : AdelicVectorBundle S E)
    (i : ℕ) (t : ℝ) :
    i ≤ Module.finrank K (V.degreeThresholdSpan t) ↔
      ∃ s : Fin i → {x : E // x ≠ 0},
        LinearIndependent K (fun j => (s j).val) ∧
        ∀ j, t ≤ V.vectorDegree (s j) := by
  classical
  constructor
  · intro hi
    obtain ⟨f, hf, _, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq K
      {x : E | ∃ hx : x ≠ 0, t ≤ V.vectorDegree ⟨x, hx⟩}
    choose hn hd using fun j : Fin i => hf (Fin.castLE hi j)
    refine ⟨fun j => ⟨f (Fin.castLE hi j), hn j⟩, ?_, hd⟩
    exact hli.comp (Fin.castLE hi) (Fin.castLE_injective hi)
  · rintro ⟨s, hli, hs⟩
    have hspan : Submodule.span K (Set.range fun j => (s j).val) ≤
        V.degreeThresholdSpan t := by
      apply Submodule.span_le.mpr
      rintro x ⟨j, rfl⟩
      exact V.mem_degreeThresholdSpan (s j) (hs j)
    have hcard : Module.finrank K (Submodule.span K (Set.range fun j => (s j).val)) = i := by
      simpa using finrank_span_eq_card hli
    rw [← hcard]
    exact Submodule.finrank_mono hspan

/-- An attained independent high-degree family gives a lower bound on the
supremum minimum. The converse would require a separate attainment argument. -/
theorem coe_le_logarithmicMinimum_of_linearIndependent (V : AdelicVectorBundle S E)
    {i : ℕ} {t : ℝ} (s : Fin i → {x : E // x ≠ 0})
    (hli : LinearIndependent K (fun j => (s j).val))
    (hs : ∀ j, t ≤ V.vectorDegree (s j)) :
    (t : EReal) ≤ V.logarithmicMinimum i :=
  V.coe_le_logarithmicMinimum_of_finrank_le
    ((V.le_finrank_degreeThresholdSpan_iff i t).mpr ⟨s, hli, hs⟩)

/-- Auxiliary index-zero convention: the empty high-degree family always exists. -/
theorem exists_linearIndependent_degree_ge_zero (V : AdelicVectorBundle S E) (t : ℝ) :
    ∃ s : Fin 0 → {x : E // x ≠ 0},
      LinearIndependent K (fun j => (s j).val) ∧ ∀ j, t ≤ V.vectorDegree (s j) :=
  (V.le_finrank_degreeThresholdSpan_iff 0 t).mp (Nat.zero_le _)

/-- In rank zero, only the auxiliary empty family can meet an attained threshold. -/
theorem exists_linearIndependent_degree_ge_iff_eq_zero_of_finrank_eq_zero
    (V : AdelicVectorBundle S E) (hr : Module.finrank K E = 0) (i : ℕ) (t : ℝ) :
    (∃ s : Fin i → {x : E // x ≠ 0},
      LinearIndependent K (fun j => (s j).val) ∧ ∀ j, t ≤ V.vectorDegree (s j)) ↔ i = 0 := by
  rw [← V.le_finrank_degreeThresholdSpan_iff i t,
    V.degreeThresholdSpan_eq_bot_of_finrank_eq_zero hr t]
  simp

end ArakelovGeometry.AdelicVectorBundle
