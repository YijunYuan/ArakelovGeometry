/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.AbsoluteLogarithmicMinimaFinite
public import ArakelovGeometry.AdelicVectorBundle.LogarithmicMinimaFiltrationFinite

/-!
# Actual absolute minima cut bases, ranks and finite jumps

The absolute cut is the existing ordinary minima filtration on the genuine
canonical closure bundle. Its jump set reuses the ordinary jump set of that
bundle. Original finite minima supply its real interpretation without any
additional regularity hypothesis on the algebraic-closure curve.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
universe u v w
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} {E : Type w}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

variable (V : AdelicVectorBundle S E)
  (hreg : S.HasCommonCountableDenseSubfield ∨
    (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
    (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)

/-- The canonical ordinary jump set of the genuine closure bundle.
Its real-minimum interpretation is produced from original hypotheses below. -/
abbrev absoluteLogarithmicMinimaJumpSet : Finset ℝ :=
  (V.ordinaryScalarExtension (L := AlgebraicClosure K) hreg hN).logarithmicMinimaJumpSet

/-- The actual closure jump set is the finite image of precisely the original
valid indices under the actual absolute minimum's real-value projection. -/
theorem absoluteLogarithmicMinimaJumpSet_eq_image :
    V.absoluteLogarithmicMinimaJumpSet hreg hN =
      (Finset.Icc 1 (Module.finrank K E)).image
        (fun i => (V.absoluteLogarithmicMinimum hreg hN i).toReal) := by
  classical
  unfold absoluteLogarithmicMinimaJumpSet logarithmicMinimaJumpSet
  rw [Module.finrank_baseChange]
  rfl

/-- Actual absolute filtration ranks count valid original absolute minimum
indices; the ordinary actual rank theorem supplies the whole statement. -/
theorem finrank_absoluteMinimaFiltration_eq_card (t : ℝ) :
    Module.finrank (AlgebraicClosure K)
        ((V.ordinaryScalarExtension (L := AlgebraicClosure K) hreg hN).minimaFiltration t) =
      ((Finset.Icc 1 (Module.finrank K E)).filter
        (fun i => (t : EReal) ≤ V.absoluteLogarithmicMinimum hreg hN i)).card := by
  classical
  rw [finrank_minimaFiltration_eq_card
    (V.ordinaryScalarExtension (L := AlgebraicClosure K) hreg hN) t,
    Module.finrank_baseChange]
  rfl

/-- Every actual absolute cut has a true high-degree subtype basis at each
relaxation, with no regularity premise on the closure curve. -/
theorem exists_basis_absoluteMinimaFiltration_degree_ge (t : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    let W := V.ordinaryScalarExtension (L := AlgebraicClosure K) hreg hN
    ∃ b : Module.Basis (Fin (Module.finrank (AlgebraicClosure K) (W.minimaFiltration t)))
        (AlgebraicClosure K) (W.minimaFiltration t),
      ∀ j, t - ε ≤ W.vectorDegree
        ⟨(b j : AlgebraicClosure K ⊗[K] E), fun h => b.ne_zero j (Subtype.ext h)⟩ :=
  exists_basis_minimaFiltration_degree_ge
    (V.ordinaryScalarExtension (L := AlgebraicClosure K) hreg hN) t hε

variable [S.IsProper]

/-- The actual closure jump set consists precisely of the produced real
absolute minima at valid original indices. No closure regularity is assumed. -/
theorem mem_absoluteLogarithmicMinimaJumpSet_iff (c : ℝ) :
    c ∈ V.absoluteLogarithmicMinimaJumpSet hreg hN ↔
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ Module.finrank K E ∧
        V.absoluteLogarithmicMinimum hreg hN i = (c : EReal) := by
  classical
  rw [V.absoluteLogarithmicMinimaJumpSet_eq_image hreg hN, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, hc⟩
    obtain ⟨hi, hr⟩ := Finset.mem_Icc.mp hi
    have hm := EReal.coe_toReal (V.absoluteLogarithmicMinimum_ne_top hreg hN hi)
      (V.absoluteLogarithmicMinimum_ne_bot hreg hN hr)
    exact ⟨i, hi, hr, hm.symm.trans (congrArg (fun x : ℝ => (x : EReal)) hc)⟩
  · rintro ⟨i, hi, hr, hc⟩
    exact ⟨i, Finset.mem_Icc.mpr ⟨hi, hr⟩, by rw [hc, EReal.toReal_coe]⟩

/-- Jump-free intervals give equality of the actual closure filtration cuts,
with all real-minimum bounds produced from original-base hypotheses. -/
theorem absoluteMinimaFiltration_eq_of_disjoint_jump_interval {a b : ℝ} (hab : a ≤ b)
    (hJ : Disjoint (V.absoluteLogarithmicMinimaJumpSet hreg hN : Set ℝ) (Set.Ico a b)) :
    (V.ordinaryScalarExtension (L := AlgebraicClosure K) hreg hN).minimaFiltration a =
      (V.ordinaryScalarExtension (L := AlgebraicClosure K) hreg hN).minimaFiltration b := by
  apply minimaFiltration_eq_of_minimum_profile
  intro i hi hr
  have hir : i ≤ Module.finrank K E := by
    simpa only [Module.finrank_baseChange] using hr
  obtain ⟨c, hc⟩ := V.exists_absoluteLogarithmicMinimum_eq_coe hreg hN hi hir
  change (a : EReal) ≤ V.absoluteLogarithmicMinimum hreg hN i ↔
    (b : EReal) ≤ V.absoluteLogarithmicMinimum hreg hN i
  rw [hc]
  simp only [EReal.coe_le_coe_iff]
  constructor
  · intro hac
    by_contra hbc
    have hcJ := (V.mem_absoluteLogarithmicMinimaJumpSet_iff hreg hN c).mpr
      ⟨i, hi, hir, hc⟩
    exact Set.disjoint_left.mp hJ hcJ ⟨hac, lt_of_not_ge hbc⟩
  · exact hab.trans

end ArakelovGeometry.AdelicVectorBundle
