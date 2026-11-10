/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.UltrametricCoordinateSplit
import Mathlib.Analysis.Normed.Group.Quotient

/-!
# Actual coordinate quotient norm from maximal minors

The produced residual computes Mathlib's literal quotient seminorm by the
column space, including empty coordinates. No quotient identity is assumed.
-/

noncomputable section

open scoped Matrix

namespace ArakelovGeometry.Matrix

variable {L m n : Type*} [NormedField L] [IsUltrametricDist L]
  [Fintype m] [Fintype n] [DecidableEq n]

/-- An actual maximal minor computes the canonical quotient seminorm on every class. -/
theorem exists_maximal_minor_quotient_norm (A : Matrix m n L)
    (hA : LinearIndependent L A.col) :
    ∃ I : n → m, Function.Injective I ∧ (A.submatrix I id).det ≠ 0 ∧
      ∀ x : m → L,
        ‖(Submodule.Quotient.mk x : (m → L) ⧸ A.mulVecLin.range)‖ =
          ‖x - (A * (A.submatrix I id)⁻¹) *ᵥ (x ∘ I)‖ := by
  obtain ⟨I, hi, hd, hmin⟩ := exists_maximal_minor_quotient_minimum A hA
  refine ⟨I, hi, hd, ?_⟩
  intro x
  let p := x - (A * (A.submatrix I id)⁻¹) *ᵥ (x ∘ I)
  obtain ⟨_, _, hp, a₀, ha₀⟩ := hmin x
  change x + A *ᵥ a₀ = p at ha₀
  have heq : (Submodule.Quotient.mk p : (m → L) ⧸ A.mulVecLin.range) =
      Submodule.Quotient.mk x := by
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨a₀, ?_⟩
    change A *ᵥ a₀ = p - x
    rw [← ha₀]
    abel
  apply le_antisymm
  · rw [← heq]
    exact Submodule.Quotient.norm_mk_le _ p
  · apply QuotientAddGroup.le_norm_iff.mpr
    intro y hy
    have hm : y - x ∈ A.mulVecLin.range := (Submodule.Quotient.eq _).mp hy
    obtain ⟨a, ha⟩ := hm
    change A *ᵥ a = y - x at ha
    have he : x + A *ᵥ a = y := by rw [ha]; abel
    exact he ▸ hp a

end ArakelovGeometry.Matrix
