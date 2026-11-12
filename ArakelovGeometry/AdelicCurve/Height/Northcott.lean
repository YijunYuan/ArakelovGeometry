/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
public import ArakelovGeometry.AdelicCurve.Height.Affine

import ArakelovGeometry.AdelicCurve.Height.MinimalPolynomial
import Mathlib.CategoryTheory.Category.Init

/-!
# Northcott finiteness for algebraic elements

Bounded coefficient heights and bounded polynomial degree give finitely many
roots in any extension field. The minimal-polynomial height bound then proves
Chen–Moriwaki, Claim 3.5.6, for every algebraic extension and arbitrary real
height and degree bounds, including inseparable elements.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure

open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (AS : AdelicStructure K)

/-- Northcott finiteness of coefficients gives finitely many roots of bounded-degree
nonzero polynomials in any extension field. -/
theorem finite_roots_of_coeff_height_le [hS : AS.HasNorthcott] (B : ℝ) (D : ℕ) :
    Set.Finite {a : L | ∃ f : K[X], f ≠ 0 ∧ f.natDegree ≤ D ∧
      (∀ j : ℕ, AS.affineHeight (f.coeff j) ≤ B) ∧ Polynomial.aeval a f = 0} := by
  classical
  have hT := AS.hasNorthcott_iff.mp hS B
  have hroots := Polynomial.bUnion_roots_finite (algebraMap K L) D hT
  apply hroots.subset
  rintro a ⟨f, hf, hD, hc, ha⟩
  simp only [Set.mem_iUnion]
  refine ⟨f, ⟨hD, hc⟩, ?_⟩
  change a ∈ (f.map (algebraMap K L)).roots.toFinset
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (Polynomial.map_ne_zero hf), Polynomial.IsRoot,
    Polynomial.eval_map_algebraMap]
  exact ha

variable [Algebra.IsAlgebraic K L]

/-- Bounded affine height and bounded minimal-polynomial degree give finitely many
elements of an algebraic extension. No sign restriction on the height bound is needed. -/
theorem finite_affineHeight_le_minpoly_natDegree_le [hS : AS.HasNorthcott]
    (C : ℝ) (D : ℕ) :
    Set.Finite {a : L | (AS.algebraicExtension L).affineHeight a ≤ C ∧
      (minpoly K a).natDegree ≤ D} := by
  have hroots := AS.finite_roots_of_coeff_height_le (L := L)
    ((D : ℝ) * C + (D - 1 : ℕ) * Real.log 2 * AS.heightArchimedeanConstant) D
  apply hroots.subset
  rintro a ⟨ha, hD⟩
  have hint : IsIntegral K a := Algebra.IsIntegral.isIntegral a
  refine ⟨minpoly K a, minpoly.ne_zero hint, hD, ?_, minpoly.aeval K a⟩
  intro j
  apply (AS.affineHeight_minpoly_coeff_le a j).trans
  apply add_le_add
  · exact mul_le_mul (Nat.cast_le.mpr hD) ha
      ((AS.algebraicExtension L).affineHeight_nonneg a) (Nat.cast_nonneg D)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le_sub_right hD 1))
        (Real.log_nonneg (by norm_num))) AS.heightArchimedeanConstant_nonneg

/-- Chen–Moriwaki, Claim 3.5.6: bounded height and bounded degree give finitely many
algebraic elements. This holds in any algebraic extension, with arbitrary real bounds. -/
theorem finite_affineHeight_le_degree_le [hS : AS.HasNorthcott] (C δ : ℝ) :
    Set.Finite {a : L | (AS.algebraicExtension L).affineHeight a ≤ C ∧
      (Module.finrank K (IntermediateField.adjoin K {a}) : ℝ) ≤ δ} := by
  apply (AS.finite_affineHeight_le_minpoly_natDegree_le (L := L) C ⌊δ⌋₊).subset
  rintro a ⟨ha, hd⟩
  refine ⟨ha, Nat.le_floor ?_⟩
  simpa only [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral a)] using hd

end ArakelovGeometry.AdelicStructure
