/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Height.Affine
import Mathlib.Algebra.Polynomial.Roots

/-!
# Polynomial-root finiteness from the Northcott property

Bounded coefficient heights and bounded polynomial degree give finitely many
roots in any extension field. This is the finite-set step in the proof of
Chen–Moriwaki, Claim 3.5.6; the minimal-polynomial height bound is a separate
prerequisite to applying it to all algebraic elements of bounded height.
-/

namespace ArakelovGeometry.AdelicStructure

open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (AS : AdelicStructure K)

/-- Northcott finiteness of coefficients gives finitely many roots of bounded-degree
nonzero polynomials in any extension field. -/
theorem finite_roots_of_coeff_height_le (hS : AS.HasNorthcott) (B : ℝ) (D : ℕ) :
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

end ArakelovGeometry.AdelicStructure
