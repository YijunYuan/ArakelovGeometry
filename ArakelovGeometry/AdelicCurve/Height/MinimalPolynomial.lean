/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
public import ArakelovGeometry.AdelicCurve.Height.Polynomial
import ArakelovGeometry.AdelicCurve.Height.Extension
import Mathlib.CategoryTheory.Category.Init

/-!
# Heights of minimal polynomials

Two roots of the same irreducible polynomial have the same affine height,
including in the inseparable case. Factoring the minimal polynomial then
bounds its height and the heights of its coefficients by the degree and the
affine height of the original element. The error uses the finite integrated
archimedean exponent.

Reference: Chen–Moriwaki, the proof of Claim 3.5.6.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure

open Polynomial

variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- Extending the base field leaves the height of a polynomial unchanged. -/
theorem polynomialLogHeight_map_algebraicExtension (p : K[X]) :
    (AS.algebraicExtension L).polynomialLogHeight (p.map (algebraMap K L)) =
      AS.polynomialLogHeight p := by
  rw [(AS.algebraicExtension L).polynomialLogHeight_eq_logHeight _
    (le_of_eq (natDegree_map _))]
  simp only [coeff_map]
  exact AS.logHeight_algebraicExtension L _

/-- A root of an element's minimal polynomial has the same height as that element.
The two embeddings of the simple extension suffice, without a normal closure. -/
theorem affineLogHeight_eq_of_aeval_minpoly_eq_zero
    {E : Type*} [Field E] [Algebra K E] [Algebra.IsAlgebraic K E] {a : E} {b : L}
    (hb : Polynomial.aeval b (minpoly K a) = 0) :
    (AS.algebraicExtension L).affineLogHeight b =
      (AS.algebraicExtension E).affineLogHeight a := by
  have ha : IsIntegral K a := Algebra.IsIntegral.isIntegral a
  let := IntermediateField.adjoin.finiteDimensional ha
  let r : {b : L // b ∈ (minpoly K a).aroots L} :=
    ⟨b, mem_aroots.mpr ⟨minpoly.ne_zero ha, hb⟩⟩
  let i := (IntermediateField.algHomAdjoinIntegralEquiv K ha).symm r
  have hi : i (IntermediateField.AdjoinSimple.gen K a) = b :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen K ha r
  rw [← hi, AS.affineLogHeight_comp_finiteEmbedding i]
  exact (AS.affineLogHeight_comp_finiteEmbedding (IntermediateField.adjoin K {a}).val
    (IntermediateField.AdjoinSimple.gen K a)).symm

/-- Roots of a monic irreducible polynomial have equal affine heights, with no
separability assumption. -/
theorem affineLogHeight_eq_of_irreducible {p : K[X]} (hp : Irreducible p)
    (hm : p.Monic) {a b : L} (ha : Polynomial.aeval a p = 0)
    (hb : Polynomial.aeval b p = 0) :
    (AS.algebraicExtension L).affineLogHeight b =
      (AS.algebraicExtension L).affineLogHeight a := by
  apply AS.affineLogHeight_eq_of_aeval_minpoly_eq_zero
  rwa [← minpoly.eq_of_irreducible_of_monic hp ha hm]

/-- The height bound for the minimal polynomial, counting all roots with multiplicity. -/
theorem polynomialLogHeight_minpoly_le (a : L) :
    AS.polynomialLogHeight (minpoly K a) ≤
      (minpoly K a).natDegree * (AS.algebraicExtension L).affineLogHeight a +
        ((minpoly K a).natDegree - 1 : ℕ) * Real.log 2 *
          AS.heightArchimedeanConstant := by
  classical
  have ha : IsIntegral K a := Algebra.IsIntegral.isIntegral a
  let p := (minpoly K a).map (algebraMap K (AlgebraicClosure K))
  have hp : p.Monic := (minpoly.monic ha).map _
  have hd : p.roots.card = (minpoly K a).natDegree :=
    (IsAlgClosed.splits p).natDegree_eq_card_roots.symm.trans (natDegree_map _)
  have hl : p.roots.toList ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    rw [Multiset.length_toList, hd] at hlen
    exact (minpoly.natDegree_pos ha).ne' hlen
  have hprod : (p.roots.toList.map
      (fun b ↦ (X - C b : (AlgebraicClosure K)[X]))).prod = p := by
    rw [Multiset.prod_map_toList]
    exact prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp
      (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  have heq (b : AlgebraicClosure K) (hb : b ∈ p.roots.toList) :
      (AS.algebraicExtension (AlgebraicClosure K)).affineLogHeight b =
        (AS.algebraicExtension L).affineLogHeight a := by
    apply AS.affineLogHeight_eq_of_aeval_minpoly_eq_zero
    have hb' : b ∈ (minpoly K a).aroots (AlgebraicClosure K) := by
      simpa only [Multiset.mem_toList] using hb
    exact (mem_aroots.mp hb').2
  have hsum :
      (p.roots.toList.map (AS.algebraicExtension (AlgebraicClosure K)).affineLogHeight).sum =
      (minpoly K a).natDegree * (AS.algebraicExtension L).affineLogHeight a := by
    calc
      _ = (p.roots.toList.map
          (Function.const (AlgebraicClosure K)
            ((AS.algebraicExtension L).affineLogHeight a))).sum :=
        congrArg List.sum (List.map_congr_left heq)
      _ = _ := by
        rw [List.map_const, List.sum_replicate, nsmul_eq_mul, Multiset.length_toList, hd]
  have h := AS.polynomialLogHeight_prod_X_sub_C_le_algebraicExtension
    (AlgebraicClosure K) p.roots.toList hl
  rw [hprod, hsum, Multiset.length_toList, hd] at h
  exact (AS.polynomialLogHeight_map_algebraicExtension
    (L := AlgebraicClosure K) (minpoly K a)).ge.trans h

/-- Each minimal-polynomial coefficient has the same uniform bound. -/
theorem affineLogHeight_minpoly_coeff_le (a : L) (j : ℕ) :
    AS.affineLogHeight ((minpoly K a).coeff j) ≤
      (minpoly K a).natDegree * (AS.algebraicExtension L).affineLogHeight a +
        ((minpoly K a).natDegree - 1 : ℕ) * Real.log 2 *
          AS.heightArchimedeanConstant :=
  (AS.affineLogHeight_coeff_le_polynomialLogHeight
    (minpoly.monic (Algebra.IsIntegral.isIntegral a)) j).trans
      (AS.polynomialLogHeight_minpoly_le a)

/-- The minimal-polynomial bound in terms of the degree of the simple field extension. -/
theorem polynomialLogHeight_minpoly_le_finrank (a : L) :
    AS.polynomialLogHeight (minpoly K a) ≤
      Module.finrank K (IntermediateField.adjoin K {a}) *
          (AS.algebraicExtension L).affineLogHeight a +
        (Module.finrank K (IntermediateField.adjoin K {a}) - 1 : ℕ) * Real.log 2 *
          AS.heightArchimedeanConstant := by
  simpa only [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral a)] using
    AS.polynomialLogHeight_minpoly_le a

end ArakelovGeometry.AdelicStructure
