/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.Basic
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Basic
import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.Hermitian
import ArakelovGeometry.AdelicVectorBundle.Degree.Isometry
import ArakelovGeometry.AdelicVectorBundle.Subquotient.Quotient.Restriction
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Degrees of the actual Hermitian Harder--Narasimhan factors

The constructed factor is an actual restriction inside an ambient quotient.
The completed quotient-restriction isometry identifies its degree with the
canonical flag quotient degree. The accepted finite Hermitian flag identity
then sums the actual factors to the original degree, with the empty flag
retained. No supplied flag or numerical degree identity is used.
-/

@[expose] public section

open scoped BigOperators

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S E)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hV : V.toNormFamily.IsHermitian hN)

/-- The actual image factor and canonical quotient of the next restricted
flag term have the same degree under their completed isometry. -/
theorem degree_hermitianHNFactor_eq_flagQuotient
    (i : Fin (V.hermitianHNLength hS hN hV)) :
    (V.hermitianHNFactor hS hN hV i).degree hS hN =
      (V.flagQuotientOfMeasurableBase (V.hermitianHNFlag hS hN hV) hS i).degree hS hN := by
  let U := V.hermitianHNTerm hS hN hV i.val
  let W := V.hermitianHNTerm hS hN hV (i.val + 1)
  let g : W →ₗ[K] E ⧸ U := U.mkQ.comp W.subtype
  have hUW : U ≤ W := V.hermitianHNTerm_monotone hS hN hV (Nat.le_succ _)
  have hk : g.ker = U.comap W.subtype := by
    simp only [g, LinearMap.ker_comp, Submodule.ker_mkQ]
  have hr : g.range = W.map U.mkQ := by
    simp only [g, LinearMap.range_comp, Submodule.range_subtype]
  have hd : ((V.restrictOfMeasurableBase W hS).quotientOfMeasurableBase g.ker hS).degree
      hS hN = ((V.quotientOfMeasurableBase U hS).restrictOfMeasurableBase
        g.range hS).degree hS hN := by
    apply degree_eq_of_completed_isometry _ _ g.quotKerEquivRange hS hN
    intro ω z
    exact (V.toNormFamily.quotient_restrict_range_norm_eq W U hUW ω z).symm
  have hkd := congrArg (fun T : Submodule K W ↦
    ((V.restrictOfMeasurableBase W hS).quotientOfMeasurableBase T hS).degree hS hN) hk
  have hrd := congrArg (fun T : Submodule K (E ⧸ U) ↦
    ((V.quotientOfMeasurableBase U hS).restrictOfMeasurableBase T hS).degree hS hN) hr
  exact (hrd.symm.trans hd.symm).trans hkd

/-- The actual constructed positive-rank factors telescope to the original
Hermitian degree; in rank zero this is the genuine empty sum. -/
theorem sum_hermitianHNFactor_degree_eq :
    (∑ i : Fin (V.hermitianHNLength hS hN hV),
      (V.hermitianHNFactor hS hN hV i).degree hS hN) = V.degree hS hN := by
  calc
    _ = ∑ i : Fin (V.hermitianHNLength hS hN hV),
        (V.flagQuotientOfMeasurableBase (V.hermitianHNFlag hS hN hV) hS i).degree hS hN := by
      apply Finset.sum_congr rfl
      intro i _
      exact V.degree_hermitianHNFactor_eq_flagQuotient hS hN hV i
    _ = V.degree hS hN := V.sum_flagQuotient_degree_eq_of_isHermitian
      (V.hermitianHNFlag hS hN hV) (V.hermitianHNFlag_strictMono hS hN hV).monotone
      (V.hermitianHNFlag_zero hS hN hV) (V.hermitianHNFlag_last hS hN hV) hS hN hV

/-- The actual degree is the sum of actual factor means with their actual
rank multiplicities, prior to identifying individual ordered slots. -/
theorem sum_hermitianHNFactor_rank_mul_slope_eq_degree :
    (∑ i : Fin (V.hermitianHNLength hS hN hV),
      (Module.finrank K ((V.hermitianHNTerm hS hN hV (i.val + 1)).map
        (V.hermitianHNTerm hS hN hV i.val).mkQ) : ℝ) *
        (V.hermitianHNFactor hS hN hV i).slope hS hN) = V.degree hS hN := by
  simpa only [← degree_eq_rank_mul_slope] using V.sum_hermitianHNFactor_degree_eq hS hN hV

end

end ArakelovGeometry.AdelicVectorBundle
