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

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S)
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]
  [hV : V.toNormFamily.IsHermitian]

/-- The actual image factor and canonical quotient of the next restricted
flag term have the same degree under their completed isometry. -/
theorem degree_hermitianHNFactor_eq_flagQuotient
    (i : Fin (V.hermitianHNLength)) :
    (V.hermitianHNFactor i).degree =
      (V.flagQuotientOfNormMeasurability (V.hermitianHNFlag) i).degree := by
  let U := V.hermitianHNTerm i.val
  let W := V.hermitianHNTerm (i.val + 1)
  let g : W →ₗ[K] V ⧸ U := U.mkQ.comp W.subtype
  have hUW : U ≤ W := V.hermitianHNTerm_monotone (Nat.le_succ _)
  have hk : g.ker = U.comap W.subtype := by
    simp only [g, LinearMap.ker_comp, Submodule.ker_mkQ]
  have hr : g.range = W.map U.mkQ := by
    simp only [g, LinearMap.range_comp, Submodule.range_subtype]
  have hd : ((V.restrictOfNormMeasurability W).quotientOfNormMeasurability g.ker).degree
    = ((V.quotientOfNormMeasurability U).restrictOfNormMeasurability
        g.range).degree := by
    apply degree_eq_of_completed_isometry _ _ g.quotKerEquivRange
    intro ω z
    exact (V.toNormFamily.quotient_restrict_range_norm_eq W U hUW ω z).symm
  have hkd := congrArg (fun T : Submodule K W ↦
    ((V.restrictOfNormMeasurability W).quotientOfNormMeasurability T).degree) hk
  have hrd := congrArg (fun T : Submodule K (V ⧸ U) ↦
    ((V.quotientOfNormMeasurability U).restrictOfNormMeasurability T).degree) hr
  exact (hrd.symm.trans hd.symm).trans hkd

/-- The actual constructed positive-rank factors telescope to the original
Hermitian degree; in rank zero this is the genuine empty sum. -/
theorem sum_hermitianHNFactor_degree_eq :
    (∑ i : Fin (V.hermitianHNLength),
      (V.hermitianHNFactor i).degree) = V.degree := by
  calc
    _ = ∑ i : Fin (V.hermitianHNLength),
        (V.flagQuotientOfNormMeasurability (V.hermitianHNFlag) i).degree := by
      apply Finset.sum_congr rfl
      intro i _
      exact V.degree_hermitianHNFactor_eq_flagQuotient i
    _ = V.degree := V.sum_flagQuotient_degree_eq_of_isHermitian
      (V.hermitianHNFlag) (V.hermitianHNFlag_strictMono).monotone
      (V.hermitianHNFlag_zero) (V.hermitianHNFlag_last)

/-- The actual degree is the sum of actual factor means with their actual
rank multiplicities, prior to identifying individual ordered slots. -/
theorem sum_hermitianHNFactor_rank_mul_slope_eq_degree :
    (∑ i : Fin (V.hermitianHNLength),
      (Module.finrank K ((V.hermitianHNTerm (i.val + 1)).map
        (V.hermitianHNTerm i.val).mkQ) : ℝ) *
        (V.hermitianHNFactor i).slope) = V.degree := by
  calc
    _ = ∑ i : Fin (V.hermitianHNLength), (V.hermitianHNFactor i).degree :=
      Finset.sum_congr rfl (fun i _ ↦ (V.hermitianHNFactor i).degree_eq_rank_mul_slope.symm)
    _ = V.degree := V.sum_hermitianHNFactor_degree_eq

end

end ArakelovGeometry.AdelicVectorBundle
