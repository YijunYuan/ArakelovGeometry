/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HermitianHNDegree
public import ArakelovGeometry.AdelicVectorBundle.PositiveDegree
public import ArakelovGeometry.AdelicVectorBundle.SemistableFlagDegree

/-!
# Positive degree from actual Hermitian Harder--Narasimhan factors

Bounds use every actual rational subspace and the produced intersection
contractions into actual semistable factors. No maximizing subspace is assumed.
-/

@[expose] public section

open scoped BigOperators

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Every actual subspace degree is bounded by the positive parts of the
actual semistable flag means, weighted by the actual factor ranks. -/
theorem positiveDegree_le_sum_rank_mul_max_slope_of_semistableFlag
    (V : AdelicVectorBundle S E) {n : ℕ} (F : Fin (n + 1) → Submodule K E)
    (hF : Monotone F) (hzero : F 0 = ⊥) (htop : F (Fin.last n) = ⊤)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN)
    (hsemi : ∀ i, (V.flagQuotientOfMeasurableBase F hS i).IsMeanSlopeSemistable hS hN) :
    V.positiveDegree hS hN ≤ ((∑ i : Fin n,
      (Module.finrank K ((F i.succ) ⧸ ((F i.castSucc).comap (F i.succ).subtype)) : ℝ) *
        max ((V.flagQuotientOfMeasurableBase F hS i).slope hS hN) 0 : ℝ) : EReal) := by
  apply V.positiveDegree_le hS hN
  intro U
  apply EReal.coe_le_coe_iff.mpr
  apply (V.degree_restrict_le_sum_intersection_rank_mul_slope_of_semistableFlag
    F hF hzero htop hS hN hV hsemi U).trans
  apply Finset.sum_le_sum
  intro i _
  exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (intersection_rank_increment_le F hF U i)) (le_max_right _ _))

variable (V : AdelicVectorBundle S E)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hV : V.toNormFamily.IsHermitian hN)

/-- Each canonical restriction-then-quotient flag factor is actually
semistable, by the checked completed isometry with the produced image factor. -/
theorem isMeanSlopeSemistable_hermitianHNFlagQuotient
    (i : Fin (V.hermitianHNLength hS hN hV)) :
    (V.flagQuotientOfMeasurableBase (V.hermitianHNFlag hS hN hV) hS i).IsMeanSlopeSemistable
      hS hN := by
  let U := V.hermitianHNTerm hS hN hV i.val
  let W := V.hermitianHNTerm hS hN hV (i.val + 1)
  let g := U.mkQ.comp W.subtype
  have hk : g.ker = U.comap W.subtype := by
    simp only [g, LinearMap.ker_comp, Submodule.ker_mkQ]
  have hs := (V.hermitianHNSubquotient_semistable_slope hS hN hV i).1
  change IsMeanSlopeSemistable
    ((V.restrictOfMeasurableBase W hS).quotientOfMeasurableBase g.ker hS) hS hN at hs
  have ht := congrArg (fun T : Submodule K W ↦
    IsMeanSlopeSemistable
      ((V.restrictOfMeasurableBase W hS).quotientOfMeasurableBase T hS) hS hN) hk
  exact Eq.mp ht hs

/-- The actual factor image rank agrees with the canonical flag quotient
rank under its first-isomorphism equivalence. -/
theorem finrank_hermitianHNFlagQuotient_eq
    (i : Fin (V.hermitianHNLength hS hN hV)) :
    Module.finrank K ((V.hermitianHNFlag hS hN hV i.succ) ⧸
      ((V.hermitianHNFlag hS hN hV i.castSucc).comap
        (V.hermitianHNFlag hS hN hV i.succ).subtype)) =
      Module.finrank K ((V.hermitianHNTerm hS hN hV (i.val + 1)).map
        (V.hermitianHNTerm hS hN hV i.val).mkQ) := by
  let U := V.hermitianHNTerm hS hN hV i.val
  let W := V.hermitianHNTerm hS hN hV (i.val + 1)
  let g := U.mkQ.comp W.subtype
  have hk : g.ker = U.comap W.subtype := by
    simp only [g, LinearMap.ker_comp, Submodule.ker_mkQ]
  have hr : g.range = W.map U.mkQ := by
    simp only [g, LinearMap.range_comp, Submodule.range_subtype]
  change Module.finrank K (W ⧸ U.comap W.subtype) = Module.finrank K (W.map U.mkQ)
  rw [← hk, ← hr]
  exact g.quotKerEquivRange.finrank_eq

/-- Canonical flag quotient means equal actual image-factor means. -/
theorem slope_hermitianHNFlagQuotient_eq
    (i : Fin (V.hermitianHNLength hS hN hV)) :
    (V.flagQuotientOfMeasurableBase (V.hermitianHNFlag hS hN hV) hS i).slope hS hN =
      (V.hermitianHNFactor hS hN hV i).slope hS hN := by
  let U := V.hermitianHNTerm hS hN hV i.val
  let W := V.hermitianHNTerm hS hN hV (i.val + 1)
  let g := U.mkQ.comp W.subtype
  have hk : g.ker = U.comap W.subtype := by
    simp only [g, LinearMap.ker_comp, Submodule.ker_mkQ]
  have hs := (V.hermitianHNSubquotient_semistable_slope hS hN hV i).2
  change ((V.restrictOfMeasurableBase W hS).quotientOfMeasurableBase g.ker hS).slope
    hS hN = _ at hs
  have ht := congrArg (fun T : Submodule K W ↦
    ((V.restrictOfMeasurableBase W hS).quotientOfMeasurableBase T hS).slope hS hN) hk
  exact ht.symm.trans hs

/-- Positive degree is bounded by the positive actual HN factor means
with their actual rank multiplicities, including the empty flag. -/
theorem positiveDegree_le_sum_hermitianHNFactor_rank_mul_max_slope :
    V.positiveDegree hS hN ≤ ((∑ i : Fin (V.hermitianHNLength hS hN hV),
      (Module.finrank K ((V.hermitianHNTerm hS hN hV (i.val + 1)).map
        (V.hermitianHNTerm hS hN hV i.val).mkQ) : ℝ) *
          max ((V.hermitianHNFactor hS hN hV i).slope hS hN) 0 : ℝ) : EReal) := by
  simpa only [V.finrank_hermitianHNFlagQuotient_eq hS hN hV,
    V.slope_hermitianHNFlagQuotient_eq hS hN hV] using
      V.positiveDegree_le_sum_rank_mul_max_slope_of_semistableFlag
        (V.hermitianHNFlag hS hN hV) (V.hermitianHNFlag_strictMono hS hN hV).monotone
        (V.hermitianHNFlag_zero hS hN hV) (V.hermitianHNFlag_last hS hN hV) hS hN hV
        (V.isMeanSlopeSemistable_hermitianHNFlagQuotient hS hN hV)

/-- Actual degree additivity at each produced HN step, expressed using
the actual quotient-image factor rather than a supplied degree identity. -/
theorem degree_restrict_hermitianHNTerm_succ
    (i : Fin (V.hermitianHNLength hS hN hV)) :
    (V.restrictOfMeasurableBase (V.hermitianHNTerm hS hN hV i.val) hS).degree hS hN +
      (V.hermitianHNFactor hS hN hV i).degree hS hN =
        (V.restrictOfMeasurableBase (V.hermitianHNTerm hS hN hV (i.val + 1)) hS).degree
          hS hN := by
  let U := V.hermitianHNTerm hS hN hV i.val
  let W := V.hermitianHNTerm hS hN hV (i.val + 1)
  have hUW : U ≤ W := V.hermitianHNTerm_monotone hS hN hV (Nat.le_succ _)
  have hHW : (V.restrictOfMeasurableBase W hS).toNormFamily.IsHermitian hN := by
    simpa only [restrictOfMeasurableBase_toNormFamily] using hV.restrict W
  have hs := degree_restrict_add_degree_quotient_eq_of_isHermitian
    (V.restrictOfMeasurableBase W hS) (U.comap W.subtype) hS hN hHW
  rw [V.degree_restrict_restrict U W hUW hS hN] at hs
  change (V.restrictOfMeasurableBase U hS).degree hS hN +
    (V.flagQuotientOfMeasurableBase (V.hermitianHNFlag hS hN hV) hS i).degree hS hN =
      (V.restrictOfMeasurableBase W hS).degree hS hN at hs
  rwa [← V.degree_hermitianHNFactor_eq_flagQuotient hS hN hV i] at hs

/-- Every actual HN prefix degree is the sum of the preceding actual
factor degrees. This includes the empty prefix before the first factor. -/
theorem sum_hermitianHNFactor_degree_prefix (m : ℕ)
    (hm : m ≤ V.hermitianHNLength hS hN hV) :
    (∑ i : Fin m,
      (V.hermitianHNFactor hS hN hV ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩).degree hS hN) =
        (V.restrictOfMeasurableBase (V.hermitianHNTerm hS hN hV m) hS).degree hS hN := by
  induction m with
  | zero =>
      rw [Fin.sum_univ_zero, V.hermitianHNTerm_zero hS hN hV]
      exact (degree_eq_zero_of_finrank_eq_zero _ hS hN (finrank_bot K E)).symm
  | succ m ih =>
      have hm' : m ≤ V.hermitianHNLength hS hN hV := by omega
      rw [Fin.sum_univ_castSucc]
      exact (congrArg (fun d : ℝ ↦ d +
        (V.hermitianHNFactor hS hN hV ⟨m, by omega⟩).degree hS hN) (ih hm')).trans
          (V.degree_restrict_hermitianHNTerm_succ hS hN hV ⟨m, by omega⟩)

/-- The produced threshold-zero HN term has degree equal to the sum of
the positive actual factor means, including zero-slope factors harmlessly. -/
theorem degree_restrict_hermitianHNFiltration_zero :
    (V.restrictOfMeasurableBase (V.hermitianHNFiltration hS hN hV 0) hS).degree hS hN =
      ∑ i : Fin (V.hermitianHNLength hS hN hV),
        (Module.finrank K ((V.hermitianHNTerm hS hN hV (i.val + 1)).map
          (V.hermitianHNTerm hS hN hV i.val).mkQ) : ℝ) *
            max ((V.hermitianHNFactor hS hN hV i).slope hS hN) 0 := by
  classical
  let m := V.hermitianHNCut hS hN hV 0
  have hm : m ≤ V.hermitianHNLength hS hN hV := V.hermitianHNCut_le_length hS hN hV 0
  let f := fun i : Fin (V.hermitianHNLength hS hN hV) ↦
    (Module.finrank K ((V.hermitianHNTerm hS hN hV (i.val + 1)).map
      (V.hermitianHNTerm hS hN hV i.val).mkQ) : ℝ) *
        max ((V.hermitianHNFactor hS hN hV i).slope hS hN) 0
  have hs : (∑ i : Fin m,
      (V.hermitianHNFactor hS hN hV ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩).degree hS hN) =
      ∑ i ∈ Finset.univ.filter (fun j : Fin (V.hermitianHNLength hS hN hV) ↦ j.val < m),
        f i := by
    apply Finset.sum_bij
      (fun i _ ↦ (⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩ :
        Fin (V.hermitianHNLength hS hN hV)))
    · intro i _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩
    · intro i _ j _ hij
      exact Fin.ext (congrArg
        (fun k : Fin (V.hermitianHNLength hS hN hV) ↦ k.val) hij)
    · intro j hj
      refine ⟨⟨j.val, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, ?_⟩
      rfl
    · intro i _
      have hp := (V.le_hermitianHNFactor_slope_iff_lt_cut hS hN hV 0
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩).mpr i.isLt
      simp only [f, max_eq_left hp, degree_eq_rank_mul_slope]
  have ht : (∑ i ∈ Finset.univ.filter
      (fun j : Fin (V.hermitianHNLength hS hN hV) ↦ j.val < m), f i) = ∑ i, f i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hni
    have hn : ¬ i.val < m := fun h ↦ hni (Finset.mem_filter.mpr ⟨hi, h⟩)
    have hb : (V.hermitianHNFactor hS hN hV i).slope hS hN < 0 :=
      lt_of_not_ge (fun h ↦ hn ((V.le_hermitianHNFactor_slope_iff_lt_cut hS hN hV 0 i).mp h))
    simp only [f, max_eq_right hb.le, mul_zero]
  exact (V.sum_hermitianHNFactor_degree_prefix hS hN hV m hm).symm.trans (hs.trans ht)

/-- Positive degree is attained by the actual constructed threshold-zero
HN subspace; neither the subspace nor its numerical degree is an input. -/
theorem positiveDegree_eq_degree_restrict_hermitianHNFiltration_zero :
    V.positiveDegree hS hN =
      ((V.restrictOfMeasurableBase (V.hermitianHNFiltration hS hN hV 0) hS).degree
        hS hN : EReal) := by
  apply le_antisymm
  · exact (V.positiveDegree_le_sum_hermitianHNFactor_rank_mul_max_slope hS hN hV).trans_eq
      (congrArg (fun x : ℝ ↦ (x : EReal))
        (V.degree_restrict_hermitianHNFiltration_zero hS hN hV).symm)
  · exact V.degree_restrict_le_positiveDegree hS hN _

/-- Source positive degree is the sum of positive actual HN factor means
with their actual rank multiplicities, with no attainment assumption. -/
theorem positiveDegree_eq_sum_hermitianHNFactor_rank_mul_max_slope :
    V.positiveDegree hS hN = ((∑ i : Fin (V.hermitianHNLength hS hN hV),
      (Module.finrank K ((V.hermitianHNTerm hS hN hV (i.val + 1)).map
        (V.hermitianHNTerm hS hN hV i.val).mkQ) : ℝ) *
          max ((V.hermitianHNFactor hS hN hV i).slope hS hN) 0 : ℝ) : EReal) :=
  (V.positiveDegree_eq_degree_restrict_hermitianHNFiltration_zero hS hN hV).trans
    (congrArg (fun x : ℝ ↦ (x : EReal))
      (V.degree_restrict_hermitianHNFiltration_zero hS hN hV))

end

end ArakelovGeometry.AdelicVectorBundle
