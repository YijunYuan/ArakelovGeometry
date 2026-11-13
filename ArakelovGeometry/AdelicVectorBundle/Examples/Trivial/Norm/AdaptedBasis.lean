/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Basic

import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.HN
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Actual orthogonal bases adapted to trivial-place balls

The actual finite ball flag produces an adapted basis by successive
independent-set extension. No adapted basis is supplied as an input.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u w

variable {K : Type u} [Field K] {E : Type w} [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

omit [FiniteDimensional K E] in
private theorem exists_independent_generators_of_monotone_flag
    (n : ℕ) (U : Fin (n + 1) → Submodule K E) (hU : Monotone U) (hz : U 0 = ⊥) :
    ∃ S : Set E, LinearIndepOn K id S ∧ S ⊆ U (Fin.last n) ∧
      Submodule.span K S = U (Fin.last n) ∧
      ∀ j, Submodule.span K (S ∩ (U j : Set E)) = U j := by
  classical
  induction n with
  | zero =>
      refine ⟨∅, linearIndepOn_empty K id, Set.empty_subset _, ?_, ?_⟩
      · simpa only [Submodule.span_empty, Fin.last_zero] using hz.symm
      · intro j
        have hj : j = 0 := by apply Fin.ext; omega
        rw [hj, Set.empty_inter, Submodule.span_empty, hz]
  | succ n ih =>
      let V : Fin (n + 1) → Submodule K E := fun j ↦ U j.castSucc
      have hV : Monotone V := fun i j hij ↦ hU (Fin.castSucc_le_castSucc_iff.mpr hij)
      obtain ⟨S, hS, hsub, hspan, hprev⟩ := ih V hV hz
      have hST : S ⊆ (U (Fin.last (n + 1)) : Set E) := by
        intro x hx
        exact hU (Fin.le_last _) (hsub hx)
      let T := hS.extend hST
      have hT : T ⊆ (U (Fin.last (n + 1)) : Set E) := hS.extend_subset hST
      have hsp : Submodule.span K T = U (Fin.last (n + 1)) := by
        rw [hS.span_extend_eq_span hST, Submodule.span_eq]
      refine ⟨T, hS.linearIndepOn_extend hST, hT, hsp, ?_⟩
      intro j
      rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
      · apply le_antisymm
        · exact Submodule.span_le.mpr (fun _ hx ↦ hx.2)
        · calc
            U i.castSucc = Submodule.span K (S ∩ (U i.castSucc : Set E)) := (hprev i).symm
            _ ≤ Submodule.span K (T ∩ (U i.castSucc : Set E)) :=
              Submodule.span_mono (fun _ hx ↦ ⟨hS.subset_extend hST hx.1, hx.2⟩)
      · have hi : T ∩ (U (Fin.last (n + 1)) : Set E) = T := Set.inter_eq_left.mpr hT
        rw [hi, hsp]

namespace NormFamily

open AdelicStructure

open Classical in
/-- The actual finite ball flag produces a finite basis whose coefficient
supports characterize every actual ball, including the empty basis. -/
theorem exists_basis_adapted_trivialFiltration
    (ξ : NormFamily (singleTrivialPlace K) E) [hξ : ξ.IsUltrametric] :
    ∃ b : Module.Basis (Fin (Module.finrank K E)) K E,
      ∀ t x, x ∈ ξ.trivialFiltration t ↔
        ∀ i, b.repr x i ≠ 0 → b i ∈ ξ.trivialFiltration t := by
  obtain ⟨n, U, _, hU, hz, ht, hrange, _⟩ :=
    ξ.exists_strictMono_flag_and_jumps_trivialFiltration
  obtain ⟨S, hS, _, hspan, hflag⟩ :=
    exists_independent_generators_of_monotone_flag n U hU.monotone hz
  have htop : ⊤ ≤ Submodule.span K (Set.range (fun x : S ↦ (x : E))) := by
    simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hspan, ht] using
      (le_rfl : (⊤ : Submodule K E) ≤ ⊤)
  let b₀ := Module.Basis.mk hS.linearIndependent_restrict htop
  have hr₀ : Set.range b₀ = S := by
    have he : (b₀ : S → E) = Subtype.val := by
      funext i
      exact Module.Basis.mk_apply _ _ i
    rw [he, Subtype.range_coe_subtype, Set.ofPred_mem_eq]
  let b := b₀.reindex (b₀.indexEquiv (Module.finBasis K E))
  have hr : Set.range b = S := (Module.Basis.range_reindex _ _).trans hr₀
  refine ⟨b, ?_⟩
  intro t x
  obtain ⟨j, hj⟩ : ξ.trivialFiltration t ∈ Set.range U := by
    rw [hrange]
    exact ⟨t, rfl⟩
  have him : b '' {i | b i ∈ U j} = S ∩ (U j : Set E) := by
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨hr ▸ Set.mem_range_self i, hi⟩
    · rintro ⟨hy, hyU⟩
      obtain ⟨i, rfl⟩ : y ∈ Set.range b := hr.symm ▸ hy
      exact ⟨i, hyU, rfl⟩
  have hs : Submodule.span K (b '' {i | b i ∈ U j}) = U j := by
    rw [him, hflag j]
  rw [← hj]
  constructor
  · intro hx i hi
    have hm : x ∈ Submodule.span K (b '' {i | b i ∈ U j}) := hs.symm ▸ hx
    exact (b.mem_span_image.mp hm) (Finsupp.mem_support_iff.mpr hi)
  · intro hx
    have hm : x ∈ Submodule.span K (b '' {i | b i ∈ U j}) :=
      b.mem_span_image.mpr (fun i hi ↦ hx i (Finsupp.mem_support_iff.mp hi))
    exact hs ▸ hm

open Classical in
/-- The produced actual adapted basis gives the weighted coordinate
maximum on every original vector and every genuine completed fibre. -/
theorem exists_basis_orthogonal_trivialFiltration
    (ξ : NormFamily (singleTrivialPlace K) E) [hξ : ξ.IsUltrametric] :
    ∃ b : Module.Basis (Fin (Module.finrank K E)) K E,
      (∀ t x, x ∈ ξ.trivialFiltration t ↔
        ∀ i, b.repr x i ≠ 0 → b i ∈ ξ.trivialFiltration t) ∧
      (∀ x, ξ.trivialSeminorm x =
        (((b.repr x).support.sup fun i ↦
          ⟨ξ.trivialSeminorm (b i), apply_nonneg ξ.trivialSeminorm (b i)⟩ : NNReal) : ℝ)) ∧
      ∀ (ω : (singleTrivialPlace K).Ω)
        (z : ((singleTrivialPlace K).ϕ ω).Completion ⊗[K] E),
        ξ.norm ω z =
          (((b.repr (trivialCompletedTensorEquiv K E z)).support.sup fun i ↦
            ⟨ξ.trivialSeminorm (b i), apply_nonneg ξ.trivialSeminorm (b i)⟩ : NNReal) : ℝ) := by
  obtain ⟨b, hb⟩ := ξ.exists_basis_adapted_trivialFiltration
  have hn : ∀ x, ξ.trivialSeminorm x =
      (((b.repr x).support.sup fun i ↦
        ⟨ξ.trivialSeminorm (b i), apply_nonneg ξ.trivialSeminorm (b i)⟩ : NNReal) : ℝ) := by
    intro x
    by_cases hx : x = 0
    · subst x
      rw [map_zero, map_zero, Finsupp.support_zero]
      rfl
    have hp : 0 < ξ.trivialSeminorm x := by
      rw [trivialSeminorm_apply]
      exact ξ.norm_rational_pos PUnit.unit hx
    let f : Fin (Module.finrank K E) → NNReal :=
      fun i ↦ ⟨ξ.trivialSeminorm (b i), apply_nonneg ξ.trivialSeminorm (b i)⟩
    let M : NNReal := (b.repr x).support.sup f
    have hs : ∀ i ∈ (b.repr x).support, ξ.trivialSeminorm (b i) ≤ (M : ℝ) := by
      intro i hi
      exact_mod_cast (Finset.le_sup hi : f i ≤ M)
    have hrepr : b.repr x ≠ 0 := by
      intro hz
      apply hx
      apply b.repr.injective
      simpa only [map_zero] using hz
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hrepr
    have hip : 0 < ξ.trivialSeminorm (b i) := by
      rw [trivialSeminorm_apply]
      exact ξ.norm_rational_pos PUnit.unit (b.ne_zero i)
    have hM : 0 < (M : ℝ) := hip.trans_le (hs i hi)
    apply le_antisymm
    · have hm : x ∈ ξ.trivialFiltration (-Real.log (M : ℝ)) := by
        apply (hb _ x).mpr
        intro j hj
        change ξ.trivialSeminorm (b j) ≤ Real.exp (-(-Real.log (M : ℝ)))
        rw [neg_neg, Real.exp_log hM]
        exact hs j (Finsupp.mem_support_iff.mpr hj)
      change ξ.trivialSeminorm x ≤ Real.exp (-(-Real.log (M : ℝ))) at hm
      simpa only [neg_neg, Real.exp_log hM] using hm
    · have hm : x ∈ ξ.trivialFiltration (-Real.log (ξ.trivialSeminorm x)) := by
        change ξ.trivialSeminorm x ≤ Real.exp (-(-Real.log (ξ.trivialSeminorm x)))
        rw [neg_neg, Real.exp_log hp]
      have hsup : M ≤ ⟨ξ.trivialSeminorm x, hp.le⟩ := by
        apply Finset.sup_le
        intro j hj
        have hjm := (hb _ x).mp hm j (Finsupp.mem_support_iff.mp hj)
        change ξ.trivialSeminorm (b j) ≤
          Real.exp (-(-Real.log (ξ.trivialSeminorm x))) at hjm
        change ξ.trivialSeminorm (b j) ≤ ξ.trivialSeminorm x
        simpa only [neg_neg, Real.exp_log hp] using hjm
      exact_mod_cast hsup
  refine ⟨b, hb, hn, ?_⟩
  intro ω z
  cases ω
  have he := hn (trivialCompletedTensorEquiv K E z)
  change ξ.norm PUnit.unit ((trivialCompletedTensorEquiv K E).symm
      (trivialCompletedTensorEquiv K E z)) = _ at he
  exact (congrArg (ξ.norm PUnit.unit)
    ((trivialCompletedTensorEquiv K E).symm_apply_apply z)).symm.trans he

open Classical in
/-- The genuine finite actual norm range has a positive attained maximum
in positive rank; no maximal-radius bound is supplied as an assumption. -/
theorem exists_nonzero_trivialSeminorm_eq_sSup_range
    (ξ : NormFamily (singleTrivialPlace K) E) [hξ : ξ.IsUltrametric]
    (hr : 0 < Module.finrank K E) :
    ∃ x, x ≠ 0 ∧ ξ.trivialSeminorm x = sSup (Set.range ξ.trivialSeminorm) ∧
      0 < sSup (Set.range ξ.trivialSeminorm) ∧
      ∀ y, ξ.trivialSeminorm y ≤ sSup (Set.range ξ.trivialSeminorm) := by
  have hf := ξ.finite_range_trivialSeminorm
  have hm : sSup (Set.range ξ.trivialSeminorm) ∈ Set.range ξ.trivialSeminorm :=
    (Set.range_nonempty ξ.trivialSeminorm).csSup_mem hf
  let y := Module.finBasis K E ⟨0, hr⟩
  have hy : y ≠ 0 := (Module.finBasis K E).ne_zero _
  have hp : 0 < ξ.trivialSeminorm y := by
    rw [trivialSeminorm_apply]
    exact ξ.norm_rational_pos PUnit.unit hy
  have hR : 0 < sSup (Set.range ξ.trivialSeminorm) :=
    hp.trans_le (le_csSup hf.bddAbove ⟨y, rfl⟩)
  obtain ⟨x, hx⟩ := hm
  have hn : x ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hx
    exact hR.ne' hx.symm
  exact ⟨x, hn, hx, hR, fun y ↦ le_csSup hf.bddAbove ⟨y, rfl⟩⟩

end NormFamily

namespace AdelicVectorBundle

open AdelicStructure

variable (V : AdelicVectorBundle (singleTrivialPlace K))
  [hS : (singleTrivialPlace K).HasMeasurableBase]
  [hN : (singleTrivialPlace K).IsArchimedeanNormalized]

open Classical in
/-- The actual HN ball identification and whole-space cut give the
minimal slope as negative log of the genuine largest nonzero-vector norm. -/
theorem minimalSlope_eq_neg_log_sSup_range_of_isUltrametric
    [hV : V.toNormFamily.IsUltrametric] (hr : 0 < Module.finrank K V) :
    V.minimalSlope = (-Real.log (sSup (Set.range V.toNormFamily.trivialSeminorm)) : ℝ) := by
  obtain ⟨x, _, hx, hR, hmax⟩ :=
    V.toNormFamily.exists_nonzero_trivialSeminorm_eq_sSup_range hr
  have hcut : ∀ t : ℝ, (t : EReal) ≤ V.minimalSlope ↔
      t ≤ -Real.log (sSup (Set.range V.toNormFamily.trivialSeminorm)) := by
    intro t
    rw [← V.generalHNFiltration_eq_top_iff t,
      V.generalHNFiltration_eq_trivialFiltration t]
    have hb : V.toNormFamily.trivialFiltration t = ⊤ ↔
        ∀ y, V.toNormFamily.trivialSeminorm y ≤ Real.exp (-t) := by
      constructor
      · intro he y
        have hy : y ∈ V.toNormFamily.trivialFiltration t := he ▸ Submodule.mem_top
        exact hy
      · intro he
        exact top_unique (fun y _ ↦ he y)
    rw [hb]
    have hm : (∀ y, V.toNormFamily.trivialSeminorm y ≤ Real.exp (-t)) ↔
        sSup (Set.range V.toNormFamily.trivialSeminorm) ≤ Real.exp (-t) := by
      constructor
      · intro he
        rw [← hx]
        exact he x
      · exact fun he y ↦ (hmax y).trans he
    rw [hm]
    conv_lhs => rw [← Real.exp_log hR]
    rw [Real.exp_le_exp]
    constructor <;> intro he <;> linarith
  apply le_antisymm
  · apply EReal.le_of_forall_lt_iff_le.mp
    intro t ht
    have hlt : -Real.log (sSup (Set.range V.toNormFamily.trivialSeminorm)) < t :=
      EReal.coe_lt_coe_iff.mp ht
    apply le_of_lt
    apply lt_of_not_ge
    intro hm
    exact (not_le_of_gt hlt) ((hcut t).mp hm)
  · exact (hcut _).mpr le_rfl

open Classical in
/-- The actual largest-radius formula retains the genuine positive
infinity convention in rank zero, on the extended real line. -/
theorem minimalSlope_eq_if_neg_log_sSup_range_of_isUltrametric
    [hV : V.toNormFamily.IsUltrametric] :
    V.minimalSlope = if Module.finrank K V = 0 then (⊤ : EReal) else
      ((-Real.log (sSup (Set.range V.toNormFamily.trivialSeminorm)) : ℝ) : EReal) := by
  by_cases hr : Module.finrank K V = 0
  · rw [ite_eq_left hr]
    exact V.minimalSlope_eq_top_of_finrank_eq_zero hr
  · rw [ite_eq_right hr]
    exact V.minimalSlope_eq_neg_log_sSup_range_of_isUltrametric (Nat.pos_of_ne_zero hr)

end AdelicVectorBundle

end

end ArakelovGeometry
