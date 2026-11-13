/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Bidual
public import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.Basic
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Basic

import ArakelovGeometry.AdelicVectorBundle.Degree.Supermodular
import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.HN
import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Norm.Bidual
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.FlagUniqueness
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Functoriality
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Actual bidual balls as approximate spans at a trivial place

Algebraic separation and the genuine completed operator-dual norm identify
bidual balls with intersections of spans of slightly larger original balls.
The original norm is allowed to be non-ultrametric.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u w

variable {K : Type u} [Field K] {E : Type w} [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

namespace NormFamily

open AdelicStructure

open Classical in
/-- A lower bound only away from a rational functional's kernel bounds
its actual completed dual norm, with every completed input tested. -/
theorem trivialSeminorm_dual_le_inv_of_ge_away_kernel
    (ξ : NormFamily (singleTrivialPlace K) E) (ℓ : Module.Dual K E)
    {a : ℝ} (ha : 0 < a) (h : ∀ y, ℓ y ≠ 0 → a ≤ ξ.trivialSeminorm y) :
    ξ.dual.trivialSeminorm ℓ ≤ a⁻¹ := by
  rw [trivialSeminorm_apply]
  apply ξ.dual_norm_le PUnit.unit _ (inv_nonneg.mpr ha.le)
  intro z
  let C := (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
  let q : Seminorm C (C ⊗[K] E) := ξ.norm PUnit.unit
  change C ⊗[K] E at z
  obtain ⟨y, rfl⟩ := (trivialCompletedTensorEquiv K E).symm.surjective z
  change ‖dualBaseChangeEquiv K C E ((1 : C) ⊗ₜ[K] ℓ)
      ((trivialCompletedTensorEquiv K E).symm y)‖ ≤
    a⁻¹ * q ((trivialCompletedTensorEquiv K E).symm y)
  have he : (trivialCompletedTensorEquiv K E).symm y = (1 : C) ⊗ₜ[K] y := by
    apply (trivialCompletedTensorEquiv K E).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (trivialCompletedTensorEquiv_one_tmul K E y).symm
  rw [he, dualBaseChangeEquiv_tmul_apply_tmul K C E, one_mul, one_mul,
    norm_trivialCompletion K, trivialCompletionAlgEquiv_algebraMap]
  by_cases hy : ℓ y = 0
  · rw [hy, map_zero]
    exact mul_nonneg (inv_nonneg.mpr ha.le) (apply_nonneg q _)
  rw [AbsoluteValue.trivial_apply hy]
  have hl := h y hy
  rw [trivialSeminorm_apply] at hl
  change a ≤ q ((1 : C) ⊗ₜ[K] y) at hl
  have hm := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr ha.le)
  simpa only [inv_mul_cancel₀ ha.ne'] using hm

open Classical in
/-- A separating functional gives a genuine bidual lower bound outside
the actual rational span of the original small vectors. -/
theorem le_trivialSeminorm_bidual_of_not_mem_span
    (ξ : NormFamily (singleTrivialPlace K) E) {a : ℝ} (ha : 0 < a) (x : E)
    (hx : x ∉ Submodule.span K {y | ξ.trivialSeminorm y ≤ a}) :
    a ≤ (ξ.dual.dual.pullback (Module.Dual.eval K E)
      (Module.eval_apply_injective K)).trivialSeminorm x := by
  obtain ⟨ℓ, hℓx, hℓ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  have hp : ∀ y, ℓ y ≠ 0 → a ≤ ξ.trivialSeminorm y := by
    intro y hy
    by_contra hn
    have hm : ℓ y ∈ (Submodule.span K {y | ξ.trivialSeminorm y ≤ a}).map ℓ :=
      Submodule.mem_map.mpr ⟨y, Submodule.subset_span (le_of_not_ge hn), rfl⟩
    rw [hℓ, Submodule.mem_bot] at hm
    exact hy hm
  have hd := ξ.trivialSeminorm_dual_le_inv_of_ge_away_kernel ℓ ha hp
  let C := (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
  let q : Seminorm C (C ⊗[K] Module.Dual K E) := ξ.dual.norm PUnit.unit
  let qq : Seminorm C (C ⊗[K] Module.Dual K (Module.Dual K E)) :=
    ξ.dual.dual.norm PUnit.unit
  have he := ξ.dual.norm_dual_tmul_apply_tmul_le PUnit.unit (1 : C) (1 : C)
    (Module.Dual.eval K E x) ℓ
  change ‖(1 : C) * 1 * algebraMap K C (ℓ x)‖ ≤
    qq ((1 : C) ⊗ₜ[K] Module.Dual.eval K E x) * q ((1 : C) ⊗ₜ[K] ℓ) at he
  rw [one_mul, one_mul, norm_trivialCompletion K,
    trivialCompletionAlgEquiv_algebraMap, AbsoluteValue.trivial_apply hℓx] at he
  rw [trivialSeminorm_apply] at hd
  have hb : 1 ≤ qq ((1 : C) ⊗ₜ[K] Module.Dual.eval K E x) * a⁻¹ :=
    he.trans (mul_le_mul_of_nonneg_left hd (apply_nonneg qq _))
  have hl : a ≤ qq ((1 : C) ⊗ₜ[K] Module.Dual.eval K E x) := by
    have hm := (le_div_iff₀ ha).mp (show 1 ≤
      qq ((1 : C) ⊗ₜ[K] Module.Dual.eval K E x) / a from by
        simpa only [div_eq_mul_inv] using hb)
    simpa only [one_mul] using hm
  rw [trivialSeminorm_apply]
  change qq ((Module.Dual.eval K E).baseChange C ((1 : C) ⊗ₜ[K] x)) ≥ a
  rw [LinearMap.baseChange_tmul]
  exact hl

open Classical in
/-- The actual bidual small ball contains the span of the original
small vectors, by genuine bidual contraction and ultrametricity. -/
theorem trivialSeminorm_bidual_le_of_mem_span
    (ξ : NormFamily (singleTrivialPlace K) E) {a : ℝ} (ha : 0 < a) (x : E)
    (hx : x ∈ Submodule.span K {y | ξ.trivialSeminorm y ≤ a}) :
    (ξ.dual.dual.pullback (Module.Dual.eval K E)
      (Module.eval_apply_injective K)).trivialSeminorm x ≤ a := by
  let β := ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)
  have hβ : β.IsUltrametricAtFinitePlaces := ξ.dual.dual_isUltrametricAtFinitePlaces.pullback _ _
  have hs : Submodule.span K {y | ξ.trivialSeminorm y ≤ a} ≤
      β.trivialFiltration (hξ := hβ) (-Real.log a) := by
    apply Submodule.span_le.mpr
    intro y hy
    change β.trivialSeminorm y ≤ Real.exp (-(-Real.log a))
    rw [neg_neg, Real.exp_log ha]
    have he : β.trivialSeminorm y ≤ ξ.trivialSeminorm y := by
      rw [trivialSeminorm_apply, trivialSeminorm_apply]
      exact ξ.dual_dual_norm_eval_le PUnit.unit _
    exact he.trans hy
  have hm := hs hx
  change β.trivialSeminorm x ≤ Real.exp (-(-Real.log a)) at hm
  simpa only [neg_neg, Real.exp_log ha] using hm

open Classical in
/-- Strictly smaller actual bidual radius gives an actual finite linear
combination of original vectors of the chosen radius. -/
theorem mem_span_of_trivialSeminorm_bidual_lt
    (ξ : NormFamily (singleTrivialPlace K) E) {a : ℝ} (ha : 0 < a) (x : E)
    (hx : (ξ.dual.dual.pullback (Module.Dual.eval K E)
      (Module.eval_apply_injective K)).trivialSeminorm x < a) :
    x ∈ Submodule.span K {y | ξ.trivialSeminorm y ≤ a} := by
  by_contra hn
  exact (not_le_of_gt hx) (ξ.le_trivialSeminorm_bidual_of_not_mem_span ha x hn)

open Classical in
/-- The source approximate-span formula uses the actual bidual and
the actual original norm, without original ultrametricity. -/
theorem trivialSeminorm_bidual_le_iff_forall_mem_span
    (ξ : NormFamily (singleTrivialPlace K) E) {a : ℝ} (ha : 0 < a) (x : E) :
    (ξ.dual.dual.pullback (Module.Dual.eval K E)
      (Module.eval_apply_injective K)).trivialSeminorm x ≤ a ↔
      ∀ b : ℝ, a < b → x ∈ Submodule.span K {y | ξ.trivialSeminorm y ≤ b} := by
  constructor
  · intro hx b hab
    exact ξ.mem_span_of_trivialSeminorm_bidual_lt (ha.trans hab) x (hx.trans_lt hab)
  · intro h
    by_contra hn
    obtain ⟨b, hab, hb⟩ := exists_between (lt_of_not_ge hn)
    exact (not_le_of_gt hb) (ξ.trivialSeminorm_bidual_le_of_mem_span (ha.trans hab) x
      (h b hab))

end NormFamily

namespace AdelicVectorBundle

open AdelicStructure

variable (V : AdelicVectorBundle (singleTrivialPlace K))
  [hS : (singleTrivialPlace K).NormMeasurabilityHypotheses]
  [hN : (singleTrivialPlace K).IsArchimedeanNormalized]

open Classical in
/-- Source Proposition4.3.64: the actual general filtration of an arbitrary
original norm is the literal ball filtration of its actual canonical bidual. -/
theorem hnFiltration_eq_bidual_trivialFiltration (t : ℝ) :
    V.hnFiltration t =
      (V.bidualOfNormMeasurability).toNormFamily.trivialFiltration
        (hξ := (V.toNormFamily.dual.dual_isUltrametricAtFinitePlaces.pullback
          (Module.Dual.eval K V) (Module.eval_apply_injective K))) t := by
  let β := V.bidualOfNormMeasurability
  have hβ : β.toNormFamily.IsUltrametricAtFinitePlaces :=
    V.toNormFamily.dual.dual_isUltrametricAtFinitePlaces.pullback
    (Module.Dual.eval K V) (Module.eval_apply_injective K)
  apply le_antisymm
  · by_cases hi : (LinearMap.id : V →ₗ[K] V) = 0
    · intro x _
      have hx : x = 0 := by
        have he := DFunLike.congr_fun hi x
        simpa only [LinearMap.id_apply, LinearMap.zero_apply] using he
      change β.toNormFamily.trivialSeminorm x ≤ Real.exp (-t)
      rw [hx, map_zero]
      exact (Real.exp_pos _).le
    · have hh : V.mapHeight β (LinearMap.id : V →ₗ[K] V) ≤ (0 : EReal) := by
        apply V.mapHeight_le_zero_of_completed_contraction β
        intro ω x
        rw [LinearMap.baseChange_id, LinearMap.id_apply]
        exact V.toNormFamily.dual_dual_norm_eval_le ω x
      have hm := V.map_hnFiltration_le_of_mapHeight_le β
        (LinearMap.id : V →ₗ[K] V) hi 0 hh t
      simp only [Submodule.map_id, sub_zero] at hm
      rw [β.hnFiltration_eq_trivialFiltration (hV := hβ) t] at hm
      exact hm
  · intro x hx
    change x ∈ ⨅ (ε : ℝ) (_ : 0 < ε), V.minimalSlopeSubspaceSum (t - ε)
    rw [Submodule.mem_iInf]
    intro ε
    rw [Submodule.mem_iInf]
    intro hε
    have he : Real.exp (-t) < Real.exp (-(t - ε)) :=
      Real.exp_lt_exp.mpr (by linarith)
    have hqx : β.toNormFamily.trivialSeminorm x ≤ Real.exp (-t) := hx
    have hspan := V.toNormFamily.mem_span_of_trivialSeminorm_bidual_lt
      (Real.exp_pos (-(t - ε))) x (hqx.trans_lt he)
    have hs : Submodule.span K {y | V.toNormFamily.trivialSeminorm y ≤
        Real.exp (-(t - ε))} ≤ V.minimalSlopeSubspaceSum (t - ε) := by
      apply Submodule.span_le.mpr
      intro y hy
      by_cases hyzero : y = 0
      · subst y
        exact Submodule.zero_mem _
      have hpy : 0 < V.toNormFamily.trivialSeminorm y := by
        rw [NormFamily.trivialSeminorm_apply]
        exact V.toNormFamily.norm_rational_pos PUnit.unit hyzero
      have hline : ∀ z, z ≠ 0 →
          (V.restrictOfNormMeasurability (K ∙ y)).toNormFamily.trivialSeminorm z =
            V.toNormFamily.trivialSeminorm y := by
        intro z hz
        exact V.toNormFamily.trivialSeminorm_restrict_span_eq y z hz
      have hr : 0 < Module.finrank K (K ∙ y) := by
        rw [finrank_span_singleton hyzero]
        exact zero_lt_one
      have hl := minimalSlope_eq_neg_log_of_trivialSeminorm_eq_const
        (V.restrictOfNormMeasurability (K ∙ y)) hpy hline hr
      have hlog : Real.log (V.toNormFamily.trivialSeminorm y) ≤ -(t - ε) :=
        Real.exp_le_exp.mp (show Real.exp (Real.log (V.toNormFamily.trivialSeminorm y)) ≤
          Real.exp (-(t - ε)) from by rw [Real.exp_log hpy]; exact hy)
      have hmin : ((t - ε : ℝ) : EReal) ≤
          (V.restrictOfNormMeasurability (K ∙ y)).minimalSlope := by
        rw [hl]
        exact EReal.coe_le_coe (by linarith)
      have hi : K ∙ y ≤ V.minimalSlopeSubspaceSum (t - ε) :=
        le_iSup_of_le (K ∙ y) (le_iSup_of_le
          (Submodule.span_singleton_eq_bot.not.mpr hyzero) (le_iSup_of_le hmin le_rfl))
      exact hi (Submodule.mem_span_singleton_self y)
    exact hs hspan

open Classical in
/-- Bidualization preserves every actual real filtration term, with no
original ultrametricity or positive-rank premise. -/
theorem hnFiltration_bidualOfNormMeasurability (t : ℝ) :
    (V.bidualOfNormMeasurability).hnFiltration t =
      V.hnFiltration t := by
  rw [V.hnFiltration_eq_bidual_trivialFiltration t]
  exact (V.bidualOfNormMeasurability).hnFiltration_eq_trivialFiltration
    (hV := (V.toNormFamily.dual.dual_isUltrametricAtFinitePlaces.pullback
      (Module.Dual.eval K V) (Module.eval_apply_injective K))) t

open Classical in
/-- The actual extended filtration also keeps the source's two infinite
endpoint conventions under bidualization, including rank zero. -/
theorem hnFiltrationExtended_bidualOfNormMeasurability (t : EReal) :
    (V.bidualOfNormMeasurability).hnFiltrationExtended t =
      V.hnFiltrationExtended t := by
  have he : (V.bidualOfNormMeasurability).hnFiltration =
      V.hnFiltration :=
    funext (V.hnFiltration_bidualOfNormMeasurability)
  exact congrArg (fun g : ℝ → Submodule K V ↦
    (EReal.rec ⊤ g ⊥ t : Submodule K V)) he

open Classical in
/-- The literal supremum defining every actual ordered slot is preserved
because the actual filtration rank cuts agree. -/
theorem hnSlope_bidualOfNormMeasurability (j : Fin (Module.finrank K V)) :
    (V.bidualOfNormMeasurability).hnSlope j =
      V.hnSlope j := by
  have he : (V.bidualOfNormMeasurability).hnFiltration =
      V.hnFiltration :=
    funext (V.hnFiltration_bidualOfNormMeasurability)
  exact congrArg (fun g : ℝ → Submodule K V ↦
    sSup {t : ℝ | j.val < Module.finrank K (g t)}) he

open Classical in
/-- The actual HN flag is produced for both bundles and identified by its
true filtration range; no flag or factor semistability is supplied. -/
theorem exists_common_hnFlag_bidualOfNormMeasurability :
    ∃ n : ℕ, ∃ U : Fin (n + 1) → Submodule K V,
      StrictMono U ∧ U 0 = ⊥ ∧ U (Fin.last n) = ⊤ ∧
      (∀ i : Fin n, (V.flagQuotientOfNormMeasurability U i).IsSemistable ∧
        ((V.bidualOfNormMeasurability).flagQuotientOfNormMeasurability U i).IsSemistable) ∧
      StrictAnti (fun i : Fin n ↦ (V.flagQuotientOfNormMeasurability U i).hnMeanSlope) ∧
      StrictAnti (fun i : Fin n ↦
        ((V.bidualOfNormMeasurability).flagQuotientOfNormMeasurability U i).hnMeanSlope
) := by
  let β := V.bidualOfNormMeasurability
  obtain ⟨⟨n, U⟩, ⟨hU, hz, ht, hsemi, hb⟩, _⟩ := V.existsUnique_hnFlag
  obtain ⟨⟨m, F⟩, ⟨hF, hFz, hFt, hFsemi, hFb⟩, _⟩ := β.existsUnique_hnFlag
  have he : β.hnFiltration = V.hnFiltration :=
    funext (V.hnFiltration_bidualOfNormMeasurability)
  have hRange : Set.range U = Set.range F :=
    (V.range_hnFiltration_eq_of_semistableFlag U hU hz ht (hsemi := hsemi) hb).symm.trans
      ((congrArg Set.range he).symm.trans
        (β.range_hnFiltration_eq_of_semistableFlag F hF hFz hFt (hsemi := hFsemi) hFb))
  have hcU := Nat.card_congr (Equiv.ofInjective U hU.injective)
  have hcF := Nat.card_congr (Equiv.ofInjective F hF.injective)
  have hcRange := congrArg (fun Z : Set (Submodule K V) ↦ Nat.card Z) hRange
  simp only [Nat.card_fin] at hcU hcF
  have hmn : m = n := by omega
  subst m
  have hUF : U = F := (hU.range_inj_of_wellFoundedLT hF).mp hRange
  cases hUF
  exact ⟨n, U, hU, hz, ht, fun i ↦ ⟨hsemi i, hFsemi i⟩, hb, hFb⟩

end AdelicVectorBundle

end

end ArakelovGeometry
