/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.LinearMapBound
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Approximate extension of ultrametric functionals

The finite-dimensional extension argument uses near-minimal representatives in
a quotient norm. It applies to every complete normed field, including the
trivially valued case, without a spherical-completeness hypothesis.
-/

@[expose] public section

namespace ArakelovGeometry

variable {L V : Type*} [NormedField L] [CompleteSpace L]
  [NormedAddCommGroup V] [NormedSpace L V] [FiniteDimensional L V]

/-- Every nonzero quotient class has representatives with norm within any
prescribed factor greater than one of its quotient norm. -/
theorem exists_quotient_representative_norm_lt (W : Submodule L V) {v : V}
    (hv : v ∉ W) {A : ℝ} (hA : 1 < A) :
    ∃ v' : V, W.mkQ v' = W.mkQ v ∧ ‖v'‖ < A * ‖W.mkQ v‖ := by
  have : IsClosed (W : Set V) := finiteDimensional_submodule_isClosed W
  have hq : 0 < ‖W.mkQ v‖ := norm_pos_iff.mpr (by simpa using hv)
  obtain ⟨v', hv', hn⟩ := Submodule.Quotient.norm_mk_lt (W.mkQ v)
    (mul_pos (sub_pos.mpr hA) hq)
  refine ⟨v', hv', ?_⟩
  nlinarith

omit [CompleteSpace L] [FiniteDimensional L V] in
/-- Killing a near-minimal quotient representative loses at most its
approximation factor in the projection onto the original subspace. -/
theorem norm_le_mul_norm_add_smul_of_quotient_bound [IsUltrametricDist V]
    (W : Submodule L V) {v : V} {A : ℝ} (hA : 1 ≤ A)
    (hv : ‖v‖ ≤ A * ‖W.mkQ v‖) (w : W) (a : L) :
    ‖(w : V)‖ ≤ A * ‖(w : V) + a • v‖ := by
  have hq : ‖a‖ * ‖W.mkQ v‖ ≤ ‖(w : V) + a • v‖ := by
    have hw : (Submodule.Quotient.mk (w : V) : V ⧸ W) = 0 :=
      (Submodule.Quotient.mk_eq_zero W).mpr w.property
    simpa [map_add, map_smul, norm_smul, hw] using
      Submodule.Quotient.norm_mk_le W ((w : V) + a • v)
  have hav : ‖a • v‖ ≤ A * ‖(w : V) + a • v‖ := by
    calc
      ‖a • v‖ = ‖a‖ * ‖v‖ := norm_smul _ _
      _ ≤ ‖a‖ * (A * ‖W.mkQ v‖) := mul_le_mul_of_nonneg_left hv (norm_nonneg a)
      _ = A * (‖a‖ * ‖W.mkQ v‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hq (zero_le_one.trans hA)
  have hx : ‖(w : V) + a • v‖ ≤ A * ‖(w : V) + a • v‖ :=
    le_mul_of_one_le_left (norm_nonneg _) hA
  calc
    ‖(w : V)‖ = ‖((w : V) + a • v) + -(a • v)‖ := by simp
    _ ≤ max ‖(w : V) + a • v‖ ‖-(a • v)‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ _ := max_le hx (by simpa only [norm_neg] using hav)

/-- A functional on a proper subspace extends to a strictly larger subspace
with any prescribed norm loss greater than one. -/
theorem exists_ultrametric_extension_larger [IsUltrametricDist V]
    (W : Submodule L V) (hW : W ≠ ⊤) (f : W →ₗ[L] L) {A : ℝ} (hA : 1 < A) :
    ∃ (U : Submodule L V) (hWU : W < U) (g : U →ₗ[L] L),
      g.comp (Submodule.inclusion hWU.le) = f ∧
        linearMapOperatorSeminorm g ≤ A * linearMapOperatorSeminorm f := by
  obtain ⟨v, hv⟩ := SetLike.exists_notMem_of_ne_top W hW
  obtain ⟨u, hu, hunorm⟩ := exists_quotient_representative_norm_lt W hv hA
  have huW : u ∉ W := by
    intro huW
    apply hv
    apply (Submodule.Quotient.mk_eq_zero W).mp
    change W.mkQ v = 0
    rw [← hu]
    exact (Submodule.Quotient.mk_eq_zero W).mpr huW
  have hubound : ‖u‖ ≤ A * ‖W.mkQ u‖ := by simpa only [hu] using hunorm.le
  let U := W ⊔ Submodule.span L {u}
  have huU : u ∈ U := (show Submodule.span L {u} ≤ U from le_sup_right)
    (Submodule.subset_span (Set.mem_singleton u))
  have hWU : W < U := lt_of_le_of_ne le_sup_left (fun heq ↦ huW (heq.symm ▸ huU))
  obtain ⟨g, hgf, hgu⟩ := f.exists_extend_of_notMem huW (0 : L)
  refine ⟨U, hWU, g.domRestrict U, ?_, ?_⟩
  · ext w
    exact LinearMap.congr_fun hgf w
  · apply linearMapOperatorSeminorm_le _
      (mul_nonneg (zero_lt_one.trans hA).le (apply_nonneg _ _))
    intro x
    obtain ⟨w, hw, t, ht, hwt⟩ := Submodule.mem_sup.mp x.property
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp ht
    have hgw : g w = f ⟨w, hw⟩ := LinearMap.congr_fun hgf ⟨w, hw⟩
    change ‖g (x : V)‖ ≤ A * linearMapOperatorSeminorm f * ‖(x : V)‖
    rw [← hwt, map_add, map_smul, hgu, smul_zero, add_zero, hgw]
    calc
      ‖f ⟨w, hw⟩‖ ≤ linearMapOperatorSeminorm f * ‖w‖ := norm_linearMap_apply_le f ⟨w, hw⟩
      _ ≤ linearMapOperatorSeminorm f * (A * ‖w + a • u‖) :=
        mul_le_mul_of_nonneg_left
          (norm_le_mul_norm_add_smul_of_quotient_bound W hA.le hubound ⟨w, hw⟩ a)
          (apply_nonneg _ _)
      _ = _ := by ring

/-- Finite-dimensional ultrametric Hahn–Banach with arbitrary norm loss
`A > 1`. The scalar field may carry the trivial absolute value. -/
theorem exists_ultrametric_extension_norm_le [IsUltrametricDist V]
    (W : Submodule L V) (f : W →ₗ[L] L) {A : ℝ} (hA : 1 < A) :
    ∃ g : V →ₗ[L] L, g.comp W.subtype = f ∧
      linearMapOperatorSeminorm g ≤ A * linearMapOperatorSeminorm f := by
  induction W using WellFoundedGT.induction generalizing A with
  | ind W ih =>
    by_cases hW : W = ⊤
    · let e := LinearEquiv.ofTop W hW
      let g := f.comp e.symm.toLinearMap
      refine ⟨g, ?_, ?_⟩
      · ext w
        exact congrArg f (e.symm_apply_apply w)
      · apply linearMapOperatorSeminorm_le _
          (mul_nonneg (zero_lt_one.trans hA).le (apply_nonneg _ _))
        intro x
        change ‖f (e.symm x)‖ ≤ A * linearMapOperatorSeminorm f * ‖x‖
        calc
          ‖f (e.symm x)‖ ≤ linearMapOperatorSeminorm f * ‖e.symm x‖ :=
            norm_linearMap_apply_le f _
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (le_mul_of_one_le_left (apply_nonneg _ _) hA.le) (norm_nonneg x)
    · have hB : 1 < Real.sqrt A := by
        nlinarith [Real.mul_self_sqrt (zero_lt_one.trans hA).le, Real.sqrt_nonneg A]
      obtain ⟨U, hWU, f', hf', hn⟩ := exists_ultrametric_extension_larger W hW f hB
      obtain ⟨g, hg, hgn⟩ := ih U hWU f' hB
      refine ⟨g, ?_, ?_⟩
      · ext w
        exact (LinearMap.congr_fun hg (Submodule.inclusion hWU.le w)).trans
          (LinearMap.congr_fun hf' w)
      · calc
          linearMapOperatorSeminorm g ≤ Real.sqrt A * linearMapOperatorSeminorm f' := hgn
          _ ≤ Real.sqrt A * (Real.sqrt A * linearMapOperatorSeminorm f) :=
            mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg A)
          _ = A * linearMapOperatorSeminorm f := by
            rw [← mul_assoc, Real.mul_self_sqrt (zero_lt_one.trans hA).le]

omit [FiniteDimensional L V] in
/-- The coordinate functional on the line through `x` has norm `‖x‖⁻¹`,
also over a trivially normed scalar field. -/
theorem linearMapOperatorSeminorm_spanCoord {x : V} (hx : x ≠ 0) :
    linearMapOperatorSeminorm
      (LinearEquiv.toSpanNonzeroSingleton L V x hx).symm.toLinearMap = ‖x‖⁻¹ := by
  let e := LinearEquiv.toSpanNonzeroSingleton L V x hx
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  apply le_antisymm
  · apply linearMapOperatorSeminorm_le _ (inv_nonneg.mpr hn.le)
    intro y
    obtain ⟨a, rfl⟩ := e.surjective y
    change ‖e.symm (e a)‖ ≤ ‖x‖⁻¹ * ‖(e a : V)‖
    rw [e.symm_apply_apply]
    change ‖a‖ ≤ ‖x‖⁻¹ * ‖a • x‖
    simp [norm_smul, mul_comm, hn.ne']
  · have hb := norm_linearMap_apply_le e.symm.toLinearMap (e 1)
    change ‖e.symm (e 1)‖ ≤ linearMapOperatorSeminorm e.symm.toLinearMap * ‖(e 1 : V)‖ at hb
    rw [e.symm_apply_apply, norm_one] at hb
    change 1 ≤ linearMapOperatorSeminorm e.symm.toLinearMap * ‖(1 : L) • x‖ at hb
    rw [← one_div]
    apply (div_le_iff₀ hn).mpr
    simpa only [one_smul] using hb

/-- Every nonzero vector admits an approximately norming functional for any
factor `A > 1`; this is a concrete consumer of approximate extension. -/
theorem exists_ultrametric_norming_functional [IsUltrametricDist V] {x : V} (hx : x ≠ 0)
    {A : ℝ} (hA : 1 < A) :
    ∃ f : V →ₗ[L] L, f x = 1 ∧ linearMapOperatorSeminorm f ≤ A / ‖x‖ := by
  let e := LinearEquiv.toSpanNonzeroSingleton L V x hx
  obtain ⟨f, hf, hn⟩ := exists_ultrametric_extension_norm_le
    (Submodule.span L {x}) e.symm.toLinearMap hA
  refine ⟨f, ?_, ?_⟩
  · have hx' := LinearMap.congr_fun hf (e 1)
    change f ((e 1 : Submodule.span L {x}) : V) = e.symm (e 1) at hx'
    rw [e.symm_apply_apply] at hx'
    simpa [e, LinearEquiv.toSpanNonzeroSingleton_apply] using hx'
  · simpa only [e, linearMapOperatorSeminorm_spanCoord hx, div_eq_mul_inv] using hn

/-- Bounds tested against all algebraic functionals detect the original
ultrametric norm. No norm-attaining extension is asserted. -/
theorem norm_le_of_forall_linearMap_apply_le [IsUltrametricDist V]
    {x : V} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ f : V →ₗ[L] L, ‖f x‖ ≤ linearMapOperatorSeminorm f * C) : ‖x‖ ≤ C := by
  by_cases hx : x = 0
  · simpa [hx] using hC
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  apply (le_iff_forall_one_lt_le_mul₀ hC).mpr
  intro A hA
  obtain ⟨f, hfx, hf⟩ := exists_ultrametric_norming_functional (L := L) hx hA
  have he : 1 ≤ linearMapOperatorSeminorm f * C := by simpa only [hfx, norm_one] using h f
  have hmul := he.trans (mul_le_mul_of_nonneg_right hf hC)
  have hmul' := mul_le_mul_of_nonneg_right hmul hn.le
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hn.ne'] using hmul'

/-- A finite-dimensional ultrametric norm equals its bidual supremum.
The range includes the zero functional, so the formula also covers dimension zero. -/
theorem norm_eq_sSup_linearMap_ratios [IsUltrametricDist V] (x : V) :
    ‖x‖ = sSup (Set.range fun f : V →ₗ[L] L ↦ ‖f x‖ / linearMapOperatorSeminorm f) := by
  have hp (f : V →ₗ[L] L) (hf : f ≠ 0) : 0 < linearMapOperatorSeminorm f :=
    lt_of_le_of_ne' (apply_nonneg _ _)
      (fun h ↦ hf ((linearMapOperatorSeminorm_eq_zero_iff f).mp h))
  have hb (f : V →ₗ[L] L) : ‖f x‖ / linearMapOperatorSeminorm f ≤ ‖x‖ := by
    by_cases hf : f = 0
    · simp [hf]
    · exact (div_le_iff₀ (hp f hf)).mpr (by simpa [mul_comm] using norm_linearMap_apply_le f x)
  have hbounded : BddAbove (Set.range fun f : V →ₗ[L] L ↦
      ‖f x‖ / linearMapOperatorSeminorm f) := ⟨‖x‖, by rintro _ ⟨f, rfl⟩; exact hb f⟩
  apply le_antisymm
  · apply norm_le_of_forall_linearMap_apply_le (L := L)
      (le_csSup hbounded ⟨0, by simp⟩)
    intro f
    by_cases hf : f = 0
    · simp [hf]
    · have h := (div_le_iff₀ (hp f hf)).mp (le_csSup hbounded ⟨f, rfl⟩)
      simpa only [mul_comm] using h
  · exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨f, rfl⟩; exact hb f)

end ArakelovGeometry
