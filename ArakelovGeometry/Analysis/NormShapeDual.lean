/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.NormShapeMeasurable

/-!
# The polar profile of an absolute normalized plane norm

The canonical dual on the existing `NormShape` representation. Its closed
interval supremum is the continuous extension of Definition 1.1.48, used in
Proposition 4.1.35. Profile values outside the source interval remain irrelevant.
-/

@[expose] public section

namespace ArakelovGeometry.NormShape

noncomputable section

variable (ψ : NormShape)

/-- Every admissible profile is uniformly bounded away from zero. -/
theorem half_le {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) : (1 : ℝ) / 2 ≤ ψ.toFun u := by
  have h := ψ.lower u hu
  have h₁ := le_max_left u (1 - u)
  have h₂ := le_max_right u (1 - u)
  linarith

theorem pos {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) : 0 < ψ.toFun u := by
  linarith [ψ.half_le hu]

/-- The affine terms of the polar profile, indexed by the source compact interval. -/
def dualTerm (t : ℝ) (u : Set.Icc (0 : ℝ) 1) : ℝ :=
  (t * u.val + (1 - t) * (1 - u.val)) / ψ.toFun u.val

private theorem dualTerm_le (t : ℝ) (u : Set.Icc (0 : ℝ) 1) :
    ψ.dualTerm t u ≤ 2 * (|t| + |1 - t|) := by
  have hnum : t * u.val + (1 - t) * (1 - u.val) ≤ |t| + |1 - t| := by
    apply add_le_add
    · exact (mul_le_mul_of_nonneg_right (le_abs_self t) u.property.1).trans
        (mul_le_of_le_one_right (abs_nonneg _) u.property.2)
    · exact (mul_le_mul_of_nonneg_right (le_abs_self (1 - t))
        (sub_nonneg.mpr u.property.2)).trans
        (mul_le_of_le_one_right (abs_nonneg _) (by linarith [u.property.1]))
  apply (div_le_iff₀ (ψ.pos u.property)).mpr
  have hprod := mul_nonneg (add_nonneg (abs_nonneg t) (abs_nonneg (1 - t)))
    (sub_nonneg.mpr (ψ.half_le u.property))
  nlinarith

private theorem dualTerm_bddAbove (t : ℝ) : BddAbove (Set.range (ψ.dualTerm t)) :=
  ⟨_, by rintro _ ⟨u, rfl⟩; exact ψ.dualTerm_le t u⟩

/-- The literal polar supremum, extended to all real arguments. -/
def dualValue (t : ℝ) : ℝ := sSup (Set.range (ψ.dualTerm t))

theorem dualTerm_le_dualValue (t : ℝ) (u : Set.Icc (0 : ℝ) 1) :
    ψ.dualTerm t u ≤ ψ.dualValue t :=
  le_csSup (ψ.dualTerm_bddAbove t) (Set.mem_range_self u)

theorem dualValue_le {t C : ℝ} (h : ∀ u, ψ.dualTerm t u ≤ C) : ψ.dualValue t ≤ C :=
  csSup_le (Set.range_nonempty _) (by rintro _ ⟨u, rfl⟩; exact h u)

private theorem dualTerm_sub_le (t s : ℝ) (u : Set.Icc (0 : ℝ) 1) :
    ψ.dualTerm t u - ψ.dualTerm s u ≤ 2 * |t - s| := by
  have hu : |2 * u.val - 1| ≤ 1 := abs_le.mpr ⟨by linarith [u.property.1],
    by linarith [u.property.2]⟩
  have hm : (t - s) * (2 * u.val - 1) ≤ |t - s| := by
    calc
      _ ≤ |(t - s) * (2 * u.val - 1)| := le_abs_self _
      _ = |t - s| * |2 * u.val - 1| := abs_mul _ _
      _ ≤ |t - s| := mul_le_of_le_one_right (abs_nonneg _) hu
  have he : ψ.dualTerm t u - ψ.dualTerm s u =
      ((t - s) * (2 * u.val - 1)) / ψ.toFun u.val := by unfold dualTerm; ring
  rw [he]
  apply (div_le_iff₀ (ψ.pos u.property)).mpr
  have hp := mul_nonneg (abs_nonneg (t - s)) (sub_nonneg.mpr (ψ.half_le u.property))
  nlinarith

theorem dualValue_sub_le (t s : ℝ) : ψ.dualValue t - ψ.dualValue s ≤ 2 * |t - s| := by
  apply sub_le_iff_le_add.mpr
  apply ψ.dualValue_le
  intro u
  have h := ψ.dualTerm_sub_le t s u
  have hs := ψ.dualTerm_le_dualValue s u
  linarith

/-- Every polar supremum is globally two-Lipschitz in its scalar argument. -/
theorem dualValue_lipschitz : LipschitzWith 2 ψ.dualValue := by
  apply LipschitzWith.of_dist_le_mul
  intro t s
  rw [Real.dist_eq, Real.dist_eq]
  apply abs_le.mpr
  constructor
  · have h := ψ.dualValue_sub_le s t
    rw [abs_sub_comm s t] at h
    change -(2 * |t - s|) ≤ ψ.dualValue t - ψ.dualValue s
    linarith
  · exact ψ.dualValue_sub_le t s

/-- The endpoint test functionals give the exact admissible lower bound. -/
theorem max_le_dualValue (t : ℝ) : max t (1 - t) ≤ ψ.dualValue t := by
  apply max_le
  · simpa [dualTerm] using ψ.dualTerm_le_dualValue t ⟨1, by norm_num⟩
  · simpa [dualTerm] using ψ.dualTerm_le_dualValue t ⟨0, by norm_num⟩

/-- On the source interval the polar supremum is at most one. -/
theorem dualValue_le_one {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : ψ.dualValue t ≤ 1 := by
  apply ψ.dualValue_le
  intro u
  apply (div_le_one (ψ.pos u.property)).mpr
  have h₁ := mul_le_mul_of_nonneg_left (le_max_left u.val (1 - u.val)) ht.1
  have h₂ := mul_le_mul_of_nonneg_left (le_max_right u.val (1 - u.val))
    (sub_nonneg.mpr ht.2)
  have hψ := ψ.lower u.val u.property
  nlinarith

/-- A supremum of the affine polar terms is convex. -/
theorem dualValue_convexOn : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) ψ.dualValue := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  apply ψ.dualValue_le
  intro u
  have he : ψ.dualTerm (a * x + b * y) u = a * ψ.dualTerm x u + b * ψ.dualTerm y u := by
    have hb' : b = 1 - a := by linarith
    rw [hb']
    unfold dualTerm
    ring
  rw [he]
  exact add_le_add (mul_le_mul_of_nonneg_left (ψ.dualTerm_le_dualValue x u) ha)
    (mul_le_mul_of_nonneg_left (ψ.dualTerm_le_dualValue y u) hb)

/-- The canonical polar operation on the existing admissible-profile representation. -/
def dual : NormShape where
  toFun := ψ.dualValue
  continuousOn := ψ.dualValue_lipschitz.continuous.continuousOn
  convexOn := ψ.dualValue_convexOn
  lower t _ := ψ.max_le_dualValue t
  upper _ ht := ψ.dualValue_le_one ht

@[simp] theorem dual_apply (t : ℝ) : ψ.dual.toFun t = ψ.dualValue t := rfl

private theorem dualTerm_sub_profile_le (χ : NormShape) {D t : ℝ}
    (hD : 0 ≤ D) (hψχ : ∀ u ∈ Set.Icc (0 : ℝ) 1, |ψ.toFun u - χ.toFun u| ≤ D)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : Set.Icc (0 : ℝ) 1) :
    ψ.dualTerm t u - χ.dualTerm t u ≤ 4 * D := by
  let N := t * u.val + (1 - t) * (1 - u.val)
  have hN0 : 0 ≤ N := add_nonneg (mul_nonneg ht.1 u.property.1)
    (mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr u.property.2))
  have hN1 : N ≤ 1 := by
    have h₁ := mul_le_of_le_one_right ht.1 u.property.2
    have h₂ := mul_le_of_le_one_right (sub_nonneg.mpr ht.2)
      (by linarith [u.property.1] : 1 - u.val ≤ 1)
    dsimp [N]
    linarith
  have hp := ψ.pos u.property
  have hq := χ.pos u.property
  have hpq : (1 : ℝ) / 4 ≤ ψ.toFun u.val * χ.toFun u.val := by
    have h := mul_nonneg (sub_nonneg.mpr (ψ.half_le u.property))
      (sub_nonneg.mpr (χ.half_le u.property))
    nlinarith [ψ.half_le u.property, χ.half_le u.property]
  have hd : χ.toFun u.val - ψ.toFun u.val ≤ D := by
    have h := (abs_le.mp (hψχ u.val u.property)).1
    linarith
  have hnum : N * (χ.toFun u.val - ψ.toFun u.val) ≤ D :=
    (mul_le_mul_of_nonneg_left hd hN0).trans (mul_le_of_le_one_left hD hN1)
  have he : ψ.dualTerm t u - χ.dualTerm t u =
      N * (χ.toFun u.val - ψ.toFun u.val) / (ψ.toFun u.val * χ.toFun u.val) := by
    unfold dualTerm
    dsimp [N]
    field_simp
  rw [he]
  apply (div_le_iff₀ (mul_pos hp hq)).mpr
  have h := mul_nonneg hD (sub_nonneg.mpr hpq)
  nlinarith

/-- Uniform scalar bounds on two profiles give a uniform fourfold bound on their polars. -/
theorem abs_dualValue_sub_le (χ : NormShape) {D : ℝ} (hD : 0 ≤ D)
    (hψχ : ∀ u ∈ Set.Icc (0 : ℝ) 1, |ψ.toFun u - χ.toFun u| ≤ D)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |ψ.dualValue t - χ.dualValue t| ≤ 4 * D := by
  have hupper (ψ χ : NormShape)
      (hψχ : ∀ u ∈ Set.Icc (0 : ℝ) 1, |ψ.toFun u - χ.toFun u| ≤ D) :
      ψ.dualValue t ≤ χ.dualValue t + 4 * D := by
    apply ψ.dualValue_le
    intro u
    have h := ψ.dualTerm_sub_profile_le χ hD hψχ ht u
    have hχ := χ.dualTerm_le_dualValue t u
    linarith
  have h₁ := hupper ψ χ hψχ
  have h₂ := hupper χ ψ (fun u hu ↦ by simpa only [abs_sub_comm] using hψχ u hu)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Polarization is four-Lipschitz in the existing uniform continuous-map norm. -/
theorem norm_dual_continuousMap_sub_le (χ : NormShape) :
    ‖ψ.dual.continuousMap - χ.dual.continuousMap‖ ≤
      4 * ‖ψ.continuousMap - χ.continuousMap‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num) (norm_nonneg _))).mpr
  intro t
  change |ψ.dualValue t.val - χ.dualValue t.val| ≤ _
  apply ψ.abs_dualValue_sub_le χ (norm_nonneg _) _ t.property
  intro u hu
  exact (ψ.continuousMap - χ.continuousMap).norm_coe_le_norm ⟨u, hu⟩

/-- Irrelevant profile values outside the interval do not change the polar restriction. -/
theorem dual_continuousMap_congr (χ : NormShape) (h : ψ.continuousMap = χ.continuousMap) :
    ψ.dual.continuousMap = χ.dual.continuousMap := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [h, sub_self, norm_zero, mul_zero] using ψ.norm_dual_continuousMap_sub_le χ

/-- The closed-interval supremum equals the literal open-interval formula of Definition1.1.48. -/
theorem dualValue_eq_sSup_open (t : ℝ) :
    ψ.dualValue t = sSup ((fun u : ℝ ↦
      (t * u + (1 - t) * (1 - u)) / ψ.toFun u) '' Set.Ioo (0 : ℝ) 1) := by
  let f : ℝ → ℝ := fun u ↦ (t * u + (1 - t) * (1 - u)) / ψ.toFun u
  have hnon : (f '' Set.Ioo (0 : ℝ) 1).Nonempty :=
    ⟨f (1 / 2), 1 / 2, by norm_num, rfl⟩
  have hbdd : BddAbove (f '' Set.Ioo (0 : ℝ) 1) := by
    refine ⟨2 * (|t| + |1 - t|), ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact ψ.dualTerm_le t ⟨u, ⟨hu.1.le, hu.2.le⟩⟩
  have hcl : closure (Set.Ioo (0 : ℝ) 1) = Set.Icc (0 : ℝ) 1 := closure_Ioo (by norm_num)
  have hf : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.div _ ψ.continuousOn (fun u hu ↦ (ψ.pos hu).ne')
    fun_prop
  apply le_antisymm
  · apply ψ.dualValue_le
    intro u
    exact le_on_closure (fun x hx ↦ le_csSup hbdd (Set.mem_image_of_mem f hx))
      (hcl.symm ▸ hf) continuousOn_const (hcl.symm ▸ u.property)
  · apply csSup_le hnon
    rintro _ ⟨u, hu, rfl⟩
    exact ψ.dualTerm_le_dualValue t ⟨u, ⟨hu.1.le, hu.2.le⟩⟩

local instance : MeasurableSpace C(Set.Icc (0 : ℝ) 1, ℝ) := borel _
local instance : BorelSpace C(Set.Icc (0 : ℝ) 1, ℝ) := ⟨rfl⟩

private def polarOnRange (f : Set.range continuousMap) : C(Set.Icc (0 : ℝ) 1, ℝ) :=
  f.property.choose.dual.continuousMap

private theorem polarOnRange_apply (ψ : NormShape) :
    polarOnRange ⟨ψ.continuousMap, ⟨ψ, rfl⟩⟩ = ψ.dual.continuousMap :=
  dual_continuousMap_congr _ _
    (Exists.choose_spec (⟨ψ, rfl⟩ : ∃ χ, χ.continuousMap = ψ.continuousMap))

private theorem polarOnRange_lipschitz : LipschitzWith 4 polarOnRange := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  have h := f.property.choose.norm_dual_continuousMap_sub_le g.property.choose
  simpa only [polarOnRange, dist_eq_norm, Subtype.dist_eq,
    f.property.choose_spec, g.property.choose_spec, NNReal.coe_ofNat] using h

/-- The literal source measurable-profile predicate is preserved by polar dualization. -/
theorem IsMeasurableFamily.dual {Ω : Type*} [MeasurableSpace Ω] {ψ : Ω → NormShape}
    (hψ : IsMeasurableFamily ψ) : IsMeasurableFamily (fun ω ↦ (ψ ω).dual) := by
  have hbase : Measurable (fun ω ↦
      (⟨(ψ ω).continuousMap, ⟨ψ ω, rfl⟩⟩ : Set.range continuousMap)) := hψ.subtype_mk
  have h := polarOnRange_lipschitz.continuous.measurable.comp hbase
  simpa only [Function.comp_def, polarOnRange_apply, IsMeasurableFamily] using h

end
end ArakelovGeometry.NormShape
