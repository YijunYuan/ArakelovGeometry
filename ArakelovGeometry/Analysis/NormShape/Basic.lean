/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-!
# Convex shapes for norms on binary direct sums

A continuous convex profile on `[0, 1]`, bounded between `max t (1 - t)`
and `1`, defines the positively homogeneous function
`(a + b) * ψ (a / (a + b))` on the nonnegative quadrant. This is the
shape used for direct sums in Chen–Moriwaki, §4.1.1.3.
-/

@[expose] public section

namespace ArakelovGeometry

/-- The source's continuous convex profile on `[0,1]`. Values outside the
interval are irrelevant; this real-function presentation permits `ConvexOn`. -/
structure NormShape where
  /-- The real-valued profile, restricted to the unit interval. -/
  toFun : ℝ → ℝ
  continuousOn : ContinuousOn toFun (Set.Icc 0 1)
  convexOn : ConvexOn ℝ (Set.Icc 0 1) toFun
  lower : ∀ t ∈ Set.Icc (0 : ℝ) 1, max t (1 - t) ≤ toFun t
  upper : ∀ t ∈ Set.Icc (0 : ℝ) 1, toFun t ≤ 1

namespace NormShape

noncomputable section

variable (ψ : NormShape)

/-- The homogeneous perspective of the profile. At `(0,0)` the factor
`a + b` is zero, so Lean's total division gives the source's zero branch. -/
def perspective (a b : ℝ) : ℝ := (a + b) * ψ.toFun (a / (a + b))

@[simp]
theorem perspective_zero_zero : ψ.perspective 0 0 = 0 := by
  simp [perspective]

@[simp]
theorem map_zero : ψ.toFun 0 = 1 := by
  apply le_antisymm (ψ.upper 0 (by norm_num))
  simpa using ψ.lower 0 (by norm_num)

@[simp]
theorem map_one : ψ.toFun 1 = 1 := by
  apply le_antisymm (ψ.upper 1 (by norm_num))
  simpa using ψ.lower 1 (by norm_num)

@[simp]
theorem perspective_zero_left (b : ℝ) : ψ.perspective 0 b = b := by
  simp [perspective]

@[simp]
theorem perspective_zero_right (a : ℝ) : ψ.perspective a 0 = a := by
  by_cases ha : a = 0
  · simp [ha]
  · simp [perspective, ha]

private theorem ratio_mem {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a / (a + b) ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : a + b = 0
  · simp [h]
  · have hs : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm h)
    exact ⟨div_nonneg ha hs.le, (div_le_one hs).mpr (by linarith)⟩

/-- Only the restriction of the profile to the source interval affects its
perspective on nonnegative coordinates. -/
theorem perspective_congr (χ : NormShape)
    (h : Set.EqOn ψ.toFun χ.toFun (Set.Icc (0 : ℝ) 1))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ψ.perspective a b = χ.perspective a b := by
  simp only [perspective, h (ratio_mem ha hb)]

/-- The perspective dominates each coordinate. -/
theorem max_le_perspective {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max a b ≤ ψ.perspective a b := by
  by_cases h : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  · have hl := mul_le_mul_of_nonneg_left (ψ.lower _ (ratio_mem ha hb))
      (add_nonneg ha hb)
    rw [mul_max_of_nonneg _ _ (add_nonneg ha hb)] at hl
    have h₁ : (a + b) * (a / (a + b)) = a := by field_simp
    have h₂ : (a + b) * (1 - a / (a + b)) = b := by field_simp; ring
    simpa only [h₁, h₂, perspective] using hl

/-- The perspective is bounded above by the sum of coordinates. -/
theorem perspective_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ψ.perspective a b ≤ a + b := by
  simpa only [perspective, mul_one] using
    mul_le_mul_of_nonneg_left (ψ.upper _ (ratio_mem ha hb)) (add_nonneg ha hb)

theorem perspective_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ ψ.perspective a b :=
  ha.trans ((le_max_left _ _).trans (ψ.max_le_perspective ha hb))

/-- Positive homogeneity includes the zero scalar. -/
theorem perspective_mul (r a b : ℝ) :
    ψ.perspective (r * a) (r * b) = r * ψ.perspective a b := by
  by_cases hr : r = 0
  · simp [hr]
  · simp only [perspective, ← mul_add, mul_div_mul_left _ _ hr, mul_assoc]

/-- Convexity of the shape gives subadditivity on the nonnegative quadrant. -/
theorem perspective_add_le {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ψ.perspective (a + c) (b + d) ≤ ψ.perspective a b + ψ.perspective c d := by
  by_cases hs : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  by_cases ht : c + d = 0
  · have hc0 : c = 0 := by linarith
    have hd0 : d = 0 := by linarith
    simp [hc0, hd0]
  have hspos : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hs)
  have htpos : 0 < c + d := lt_of_le_of_ne (add_nonneg hc hd) (Ne.symm ht)
  have hsum : 0 < a + b + (c + d) := add_pos hspos htpos
  have hconv := (convexOn_iff_div.mp ψ.convexOn).2 (ratio_mem ha hb)
    (ratio_mem hc hd) hspos.le htpos.le hsum
  simp only [smul_eq_mul] at hconv
  have hratio : (a + b) / (a + b + (c + d)) * (a / (a + b)) +
      (c + d) / (a + b + (c + d)) * (c / (c + d)) =
        (a + c) / (a + c + (b + d)) := by
    have hsum' : a + c + (b + d) ≠ 0 := by linarith
    field_simp
    ring
  rw [hratio] at hconv
  have h := mul_le_mul_of_nonneg_left hconv hsum.le
  have hleft : a + b + (c + d) = a + c + (b + d) := by ring
  have hright : (a + b + (c + d)) *
      ((a + b) / (a + b + (c + d)) * ψ.toFun (a / (a + b)) +
        (c + d) / (a + b + (c + d)) * ψ.toFun (c / (c + d))) =
      ψ.perspective a b + ψ.perspective c d := by
    simp only [perspective]
    field_simp
  rw [hright, hleft] at h
  exact h

/-- The perspective is convex on the nonnegative quadrant. -/
theorem perspective_combo_le {a b c d r s : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    ψ.perspective (r * a + s * c) (r * b + s * d) ≤
      r * ψ.perspective a b + s * ψ.perspective c d := by
  simpa only [perspective_mul] using ψ.perspective_add_le
    (mul_nonneg hr ha) (mul_nonneg hr hb) (mul_nonneg hs hc) (mul_nonneg hs hd)

/-- Increasing the first nonnegative coordinate increases the perspective. -/
theorem perspective_mono_left {a A b : ℝ}
    (ha : 0 ≤ a) (haA : a ≤ A) (hb : 0 ≤ b) :
    ψ.perspective a b ≤ ψ.perspective A b := by
  by_cases hA : A = 0
  · have ha0 : a = 0 := le_antisymm (haA.trans_eq hA) ha
    simp [ha0, hA]
  have hApos : 0 < A := lt_of_le_of_ne (ha.trans haA) (Ne.symm hA)
  let r := a / A
  have hr : 0 ≤ r := div_nonneg ha hApos.le
  have hr1 : r ≤ 1 := (div_le_one hApos).mpr haA
  have hs : 0 ≤ 1 - r := sub_nonneg.mpr hr1
  have hra : r * A = a := div_mul_cancel₀ _ hA
  have hrb : r * b + (1 - r) * b = b := by ring
  have h := ψ.perspective_combo_le hApos.le hb (le_refl 0) hb hr hs
  simp only [mul_zero, add_zero, hra, hrb, perspective_zero_left] at h
  calc
    ψ.perspective a b ≤ r * ψ.perspective A b + (1 - r) * b := h
    _ ≤ r * ψ.perspective A b + (1 - r) * ψ.perspective A b := by
      gcongr
      exact (le_max_right _ _).trans (ψ.max_le_perspective hApos.le hb)
    _ = ψ.perspective A b := by ring

/-- Increasing the second nonnegative coordinate increases the perspective. -/
theorem perspective_mono_right {a b B : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hbB : b ≤ B) :
    ψ.perspective a b ≤ ψ.perspective a B := by
  by_cases hB : B = 0
  · have hb0 : b = 0 := le_antisymm (hbB.trans_eq hB) hb
    simp [hb0, hB]
  have hBpos : 0 < B := lt_of_le_of_ne (hb.trans hbB) (Ne.symm hB)
  let r := b / B
  have hr : 0 ≤ r := div_nonneg hb hBpos.le
  have hr1 : r ≤ 1 := (div_le_one hBpos).mpr hbB
  have hs : 0 ≤ 1 - r := sub_nonneg.mpr hr1
  have hrb : r * B = b := div_mul_cancel₀ _ hB
  have hra : r * a + (1 - r) * a = a := by ring
  have h := ψ.perspective_combo_le ha hBpos.le ha (le_refl 0) hr hs
  simp only [mul_zero, add_zero, hra, hrb, perspective_zero_right] at h
  calc
    ψ.perspective a b ≤ r * ψ.perspective a B + (1 - r) * a := h
    _ ≤ r * ψ.perspective a B + (1 - r) * ψ.perspective a B := by
      gcongr
      exact (le_max_left _ _).trans (ψ.max_le_perspective ha hBpos.le)
    _ = ψ.perspective a B := by ring

/-- Coordinatewise monotonicity on the nonnegative quadrant. -/
theorem perspective_mono {a b A B : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haA : a ≤ A) (hbB : b ≤ B) :
    ψ.perspective a b ≤ ψ.perspective A B :=
  (ψ.perspective_mono_left ha haA hb).trans
    (ψ.perspective_mono_right (ha.trans haA) hb hbB)

/-- The perspective separates the origin in the nonnegative quadrant. -/
theorem perspective_eq_zero_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ψ.perspective a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hmax := ψ.max_le_perspective ha hb
    rw [h, max_le_iff] at hmax
    exact ⟨le_antisymm hmax.1 ha, le_antisymm hmax.2 hb⟩
  · rintro ⟨rfl, rfl⟩
    exact ψ.perspective_zero_zero

/-- The supremum shape, used at non-Archimedean places for orthogonal sums. -/
def maxShape : NormShape where
  toFun t := max t (1 - t)
  continuousOn := (continuous_id.max (continuous_const.sub continuous_id)).continuousOn
  convexOn := (convexOn_id (convex_Icc 0 1)).sup
    ((convexOn_const 1 (convex_Icc 0 1)).sub (concaveOn_id (convex_Icc 0 1)))
  lower _ _ := le_rfl
  upper t ht := max_le ht.2 (by linarith [ht.1])

/-- The constant-one shape gives the sum norm. -/
def sumShape : NormShape where
  toFun _ := 1
  continuousOn := continuousOn_const
  convexOn := convexOn_const 1 (convex_Icc 0 1)
  lower t ht := max_le ht.2 (by linarith [ht.1])
  upper _ _ := le_rfl

@[simp]
theorem maxShape_perspective {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    maxShape.perspective a b = max a b := by
  by_cases h : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  change (a + b) * max (a / (a + b)) (1 - a / (a + b)) = max a b
  rw [mul_max_of_nonneg _ _ (add_nonneg ha hb)]
  congr 1
  · field_simp
  · field_simp
    ring

@[simp]
theorem sumShape_perspective (a b : ℝ) : sumShape.perspective a b = a + b := by
  simp [perspective, sumShape]

section Seminorm

variable {𝕜 E F : Type*} [SeminormedRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- The general convex-shape seminorm on a product. -/
def prodSeminorm (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) : Seminorm 𝕜 (E × F) :=
  Seminorm.of (fun z ↦ ψ.perspective (p z.1) (q z.2))
    (fun x y ↦ by
      apply (ψ.perspective_mono (apply_nonneg _ _) (apply_nonneg _ _)
        (map_add_le_add p x.1 y.1) (map_add_le_add q x.2 y.2)).trans
      exact ψ.perspective_add_le (apply_nonneg _ _) (apply_nonneg _ _)
        (apply_nonneg _ _) (apply_nonneg _ _))
    (fun a x ↦ by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul_eq_mul, perspective_mul])

@[simp]
theorem prodSeminorm_apply (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (z : E × F) :
    ψ.prodSeminorm p q z = ψ.perspective (p z.1) (q z.2) := rfl

/-- Combining two separated seminorms gives a separated seminorm. -/
theorem prodSeminorm_eq_zero_iff (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F)
    (hp : ∀ x, p x = 0 ↔ x = 0) (hq : ∀ y, q y = 0 ↔ y = 0) (z : E × F) :
    ψ.prodSeminorm p q z = 0 ↔ z = 0 := by
  rw [prodSeminorm_apply, ψ.perspective_eq_zero_iff (apply_nonneg _ _) (apply_nonneg _ _),
    hp, hq]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact Prod.ext h₁ h₂
  · rintro rfl
    exact ⟨rfl, rfl⟩

end Seminorm

end

end NormShape

end ArakelovGeometry
