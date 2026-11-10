/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Linarith

/-!
# A non-Archimedean norm with an expensive residue direction

Double the coordinate maximum exactly when a unit-slope linear functional
has strictly smaller norm. This gives an actual nonultrametric plane norm
whose completed operator dual is still the coordinate maximum. It is the
local producer for the standard-number-field correction to Remark 4.1.36.
-/

namespace ArakelovGeometry
namespace ResidueDirectionBump

variable {F V : Type*} [NormedField F] [NormedAddCommGroup V] [NormedSpace F V]

open Classical in
/-- Double precisely the directions where the functional decreases the norm. -/
noncomputable def value (ℓ : V →ₗ[F] F) (x : V) : ℝ :=
  if ‖ℓ x‖ < ‖x‖ then 2 * ‖x‖ else ‖x‖

theorem norm_le_value (ℓ : V →ₗ[F] F) (x : V) : ‖x‖ ≤ value ℓ x := by
  unfold value
  split_ifs <;> linarith [norm_nonneg x]

theorem value_le_two_mul_norm (ℓ : V →ₗ[F] F) (x : V) : value ℓ x ≤ 2 * ‖x‖ := by
  unfold value
  split_ifs <;> linarith [norm_nonneg x]

theorem value_nonneg (ℓ : V →ₗ[F] F) (x : V) : 0 ≤ value ℓ x :=
  (norm_nonneg x).trans (norm_le_value ℓ x)

@[simp] theorem value_zero (ℓ : V →ₗ[F] F) : value ℓ 0 = 0 := by
  simp [value]

@[simp] theorem value_eq_zero_iff (ℓ : V →ₗ[F] F) (x : V) : value ℓ x = 0 ↔ x = 0 := by
  constructor
  · intro h
    exact norm_eq_zero.mp (le_antisymm (h ▸ norm_le_value ℓ x) (norm_nonneg x))
  · rintro rfl
    exact value_zero ℓ

theorem value_smul (ℓ : V →ₗ[F] F) (c : F) (x : V) :
    value ℓ (c • x) = ‖c‖ * value ℓ x := by
  by_cases hc : c = 0
  · simp [hc]
  have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
  simp only [value, map_smul, norm_smul, mul_lt_mul_iff_right₀ hc']
  split_ifs <;> ring

variable [IsUltrametricDist F] [IsUltrametricDist V]

private theorem value_add_eq_left (ℓ : V →ₗ[F] F) (hℓ : ∀ x, ‖ℓ x‖ ≤ ‖x‖)
    {x y : V} (h : ‖y‖ < ‖x‖) : value ℓ (x + y) = value ℓ x := by
  have hnorm : ‖x + y‖ = ‖x‖ := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt h), max_eq_left h.le]
  have hy : ‖ℓ y‖ < ‖x‖ := (hℓ y).trans_lt h
  have htest : ‖ℓ (x + y)‖ < ‖x‖ ↔ ‖ℓ x‖ < ‖x‖ := by
    constructor
    · intro hs
      have heq : ℓ x = ℓ (x + y) + -(ℓ y) := by simp
      rw [heq]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt hs (by simpa using hy))
    · intro hx
      rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
  simp only [value, hnorm, htest]

theorem value_add_le (ℓ : V →ₗ[F] F) (hℓ : ∀ x, ‖ℓ x‖ ≤ ‖x‖) (x y : V) :
    value ℓ (x + y) ≤ value ℓ x + value ℓ y := by
  rcases lt_trichotomy ‖x‖ ‖y‖ with h | h | h
  · rw [add_comm x y, value_add_eq_left ℓ hℓ h]
    linarith [value_nonneg ℓ x]
  · have hnorm : ‖x + y‖ ≤ ‖x‖ := by
      simpa only [h, max_self] using IsUltrametricDist.norm_add_le_max x y
    have h₁ := value_le_two_mul_norm ℓ (x + y)
    have h₂ := norm_le_value ℓ x
    have h₃ := norm_le_value ℓ y
    linarith
  · rw [value_add_eq_left ℓ hℓ h]
    linarith [value_nonneg ℓ y]

/-- The actual residue-direction bump seminorm, separated by the original norm. -/
noncomputable def seminorm (ℓ : V →ₗ[F] F) (hℓ : ∀ x, ‖ℓ x‖ ≤ ‖x‖) : Seminorm F V :=
  Seminorm.of (value ℓ) (value_add_le ℓ hℓ) (value_smul ℓ)

@[simp] theorem seminorm_apply (ℓ : V →ₗ[F] F) (hℓ : ∀ x, ‖ℓ x‖ ≤ ‖x‖) (x : V) :
    seminorm ℓ hℓ x = value ℓ x := rfl

/-- The unit-slope residue functional on the actual two-dimensional plane. -/
def slopeFunctional (a : F) : (F × F) →ₗ[F] F :=
  LinearMap.snd F F F - a • LinearMap.fst F F F

omit [IsUltrametricDist F] in
@[simp] theorem slopeFunctional_apply (a : F) (z : F × F) :
    slopeFunctional a z = z.2 - a * z.1 := rfl

theorem slopeFunctional_norm_le (a : F) (ha : ‖a‖ = 1) (z : F × F) :
    ‖slopeFunctional a z‖ ≤ ‖z‖ := by
  rw [slopeFunctional_apply, sub_eq_add_neg]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  simp only [norm_neg, norm_mul, ha, one_mul, Prod.norm_def]
  exact max_le (le_max_right _ _) (le_max_left _ _)

private instance planeUltrametric : IsUltrametricDist (F × F) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ by
    simp only [Prod.norm_def, Prod.fst_add, Prod.snd_add]
    apply max_le
    · exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le_max (le_max_left _ _) (le_max_left _ _))
    · exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le_max (le_max_right _ _) (le_max_right _ _))

/-- A genuine separated plane seminorm with one expensive residue direction. -/
noncomputable def planeSeminorm (a : F) (ha : ‖a‖ = 1) : Seminorm F (F × F) :=
  seminorm (slopeFunctional a) (slopeFunctional_norm_le a ha)

@[simp] theorem planeSeminorm_eq_zero_iff (a : F) (ha : ‖a‖ = 1) (z : F × F) :
    planeSeminorm a ha z = 0 ↔ z = 0 := value_eq_zero_iff _ _

@[simp] theorem planeSeminorm_axis_left (a : F) (ha : ‖a‖ = 1) :
    planeSeminorm a ha (1, 0) = 1 := by
  change value (slopeFunctional a) (1, 0) = 1
  simp [value, Prod.norm_def, ha]

@[simp] theorem planeSeminorm_axis_right (a : F) (ha : ‖a‖ = 1) :
    planeSeminorm a ha (0, 1) = 1 := by
  change value (slopeFunctional a) (0, 1) = 1
  simp [value, Prod.norm_def]

@[simp] theorem planeSeminorm_direction (a : F) (ha : ‖a‖ = 1) :
    planeSeminorm a ha (1, a) = 2 := by
  change value (slopeFunctional a) (1, a) = 2
  simp [value, Prod.norm_def, ha]

/-- The coordinate maximum controls every functional evaluation. -/
theorem norm_apply_le_max_mul_planeSeminorm (a : F) (ha : ‖a‖ = 1)
    (f : (F × F) →ₗ[F] F) (z : F × F) :
    ‖f z‖ ≤ max ‖f (1, 0)‖ ‖f (0, 1)‖ * planeSeminorm a ha z := by
  have hz : z = z.1 • (1, 0) + z.2 • (0, 1) := by ext <;> simp
  have hf : f z = z.1 * f (1, 0) + z.2 * f (0, 1) := by
    conv_lhs => rw [hz]
    simp only [map_add, map_smul, smul_eq_mul]
  rw [hf]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  rw [norm_mul, norm_mul]
  have hn : ‖z‖ ≤ planeSeminorm a ha z := norm_le_value _ _
  have hM : 0 ≤ max ‖f (1, 0)‖ ‖f (0, 1)‖ :=
    (norm_nonneg _).trans (le_max_left _ _)
  apply max_le
  · rw [mul_comm]
    exact mul_le_mul (le_max_left _ _) ((le_max_left _ _).trans hn)
      (norm_nonneg _) hM
  · rw [mul_comm]
    exact mul_le_mul (le_max_right _ _) ((le_max_right _ _).trans hn)
      (norm_nonneg _) hM

/-- The supremum defining the completed operator dual is exactly the coordinate maximum. -/
theorem sSup_ratio_eq_max (a : F) (ha : ‖a‖ = 1) (f : (F × F) →ₗ[F] F) :
    sSup (Set.range fun z : F × F ↦ ‖f z‖ / planeSeminorm a ha z) =
      max ‖f (1, 0)‖ ‖f (0, 1)‖ := by
  have hbound (z : F × F) :
      ‖f z‖ / planeSeminorm a ha z ≤ max ‖f (1, 0)‖ ‖f (0, 1)‖ := by
    by_cases hz : z = 0
    · simp [hz]
    · have hpos : 0 < planeSeminorm a ha z :=
        lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm ((planeSeminorm_eq_zero_iff a ha z).not.mpr hz))
      exact (div_le_iff₀ hpos).mpr (norm_apply_le_max_mul_planeSeminorm a ha f z)
  have hbdd : BddAbove (Set.range fun z : F × F ↦ ‖f z‖ / planeSeminorm a ha z) :=
    ⟨_, by rintro _ ⟨z, rfl⟩; exact hbound z⟩
  apply le_antisymm
  · exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨z, rfl⟩; exact hbound z)
  · apply max_le
    · simpa using le_csSup hbdd (Set.mem_range_self (1, 0))
    · simpa using le_csSup hbdd (Set.mem_range_self (0, 1))

end ResidueDirectionBump
end ArakelovGeometry
