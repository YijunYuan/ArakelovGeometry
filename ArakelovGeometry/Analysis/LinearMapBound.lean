/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.FiniteDimensional
import Mathlib.Analysis.Normed.Group.Hom

/-!
# Bounds for linear maps over complete normed fields

The operator bounds used for dual norms include trivially normed fields.
-/

namespace NormedAddGroupHom

variable {L V W : Type*} [NormedField L]
  [SeminormedAddCommGroup V] [SeminormedAddCommGroup W] [NormedSpace L W]

/-- The operator norm on bounded additive maps respects pointwise scalar multiplication. -/
noncomputable instance normedSpace : NormedSpace L (NormedAddGroupHom V W) where
  norm_smul_le a f := by
    apply (a • f).opNorm_le_bound (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    intro x
    simp only [smul_apply, norm_smul]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (f.le_opNorm x) (norm_nonneg a)

end NormedAddGroupHom

namespace ArakelovGeometry

open Module

variable {L V W : Type*} [NormedField L] [CompleteSpace L]
  [NormedAddCommGroup V] [NormedSpace L V] [FiniteDimensional L V]
  [SeminormedAddCommGroup W] [NormedSpace L W]

/-- Linear maps with finite-dimensional domain are bounded over every complete
normed field, including trivially normed fields. -/
theorem linearMap_exists_pos_bound (f : V →ₗ[L] W) :
    ∃ C > 0, ∀ x : V, ‖f x‖ ≤ C * ‖x‖ := by
  classical
  by_cases h : ∃ a : L, a ≠ 0 ∧ ‖a‖ ≠ 1
  · let : NontriviallyNormedField L := NontriviallyNormedField.ofNormNeOne h
    exact (LinearMap.toContinuousLinearMap f).bound
  · have hL (a : L) : ‖a‖ ≤ 1 := by
      by_cases ha : a = 0
      · simp [ha]
      · exact le_of_eq (not_not.mp fun hn ↦ h ⟨a, ha, hn⟩)
    obtain ⟨ε, hε, hsmall⟩ := exists_pos_norm_lt_imp_eq_zero (V := V) hL
    let b := Module.finBasis L V
    let M := ∑ i, ‖f (b i)‖
    have hM : 0 ≤ M := Finset.sum_nonneg fun i _ ↦ norm_nonneg _
    have hbound (x : V) : ‖f x‖ ≤ M := by
      calc
        ‖f x‖ = ‖∑ i, (b.repr x) i • f (b i)‖ := by
          simpa only [map_sum, map_smul] using
            congrArg norm (congrArg f (b.sum_repr x)).symm
        _ ≤ ∑ i, ‖(b.repr x) i • f (b i)‖ := norm_sum_le _ _
        _ ≤ M := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_smul]
          simpa using mul_le_mul_of_nonneg_right (hL ((b.repr x) i)) (norm_nonneg (f (b i)))
    refine ⟨(M + 1) / ε, div_pos (by positivity) hε, fun x ↦ ?_⟩
    by_cases hx : x = 0
    · simp [hx]
    · have hεx : ε ≤ ‖x‖ := le_of_not_gt fun hn ↦ hx (hsmall x hn)
      calc
        ‖f x‖ ≤ M := hbound x
        _ ≤ M + 1 := le_add_of_nonneg_right zero_le_one
        _ = (M + 1) / ε * ε := (div_mul_cancel₀ _ hε.ne').symm
        _ ≤ (M + 1) / ε * ‖x‖ :=
          mul_le_mul_of_nonneg_left hεx (div_nonneg (by positivity) hε.le)

/-- The canonical bounded additive map underlying a finite-dimensional linear map.
Its bound is proved from finite dimensionality, not supplied as extra data. -/
noncomputable def linearMapToNormedAddGroupHom (f : V →ₗ[L] W) :
    NormedAddGroupHom V W where
  toFun := f
  map_add' := f.map_add
  bound' := by
    obtain ⟨C, _, hC⟩ := linearMap_exists_pos_bound f
    exact ⟨C, hC⟩

@[simp]
theorem linearMapToNormedAddGroupHom_apply (f : V →ₗ[L] W) (x : V) :
    linearMapToNormedAddGroupHom f x = f x := rfl

/-- The bounded-additive-map bridge is linear for the canonical pointwise operations. -/
noncomputable def linearMapToNormedAddGroupHomLinear :
    (V →ₗ[L] W) →ₗ[L] NormedAddGroupHom V W where
  toFun := linearMapToNormedAddGroupHom
  map_add' _ _ := NormedAddGroupHom.ext fun _ ↦ rfl
  map_smul' _ _ := NormedAddGroupHom.ext fun _ ↦ rfl

/-- The usual operator seminorm, including over trivially normed complete fields. -/
noncomputable def linearMapOperatorSeminorm : Seminorm L (V →ₗ[L] W) :=
  (normSeminorm L (NormedAddGroupHom V W)).comp linearMapToNormedAddGroupHomLinear

/-- Evaluation is bounded by the operator seminorm. -/
theorem norm_linearMap_apply_le (f : V →ₗ[L] W) (x : V) :
    ‖f x‖ ≤ linearMapOperatorSeminorm f * ‖x‖ :=
  (linearMapToNormedAddGroupHom f).le_opNorm x

/-- Every nonnegative bound for evaluations bounds the operator seminorm. -/
theorem linearMapOperatorSeminorm_le (f : V →ₗ[L] W) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : linearMapOperatorSeminorm f ≤ C :=
  (linearMapToNormedAddGroupHom f).opNorm_le_bound hC h

/-- The operator seminorm is the supremum of the usual evaluation ratios. -/
theorem linearMapOperatorSeminorm_eq_sSup (f : V →ₗ[L] W) :
    linearMapOperatorSeminorm f = sSup (Set.range fun x : V ↦ ‖f x‖ / ‖x‖) := by
  let R := Set.range fun x : V ↦ ‖f x‖ / ‖x‖
  have hb : BddAbove R := ⟨linearMapOperatorSeminorm f, by
    rintro _ ⟨x, rfl⟩
    exact (linearMapToNormedAddGroupHom f).ratio_le_opNorm x⟩
  have h0 : 0 ∈ R := ⟨0, by simp⟩
  apply le_antisymm
  · apply linearMapOperatorSeminorm_le f (le_csSup hb h0)
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · exact (div_le_iff₀ (norm_pos_iff.mpr hx)).mp (le_csSup hb ⟨x, rfl⟩)
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨x, rfl⟩
    exact (linearMapToNormedAddGroupHom f).ratio_le_opNorm x

/-- An ultrametric target gives an ultrametric operator seminorm. -/
theorem linearMapOperatorSeminorm_add_le_max
    (hW : ∀ u v : W, ‖u + v‖ ≤ max ‖u‖ ‖v‖) (f g : V →ₗ[L] W) :
    linearMapOperatorSeminorm (f + g) ≤
      max (linearMapOperatorSeminorm f) (linearMapOperatorSeminorm g) := by
  apply linearMapOperatorSeminorm_le _ (le_max_of_le_left (apply_nonneg _ _))
  intro x
  calc
    ‖(f + g) x‖ ≤ max ‖f x‖ ‖g x‖ := hW _ _
    _ ≤ max (linearMapOperatorSeminorm f * ‖x‖)
        (linearMapOperatorSeminorm g * ‖x‖) :=
      max_le_max (norm_linearMap_apply_le f x) (norm_linearMap_apply_le g x)
    _ = _ := (max_mul_of_nonneg _ _ (norm_nonneg x)).symm

/-- The operator seminorm separates linear maps when the target norm separates points. -/
theorem linearMapOperatorSeminorm_eq_zero_iff {U : Type*}
    [NormedAddCommGroup U] [NormedSpace L U] (f : V →ₗ[L] U) :
    linearMapOperatorSeminorm f = 0 ↔ f = 0 := by
  constructor
  · intro h
    ext x
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa [h] using norm_linearMap_apply_le f x
  · rintro rfl
    exact map_zero _

end ArakelovGeometry
