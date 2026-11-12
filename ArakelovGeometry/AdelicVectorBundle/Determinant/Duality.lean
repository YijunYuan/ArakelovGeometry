/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Determinant.DualNorm

import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Isometric determinant duality

Nearly optimal bases give determinant vectors pairing to one with norm product
arbitrarily close to one. Combined with the canonical completed pairing bound,
this proves the actual determinant-dual norm identity for Hermitian families.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

noncomputable section

variable {K : Type*} [Field K] {S : AdelicStructure K}
  {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E)

/-- Nearly optimal bases give actual completed determinant vectors pairing to
one whose norm product is arbitrarily close to one, in every rank. -/
theorem exists_completedDeterminantPairing_eq_one_norm_mul_le (ω : S.Ω)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ (w : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E))
      (z : (S.ϕ ω).Completion ⊗[K]
        (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E))),
      completedDeterminantPairing K (S.ϕ ω).Completion E z w = 1 ∧
        ξ.determinant.norm ω w * ξ.dual.determinant.norm ω z ≤
          α⁻¹ ^ Module.finrank K E := by
  classical
  obtain ⟨b, hb⟩ := ξ.exists_completedBasis_norm_mul_dual_norm_le ω hα hα1
  let e := finCongr (Subspace.dual_finrank_eq (K := K) (V := E))
  let f (i : Fin (Module.finrank K (Module.Dual K E))) :=
    (dualBaseChangeEquiv K (S.ϕ ω).Completion E).symm (b.coord (e i))
  let w := (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm
    (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ b)
  let z := (exteriorBaseChangeEquiv K (S.ϕ ω).Completion (Module.Dual K E) _).symm
    (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ f)
  refine ⟨w, z, ?_, ?_⟩
  · rw [completedDeterminantPairing_ιMulti]
    have hm : (Matrix.of fun i j ↦ b.coord j (b i)) =
        (1 : Matrix (Fin (Module.finrank K E)) (Fin (Module.finrank K E))
          (S.ϕ ω).Completion) := by
      ext i j
      simp [Module.Basis.coord_apply, Matrix.one_apply, Finsupp.single_apply]
    simp only [f, e, Equiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      hm, Matrix.det_one]
  · have hf : (∏ i, ξ.dual.norm ω (f i)) = ∏ i,
        ξ.dual.norm ω ((dualBaseChangeEquiv K (S.ϕ ω).Completion E).symm (b.coord i)) :=
      Equiv.prod_comp e (fun i ↦ ξ.dual.norm ω
        ((dualBaseChangeEquiv K (S.ϕ ω).Completion E).symm (b.coord i)))
    calc
      ξ.determinant.norm ω w * ξ.dual.determinant.norm ω z ≤
          (∏ i, ξ.norm ω (b i)) * ∏ i, ξ.dual.norm ω (f i) :=
        mul_le_mul (ξ.determinant_norm_ιMulti_le ω b)
          (ξ.dual.determinant_norm_ιMulti_le ω f)
          (ξ.dual.determinant.norm_nonneg ω z)
          (Finset.prod_nonneg fun i _ ↦ ξ.norm_nonneg ω (b i))
      _ = ∏ i, ξ.norm ω (b i) *
          ξ.dual.norm ω ((dualBaseChangeEquiv K (S.ϕ ω).Completion E).symm (b.coord i)) := by
        rw [hf, Finset.prod_mul_distrib]
      _ ≤ ∏ _ : Fin (Module.finrank K E), α⁻¹ :=
        Finset.prod_le_prod₀ (fun i _ ↦ mul_nonneg (ξ.norm_nonneg ω _) (ξ.dual.norm_nonneg ω _))
          (fun i _ ↦ (hb i).2)
      _ = α⁻¹ ^ Module.finrank K E := by simp

/-- The product of the two actual determinant norms is bounded by the
absolute value of their canonical pairing for every norm family. -/
theorem determinant_norm_mul_dual_le_norm_pairing (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E)))
    (w : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    ξ.determinant.norm ω w * ξ.dual.determinant.norm ω z ≤
      ‖completedDeterminantPairing K (S.ϕ ω).Completion E z w‖ := by
  have hαbound (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
      ξ.determinant.norm ω w * ξ.dual.determinant.norm ω z ≤
        ‖completedDeterminantPairing K (S.ϕ ω).Completion E z w‖ *
          α⁻¹ ^ Module.finrank K E := by
    obtain ⟨w₀, z₀, hp, hn⟩ :=
      ξ.exists_completedDeterminantPairing_eq_one_norm_mul_le ω hα hα1
    have hw₀ : w₀ ≠ 0 := by
      intro h
      simp only [h, map_zero] at hp
      exact zero_ne_one hp
    have hz₀ : z₀ ≠ 0 := by
      intro h
      simp only [h, map_zero, LinearMap.zero_apply] at hp
      exact zero_ne_one hp
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one
      (show Module.finrank (S.ϕ ω).Completion
          ((S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) = 1 by
        rw [Module.finrank_baseChange]; exact determinant_finrank) hw₀ w
    obtain ⟨b, hb⟩ := exists_smul_eq_of_finrank_eq_one
      (show Module.finrank (S.ϕ ω).Completion
          ((S.ϕ ω).Completion ⊗[K]
            (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E))) = 1 by
        rw [Module.finrank_baseChange]; exact determinant_finrank) hz₀ z
    have hpair : completedDeterminantPairing K (S.ϕ ω).Completion E z w = b * a := by
      rw [← ha, ← hb]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hp, mul_one, mul_comm]
    calc
      ξ.determinant.norm ω w * ξ.dual.determinant.norm ω z =
          (‖a‖ * ‖b‖) * (ξ.determinant.norm ω w₀ * ξ.dual.determinant.norm ω z₀) := by
        rw [← ha, ← hb, ξ.determinant.norm_smul, ξ.dual.determinant.norm_smul]
        ring
      _ ≤ (‖a‖ * ‖b‖) * α⁻¹ ^ Module.finrank K E :=
        mul_le_mul_of_nonneg_left hn (mul_nonneg (_root_.norm_nonneg a) (_root_.norm_nonneg b))
      _ = ‖completedDeterminantPairing K (S.ϕ ω).Completion E z w‖ *
          α⁻¹ ^ Module.finrank K E := by rw [hpair, norm_mul, mul_comm ‖b‖ ‖a‖]
  have hlim : Filter.Tendsto (fun α : ℝ ↦
      ‖completedDeterminantPairing K (S.ϕ ω).Completion E z w‖ * α⁻¹ ^ Module.finrank K E)
      (nhdsWithin 1 (Set.Iio 1))
      (nhds ‖completedDeterminantPairing K (S.ϕ ω).Completion E z w‖) := by
    have hc : ContinuousAt (fun α : ℝ ↦
        ‖completedDeterminantPairing K (S.ϕ ω).Completion E z w‖ *
          α⁻¹ ^ Module.finrank K E) 1 :=
      continuousAt_const.mul ((continuousAt_id.inv₀ one_ne_zero).pow _)
    simpa only [inv_one, one_pow, mul_one] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (zero_lt_one : (0 : ℝ) < 1))] with α hα1 hα
  exact hαbound α hα hα1

variable [hS : S.IsArchimedeanNormalized]

/-- The canonical completed determinant pairing has exactly the product of
the determinant norms for a Hermitian family, including rank zero. -/
theorem IsHermitian.norm_completedDeterminantPairing_eq (hξ : ξ.IsHermitian)
    (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E)))
    (w : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    ‖completedDeterminantPairing K (S.ϕ ω).Completion E z w‖ =
      ξ.determinant.norm ω w * ξ.dual.determinant.norm ω z :=
  le_antisymm (hξ.norm_completedDeterminantPairing_le ξ ω z w)
    (ξ.determinant_norm_mul_dual_le_norm_pairing ω z w)

/-- The canonical map from the determinant of the dual to the dual of the
determinant preserves the actual completed norms of a Hermitian family. -/
theorem IsHermitian.determinant_dual_norm (hξ : ξ.IsHermitian) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E))) :
    ξ.dual.determinant.norm ω z = ξ.determinant.dual.norm ω
      ((determinantDualEquiv K E).toLinearMap.baseChange (S.ϕ ω).Completion z) := by
  let b := (Module.finBasisOfFinrankEq K (⋀[K]^(Module.finrank K E) E)
    determinant_finrank).baseChange (S.ϕ ω).Completion
  rw [ξ.determinant.dual_norm_eq_div_of_basis ω b]
  change ξ.dual.determinant.norm ω z =
    ‖completedDeterminantPairing K (S.ϕ ω).Completion E z (b 0)‖ /
      ξ.determinant.norm ω (b 0)
  rw [hξ.norm_completedDeterminantPairing_eq ξ ω z (b 0)]
  exact (mul_div_cancel_left₀ _ (ξ.determinant.norm_pos ω (b.ne_zero 0)).ne').symm

/-- Isometric determinant duality as an equality of actual norm families. -/
theorem IsHermitian.determinant_dual (hξ : ξ.IsHermitian) :
    ξ.dual.determinant = ξ.determinant.dual.pullback
      (determinantDualEquiv K E).toLinearMap (determinantDualEquiv K E).injective := by
  ext ω z
  exact hξ.determinant_dual_norm ξ ω z

end

end ArakelovGeometry.NormFamily
