/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.LinearAlgebra.Filtration.Pairing
public import Mathlib.LinearAlgebra.Determinant

/-!
# Determinant weights of actual quotient filtrations

The finite maximum is derived from the image filtration. Its support consists
of the nonzero determinant coordinates of the given linear quotient.
-/

@[expose] public section

open Module
open scoped BigOperators

namespace Submodule

variable {K E Q ι κ : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup Q] [Module K Q]
  [Finite ι] [Fintype κ] [DecidableEq κ]

/-- Nonvanishing of a top determinant coordinate is independent of the target basis. -/
theorem basis_det_ne_zero_iff (c d : Basis κ K Q) (v : κ → Q) :
    c.det v ≠ 0 ↔ d.det v ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← c.is_basis_iff_det,
    d.is_basis_iff_det, isUnit_iff_ne_zero]

/-- A nonzero determinant of vectors in prescribed cuts bounds the sum of their levels. -/
theorem sum_le_sum_weights_of_det_ne_zero (c : Basis κ K Q) (d w : κ → ℝ)
    (v : κ → Q) (hv : ∀ k, v k ∈ span K (c '' {i | w k ≤ d i}))
    (hdet : c.det v ≠ 0) : ∑ k, w k ≤ ∑ k, d k := by
  classical
  rw [c.det_apply, Matrix.det_apply] at hdet
  obtain ⟨σ, _, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
  have hp : (∏ i, c.repr (v i) (σ i)) ≠ 0 := by
    intro hp
    apply hσ
    simp only [Basis.toMatrix_apply, hp, smul_zero]
  have hle (k : κ) : w k ≤ d (σ k) := by
    apply (c.mem_span_image.mp (hv k))
    exact Finsupp.mem_support_iff.mpr
      ((Finset.prod_ne_zero_iff.mp hp) k (Finset.mem_univ k))
  calc
    ∑ k, w k ≤ ∑ k, d (σ k) := Finset.sum_le_sum fun k _ ↦ hle k
    _ = ∑ k, d k := Equiv.sum_comp σ d

/-- Expanding lifts of a target basis produces an actual nonzero determinant
coordinate whose source weights dominate the lifted levels. -/
theorem exists_det_ne_zero_of_weighted_lifts (b : Basis ι K E) (c : Basis κ K Q)
    (q : E →ₗ[K] Q) (w : ι → ℝ) (d : κ → ℝ) (u : κ → E)
    (hu : ∀ k, q (u k) = c k)
    (hw : ∀ k, u k ∈ span K (b '' {i | d k ≤ w i})) :
    ∃ σ : κ → ι, c.det (fun k ↦ q (b (σ k))) ≠ 0 ∧
      ∑ k, d k ≤ ∑ k, w (σ k) := by
  classical
  let := Fintype.ofFinite ι
  have he : c.det (fun k ↦ q (u k)) =
      ∑ σ : κ → ι, (∏ k, b.repr (u k) (σ k)) * c.det (fun k ↦ q (b (σ k))) := by
    calc
      c.det (fun k ↦ q (u k)) =
          c.det.toMultilinearMap (fun k ↦ ∑ i, b.repr (u k) i • q (b i)) := by
        change c.det _ = c.det _
        congr 1
        funext k
        simpa only [map_sum, map_smul] using congrArg q (b.sum_repr (u k)).symm
      _ = _ := by
        rw [MultilinearMap.map_sum]
        apply Finset.sum_congr rfl
        intro σ _
        rw [MultilinearMap.map_smul_univ]
        rfl
  have hn : (∑ σ : κ → ι,
      (∏ k, b.repr (u k) (σ k)) * c.det (fun k ↦ q (b (σ k)))) ≠ 0 := by
    rw [← he]
    simpa only [hu] using (show c.det c ≠ 0 by rw [c.det_self]; exact one_ne_zero)
  obtain ⟨σ, _, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  obtain ⟨hp, hd⟩ := mul_ne_zero_iff.mp hσ
  refine ⟨σ, hd, Finset.sum_le_sum fun k _ ↦ ?_⟩
  apply (b.mem_span_image.mp (hw k))
  exact Finsupp.mem_support_iff.mpr
    ((Finset.prod_ne_zero_iff.mp hp) k (Finset.mem_univ k))

/-- The actual nonzero determinant coordinates of a linear quotient. The target
basis only identifies its determinant line with the scalar field. -/
noncomputable def quotientDeterminantSupport (b : Basis ι K E) (c : Basis κ K Q)
    (q : E →ₗ[K] Q) : Finset (κ → ι) := by
  classical
  let := Fintype.ofFinite ι
  exact Finset.univ.filter fun σ ↦ c.det (fun k ↦ q (b (σ k))) ≠ 0

@[simp]
theorem mem_quotientDeterminantSupport (b : Basis ι K E) (c : Basis κ K Q)
    (q : E →ₗ[K] Q) (σ : κ → ι) :
    σ ∈ quotientDeterminantSupport b c q ↔ c.det (fun k ↦ q (b (σ k))) ≠ 0 := by
  classical
  simp [quotientDeterminantSupport]

/-- Changing the generator of the determinant line does not change support. -/
theorem quotientDeterminantSupport_basis_independent (b : Basis ι K E)
    (c d : Basis κ K Q) (q : E →ₗ[K] Q) :
    quotientDeterminantSupport b c q = quotientDeterminantSupport b d q := by
  ext σ
  simp only [mem_quotientDeterminantSupport, basis_det_ne_zero_iff c d]

/-- The maximum determinant weight is attained and equals the sum of the
actual quotient weights, for any basis adapted to the image filtration. -/
theorem exists_maximal_quotient_weight_of_adapted (b : Basis ι K E)
    (c : Basis κ K Q) (q : E →ₗ[K] Q) (w : ι → ℝ) (d : κ → ℝ)
    (hc : ∀ t, (span K (b '' {i | t ≤ w i})).map q =
      span K (c '' {k | t ≤ d k})) :
    ∃ σ ∈ quotientDeterminantSupport b c q,
      (∑ k, w (σ k)) = ∑ k, d k ∧
      ∀ τ ∈ quotientDeterminantSupport b c q, (∑ k, w (τ k)) ≤ ∑ k, d k := by
  classical
  have hupper (τ : κ → ι) (hτ : τ ∈ quotientDeterminantSupport b c q) :
      (∑ k, w (τ k)) ≤ ∑ k, d k := by
    apply sum_le_sum_weights_of_det_ne_zero c d (fun k ↦ w (τ k))
      (fun k ↦ q (b (τ k))) _ ((mem_quotientDeterminantSupport b c q τ).mp hτ)
    intro k
    rw [← hc]
    exact mem_map.mpr ⟨b (τ k), subset_span ⟨τ k, by simp, rfl⟩, rfl⟩
  have hlift (k : κ) : ∃ u : E,
      u ∈ span K (b '' {i | d k ≤ w i}) ∧ q u = c k := by
    apply mem_map.mp
    rw [hc]
    exact subset_span ⟨k, by simp, rfl⟩
  choose u hw hu using hlift
  obtain ⟨σ, hσ, hle⟩ := exists_det_ne_zero_of_weighted_lifts b c q w d u hu hw
  have hs : σ ∈ quotientDeterminantSupport b c q :=
    (mem_quotientDeterminantSupport b c q σ).mpr hσ
  exact ⟨σ, hs, le_antisymm (hupper σ hs) hle, hupper⟩

end Submodule
