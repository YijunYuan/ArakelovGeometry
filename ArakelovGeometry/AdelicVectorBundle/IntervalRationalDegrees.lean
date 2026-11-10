/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.IntervalRationalDeterminant
import ArakelovGeometry.AdelicVectorBundle.Degree
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionTower
import ArakelovGeometry.Analysis.DeterminantPairing

/-!
# Actual global determinant normalization of rational interval factors

Finite fibres consume the existing non-Archimedean determinant bound. Together
with the actual real-fibre calculation, this computes the canonical degrees of
the genuine rational interval bundles used in the tensor counterexample.
-/

open MeasureTheory
open scoped TensorProduct

noncomputable section
namespace ArakelovGeometry
open AdelicStructure

/-- Every finite fibre of a modified rational family has standard actual
determinant generator norm one, independently of its chosen real norm. -/
theorem rationalRealModifiedFamily_determinant_norm_prime_standard
    (n : ℕ) (hn : 0 < n) (p : Seminorm ℝ (Fin n → ℝ))
    (hp : ∀ x, p x = 0 ↔ x = 0) (q : Nat.Primes) :
    (rationalRealModifiedFamily n p hp).determinant.norm (.inl q)
      ((1 : (rationalAdelicStructure.ϕ (.inl q)).Completion) ⊗ₜ[ℚ]
        rationalStandardDeterminantVector n) = 1 := by
  classical
  let C := (rationalAdelicStructure.ϕ (.inl q)).Completion
  let : IsUltrametricDist C := AbsoluteValue.isUltrametricDist_completion _
    (rationalAdelicStructure_prime_mem_fin q)
  let ξ := rationalRealModifiedFamily n p hp
  let e : Fin n ≃ Fin (Module.finrank ℚ (Fin n → ℚ)) := finCongr (by simp)
  let b := (Pi.basisFun ℚ (Fin n)).reindex e
  let B := b.baseChange C
  have hB : B = ((Pi.basisFun ℚ (Fin n)).baseChange C).reindex e := by
    ext i
    simp only [B, b, Module.Basis.baseChange_apply, Module.Basis.reindex_apply]
  have hb (i : Fin (Module.finrank ℚ (Fin n → ℚ))) : ξ.norm (.inl q) (B i) ≤ 1 := by
    rw [hB, Module.Basis.reindex_apply, Module.Basis.baseChange_apply]
    exact (NormFamily.ofBasis_norm_tmul_basis (S := rationalAdelicStructure)
      (E := Fin n → ℚ) (Pi.basisFun ℚ (Fin n)) (.inl q) (1 : C) (e.symm i)).trans_le (norm_one.le)
  have hd (v : Fin (Module.finrank ℚ (Fin n → ℚ)) → C ⊗[ℚ] (Fin n → ℚ)) :
      ‖B.det v‖ ≤ ∏ i, ξ.norm (.inl q) (v i) := by
    rw [hB, Module.Basis.det_reindex, Module.Basis.det_apply]
    have h := norm_det_le_prod_of_entry_le
      (((Pi.basisFun ℚ (Fin n)).baseChange C).toMatrix (v ∘ e))
      (fun _ => (1 : ℝ)) (fun j => ξ.norm (.inl q) (v (e j))) (fun i j => ?_)
    · rw [Finset.prod_const_one, one_mul,
        e.prod_comp (fun j => ξ.norm (.inl q) (v j))] at h
      exact h
    · rw [one_mul, Module.Basis.toMatrix_apply]
      change ‖(((Pi.basisFun ℚ (Fin n)).baseChange C).repr (v (e j)) i)‖ ≤
        (NormFamily.ofBasis rationalAdelicStructure (Fin n → ℚ)
          (Pi.basisFun ℚ (Fin n))).norm (.inl q) (v (e j))
      rw [NormFamily.ofBasis_norm]
      exact norm_le_pi_norm _ i
  have hvol := NormFamily.determinant_norm_completedBasis_eq_one_of_det_bound
    ξ (by simpa using hn) (.inl q) B hb hd
  have he : ⇑B = fun i => (1 : C) ⊗ₜ[ℚ] b i := by
    ext i
    exact Module.Basis.baseChange_apply _ _ _
  rw [he, exteriorBaseChangeEquiv_symm_ιMulti_tmul, Finset.prod_const_one] at hvol
  exact hvol

/-- The actual plane determinant generator has norm one at every rational place. -/
theorem rationalIntervalPlaneFamily_determinant_norm_standard
    (ω : rationalAdelicStructure.Ω) :
    rationalIntervalPlaneFamily.determinant.norm ω
      ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ]
        rationalStandardDeterminantVector 2) = 1 := by
  cases ω with
  | inl q =>
      exact rationalRealModifiedFamily_determinant_norm_prime_standard
        2 (by decide) intervalSeminorm₂ intervalSeminorm₂_eq_zero_iff q
  | inr u =>
      cases u
      exact rationalIntervalPlaneFamily_determinant_norm_infinite_standard

/-- The actual three-space determinant generator has norm one at every rational place. -/
theorem rationalIntervalThreeFamily_determinant_norm_standard
    (ω : rationalAdelicStructure.Ω) :
    rationalIntervalThreeFamily.determinant.norm ω
      ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ]
        rationalStandardDeterminantVector 3) = 1 := by
  cases ω with
  | inl q =>
      exact rationalRealModifiedFamily_determinant_norm_prime_standard
        3 (by decide) intervalSeminorm₃ intervalSeminorm₃_eq_zero_iff q
  | inr u =>
      cases u
      exact rationalIntervalThreeFamily_determinant_norm_infinite_standard


/-- The genuine rational interval plane bundle has canonical degree zero. -/
theorem rationalIntervalPlaneBundle_degree_eq_zero :
    rationalIntervalPlaneBundle.degree (Or.inl inferInstance)
      rationalAdelicStructure_isRCLike = 0 := by
  have hn : rationalStandardDeterminantVector 2 ≠ 0 := by
    intro hz
    have h0 : rationalIntervalPlaneFamily.determinant.norm (.inr ())
        ((1 : (rationalAdelicStructure.ϕ (.inr ())).Completion) ⊗ₜ[ℚ]
          rationalStandardDeterminantVector 2) = 0 := by
      rw [hz, TensorProduct.tmul_zero, map_zero]
    exact zero_ne_one (h0.symm.trans
      (rationalIntervalPlaneFamily_determinant_norm_standard (.inr ())))
  rw [rationalIntervalPlaneBundle.degree_eq_neg_integral (Or.inl inferInstance)
    rationalAdelicStructure_isRCLike ⟨rationalStandardDeterminantVector 2, hn⟩]
  have he : (fun ω => rationalIntervalPlaneBundle.toNormFamily.determinant.logNorm
      (rationalStandardDeterminantVector 2) ω) = 0 := by
    funext ω
    change Real.log (rationalIntervalPlaneFamily.determinant.norm ω
      ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ]
        rationalStandardDeterminantVector 2)) = 0
    rw [rationalIntervalPlaneFamily_determinant_norm_standard, Real.log_one]
  rw [he]
  change -(∫ _ : rationalAdelicStructure.Ω, (0 : ℝ) ∂rationalAdelicStructure.v) = 0
  rw [integral_zero, neg_zero]


/-- The genuine rational interval three bundle has canonical degree zero. -/
theorem rationalIntervalThreeBundle_degree_eq_zero :
    rationalIntervalThreeBundle.degree (Or.inl inferInstance)
      rationalAdelicStructure_isRCLike = 0 := by
  have hn : rationalStandardDeterminantVector 3 ≠ 0 := by
    intro hz
    have h0 : rationalIntervalThreeFamily.determinant.norm (.inr ())
        ((1 : (rationalAdelicStructure.ϕ (.inr ())).Completion) ⊗ₜ[ℚ]
          rationalStandardDeterminantVector 3) = 0 := by
      rw [hz, TensorProduct.tmul_zero, map_zero]
    exact zero_ne_one (h0.symm.trans
      (rationalIntervalThreeFamily_determinant_norm_standard (.inr ())))
  rw [rationalIntervalThreeBundle.degree_eq_neg_integral (Or.inl inferInstance)
    rationalAdelicStructure_isRCLike ⟨rationalStandardDeterminantVector 3, hn⟩]
  have he : (fun ω => rationalIntervalThreeBundle.toNormFamily.determinant.logNorm
      (rationalStandardDeterminantVector 3) ω) = 0 := by
    funext ω
    change Real.log (rationalIntervalThreeFamily.determinant.norm ω
      ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ]
        rationalStandardDeterminantVector 3)) = 0
    rw [rationalIntervalThreeFamily_determinant_norm_standard, Real.log_one]
  rw [he]
  change -(∫ _ : rationalAdelicStructure.Ω, (0 : ℝ) ∂rationalAdelicStructure.v) = 0
  rw [integral_zero, neg_zero]

end ArakelovGeometry
