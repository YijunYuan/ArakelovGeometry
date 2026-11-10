/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.IntervalRationalNorms
import ArakelovGeometry.AdelicVectorBundle.Determinant
import ArakelovGeometry.Analysis.IntervalDeterminant

/-!
# Actual completed determinant contraction for the rational interval factors

The actual real completion and its coordinates carry the all-column interval
bounds to the original completed fibres. A unit-volume criterion consumes an
all-tuple determinant contraction directly, without Hermitian hypotheses.
-/

open scoped TensorProduct

noncomputable section
namespace ArakelovGeometry
namespace NormFamily

/-- An actual completed unit basis has determinant volume one when its
all-tuple determinant functional contracts the product of the given norms. -/
theorem determinant_norm_completedBasis_eq_one_of_det_bound
    {K E : Type*} [Field K] {S : AdelicStructure K}
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (ξ : NormFamily S E) (hr : 0 < Module.finrank K E) (ω : S.Ω)
    (b : Module.Basis (Fin (Module.finrank K E)) (S.ϕ ω).Completion
      ((S.ϕ ω).Completion ⊗[K] E))
    (hb : ∀ i, ξ.norm ω (b i) ≤ 1)
    (hd : ∀ v, ‖b.det v‖ ≤ ∏ i, ξ.norm ω (v i)) :
    ξ.determinant.norm ω
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm
        (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ b)) = 1 := by
  classical
  apply le_antisymm
  · refine (ξ.determinant_norm_ιMulti_le ω b).trans ?_
    calc
      _ ≤ ∏ _ : Fin (Module.finrank K E), (1 : ℝ) :=
        Finset.prod_le_prod (fun i _ => ξ.norm_nonneg ω (b i)) (fun i _ => hb i)
      _ = 1 := by simp
  rw [ξ.determinant_norm_eq_sInf_ιMulti hr]
  refine le_csInf ?_ ?_
  · exact ⟨∏ i, ξ.norm ω (b i), b, rfl, rfl⟩
  rintro _ ⟨v, hv, rfl⟩
  have hw := (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm.injective hv
  have he := congrArg (_root_.exteriorPower.alternatingMapLinearEquiv b.det) hw
  have hdet : b.det v = 1 := by
    simpa only [_root_.exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      Module.Basis.det_self] using he
  simpa only [hdet, norm_one] using hd v

end NormFamily

/-- Applying the actual scalar isomorphism to a completed determinant equals
formation of the determinant of the real coordinate tuple. -/
theorem rationalRealCompletedCoordinates_det (n : ℕ)
    (v : Fin n → Rat.AbsoluteValue.real.Completion ⊗[ℚ] (Fin n → ℚ)) :
    rationalRealCompletionEquiv
      (((Pi.basisFun ℚ (Fin n)).baseChange Rat.AbsoluteValue.real.Completion).det v) =
      (Pi.basisFun ℝ (Fin n)).det (fun i => rationalRealCompletedCoordinates n (v i)) := by
  rw [Module.Basis.det_apply, Pi.basisFun_det_apply]
  rw [rationalRealCompletionEquiv.map_det]
  calc
    _ = (Matrix.of (fun i => rationalRealCompletedCoordinates n (v i))).transpose.det := by
      congr 1
    _ = _ := Matrix.det_transpose _

/-- Every tuple in the literal real completed plane fibre satisfies the
interval determinant contraction. -/
theorem rationalIntervalPlaneFamily_completed_det_le
    (v : Fin 2 → Rat.AbsoluteValue.real.Completion ⊗[ℚ] (Fin 2 → ℚ)) :
    ‖((Pi.basisFun ℚ (Fin 2)).baseChange Rat.AbsoluteValue.real.Completion).det v‖ ≤
      ∏ i, rationalIntervalPlaneFamily.norm (.inr ()) (v i) := by
  rw [← rationalRealCompletionEquiv_norm, rationalRealCompletedCoordinates_det,
    Pi.basisFun_det_apply, Real.norm_eq_abs]
  change |(Matrix.of (fun i => rationalRealCompletedCoordinates 2 (v i))).det| ≤
    ∏ i, intervalSeminorm₂ (rationalRealCompletedCoordinates 2 (v i))
  simpa only [Matrix.det_transpose, Matrix.transpose_apply, Matrix.of_apply] using
    abs_det_le_prod_intervalSeminorm₂
      (Matrix.of (fun i => rationalRealCompletedCoordinates 2 (v i))).transpose

/-- Every tuple in the literal real completed three-dimensional fibre
satisfies the interval determinant contraction, including zero entries. -/
theorem rationalIntervalThreeFamily_completed_det_le
    (v : Fin 3 → Rat.AbsoluteValue.real.Completion ⊗[ℚ] (Fin 3 → ℚ)) :
    ‖((Pi.basisFun ℚ (Fin 3)).baseChange Rat.AbsoluteValue.real.Completion).det v‖ ≤
      ∏ i, rationalIntervalThreeFamily.norm (.inr ()) (v i) := by
  rw [← rationalRealCompletionEquiv_norm, rationalRealCompletedCoordinates_det,
    Pi.basisFun_det_apply, Real.norm_eq_abs]
  change |(Matrix.of (fun i => rationalRealCompletedCoordinates 3 (v i))).det| ≤
    ∏ i, intervalSeminorm₃ (rationalRealCompletedCoordinates 3 (v i))
  simpa only [Matrix.det_transpose, Matrix.transpose_apply, Matrix.of_apply] using
    abs_det_le_prod_intervalSeminorm₃
      (Matrix.of (fun i => rationalRealCompletedCoordinates 3 (v i))).transpose


/-- The top wedge of the standard rational coordinate basis, reindexed by
its actual rank; the empty determinant vector is included. -/
def rationalStandardDeterminantVector (n : ℕ) :
    ⋀[ℚ]^(Module.finrank ℚ (Fin n → ℚ)) (Fin n → ℚ) :=
  exteriorPower.ιMulti ℚ _
    ((Pi.basisFun ℚ (Fin n)).reindex (finCongr (by simp)))

/-- A real norm with a unit standard basis and all-column determinant
contraction gives actual infinite determinant length one on the rational generator. -/
theorem rationalRealModifiedFamily_determinant_norm_infinite_standard
    (n : ℕ) (hn : 0 < n) (p : Seminorm ℝ (Fin n → ℝ))
    (hp : ∀ x, p x = 0 ↔ x = 0)
    (hunit : ∀ i, p (Pi.basisFun ℝ (Fin n) i) = 1)
    (hdet : ∀ A : Matrix (Fin n) (Fin n) ℝ,
      |A.det| ≤ ∏ j, p (fun i => A i j)) :
    (rationalRealModifiedFamily n p hp).determinant.norm (.inr ())
      ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ]
        rationalStandardDeterminantVector n) = 1 := by
  classical
  let e : Fin n ≃ Fin (Module.finrank ℚ (Fin n → ℚ)) := finCongr (by simp)
  let b := (Pi.basisFun ℚ (Fin n)).reindex e
  let B := b.baseChange Rat.AbsoluteValue.real.Completion
  have hB : B = ((Pi.basisFun ℚ (Fin n)).baseChange
      Rat.AbsoluteValue.real.Completion).reindex e := by
    ext i
    simp only [B, b, Module.Basis.baseChange_apply, Module.Basis.reindex_apply]
  have hb (i : Fin (Module.finrank ℚ (Fin n → ℚ))) :
      (rationalRealModifiedFamily n p hp).norm (.inr ()) (B i) ≤ 1 := by
    rw [hB, Module.Basis.reindex_apply, Module.Basis.baseChange_apply,
      rationalRealModifiedFamily_norm_infinite, rationalRealCompletedCoordinates_rational]
    have he : (fun j => ((Pi.basisFun ℚ (Fin n) (e.symm i)) j : ℝ)) =
        Pi.basisFun ℝ (Fin n) (e.symm i) := by
      ext j
      simp only [Pi.basisFun_apply, Pi.single_apply]
      split_ifs <;> norm_num
    rw [he, hunit]
  have hd (v : Fin (Module.finrank ℚ (Fin n → ℚ)) →
      Rat.AbsoluteValue.real.Completion ⊗[ℚ] (Fin n → ℚ)) :
      ‖B.det v‖ ≤ ∏ i, (rationalRealModifiedFamily n p hp).norm (.inr ()) (v i) := by
    rw [hB, Module.Basis.det_reindex, ← rationalRealCompletionEquiv_norm,
      rationalRealCompletedCoordinates_det, Pi.basisFun_det_apply, Real.norm_eq_abs]
    have h := hdet (Matrix.of (fun i => rationalRealCompletedCoordinates n (v (e i)))).transpose
    simp only [Matrix.det_transpose, Matrix.transpose_apply, Matrix.of_apply] at h
    change |(Matrix.of (fun i => rationalRealCompletedCoordinates n (v (e i)))).det| ≤
      ∏ j, p (rationalRealCompletedCoordinates n (v (e j))) at h
    rw [e.prod_comp (fun j => p (rationalRealCompletedCoordinates n (v j)))] at h
    exact h
  have hvol := NormFamily.determinant_norm_completedBasis_eq_one_of_det_bound
    (rationalRealModifiedFamily n p hp) (by simpa using hn) (.inr ()) B hb hd
  have he : ⇑B = fun i => (1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ] b i := by
    ext i
    exact Module.Basis.baseChange_apply _ _ _
  change (rationalRealModifiedFamily n p hp).determinant.norm (.inr ())
    ((exteriorBaseChangeEquiv ℚ Rat.AbsoluteValue.real.Completion (Fin n → ℚ) _).symm
      (exteriorPower.ιMulti Rat.AbsoluteValue.real.Completion _ B)) = 1 at hvol
  rw [he, exteriorBaseChangeEquiv_symm_ιMulti_tmul, Finset.prod_const_one] at hvol
  exact hvol

/-- The actual infinite determinant length of the rational interval plane
standard generator is one. -/
theorem rationalIntervalPlaneFamily_determinant_norm_infinite_standard :
    rationalIntervalPlaneFamily.determinant.norm (.inr ())
      ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ]
        rationalStandardDeterminantVector 2) = 1 := by
  apply rationalRealModifiedFamily_determinant_norm_infinite_standard
    2 (by decide) intervalSeminorm₂ intervalSeminorm₂_eq_zero_iff
  · intro i
    fin_cases i <;>
      norm_num [intervalSeminorm₂_apply, Pi.basisFun_apply, Pi.single_apply, Fin.ext_iff]
  · exact abs_det_le_prod_intervalSeminorm₂

/-- The actual infinite determinant length of the rational interval
three-space standard generator is one. -/
theorem rationalIntervalThreeFamily_determinant_norm_infinite_standard :
    rationalIntervalThreeFamily.determinant.norm (.inr ())
      ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ]
        rationalStandardDeterminantVector 3) = 1 := by
  apply rationalRealModifiedFamily_determinant_norm_infinite_standard
    3 (by decide) intervalSeminorm₃ intervalSeminorm₃_eq_zero_iff
  · intro i
    fin_cases i <;>
      norm_num [intervalSeminorm₃_apply, Pi.basisFun_apply, Pi.single_apply, Fin.ext_iff]
  · exact abs_det_le_prod_intervalSeminorm₃

end ArakelovGeometry
