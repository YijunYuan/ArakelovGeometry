/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberFieldArchimedeanWeightedEuclidean
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The actual Archimedean coordinate-weight Jacobian

The real dimension and determinant calculations use the literal completed
coefficients and tensor fibres with their already prescribed real action.
-/

@[expose] public section

noncomputable section
open NumberField MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldArchimedeanWeightedJacobian

open NumberFieldArchimedeanVectorDiagonal NumberFieldArchimedeanDiagonal
  NumberFieldArchimedeanWeightedEuclidean NumberFieldArchimedeanEuclidean AdelicStructure

variable {K : Type*} [Field K] [NumberField K]

/-- The actual real completion equivalence respects the fixed real action. -/
def realCoefficientAlgEquiv {w : InfinitePlace K} (hw : w.IsReal) :
    CompletedCoefficient w ≃ₐ[ℝ] ℝ :=
  { normalizedRealCompletionEquiv hw with
    commutes' := by
      intro r
      change normalizedRealCompletionEquiv hw (completedRealScalarMap w r) = r
      simp [completedRealScalarMap, hw] }

/-- The actual complex completion equivalence respects the fixed real action. -/
def complexCoefficientAlgEquiv {w : InfinitePlace K} (hw : w.IsComplex) :
    CompletedCoefficient w ≃ₐ[ℝ] ℂ :=
  { normalizedComplexCompletionEquiv hw with
    commutes' := by
      intro r
      change normalizedComplexCompletionEquiv hw (completedRealScalarMap w r) = (r : ℂ)
      simp [completedRealScalarMap, InfinitePlace.not_isReal_iff_isComplex.mpr hw] }

instance finite_completedCoefficientReal (w : InfinitePlace K) :
    FiniteDimensional ℝ (CompletedCoefficient w) := by
  classical
  by_cases hw : w.IsReal
  · exact (realCoefficientAlgEquiv hw).symm.toLinearEquiv.finiteDimensional
  · exact (complexCoefficientAlgEquiv
      (InfinitePlace.not_isReal_iff_isComplex.mp hw)).symm.toLinearEquiv.finiteDimensional

theorem completedCoefficient_real_finrank (w : InfinitePlace K) :
    Module.finrank ℝ (CompletedCoefficient w) = w.mult := by
  classical
  by_cases hw : w.IsReal
  · rw [(realCoefficientAlgEquiv hw).toLinearEquiv.finrank_eq,
      Module.finrank_self, hw.mult_eq_one]
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    rw [(complexCoefficientAlgEquiv hc).toLinearEquiv.finrank_eq,
      Complex.finrank_real_complex, hc.mult_eq_two]

variable {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

instance finite_completedFibreReal (w : InfinitePlace K) :
    FiniteDimensional ℝ (CompletedCoefficient w ⊗[K] E) :=
  Module.Finite.trans (CompletedCoefficient w) (CompletedCoefficient w ⊗[K] E)

theorem completedFibre_real_finrank (w : InfinitePlace K) :
    Module.finrank ℝ (CompletedCoefficient w ⊗[K] E) = w.mult * Module.finrank K E := by
  rw [← Module.finrank_mul_finrank ℝ (CompletedCoefficient w)
    (CompletedCoefficient w ⊗[K] E), completedCoefficient_real_finrank,
    Module.finrank_baseChange]

omit [FiniteDimensional K E] in
theorem weightEquiv_piBasis {ι : InfinitePlace K → Type*}
    (b : ∀ w : InfinitePlace K, Module.Basis (ι w) ℝ (CompletedCoefficient w ⊗[K] E))
    (i : (w : InfinitePlace K) × ι w) :
    weightEquiv (K := K) (E := E) (Pi.basis b i) = localWeight i.1 • Pi.basis b i := by
  classical
  ext w
  rw [weightEquiv_apply, Pi.basis_apply, Pi.smul_apply]
  by_cases h : w = i.1
  · subst w
    simp
  · rw [Pi.single_eq_of_ne h]
    exact (smul_zero (A := CompletedCoefficient w ⊗[K] E) (localWeight w)).trans
      (smul_zero (A := CompletedCoefficient w ⊗[K] E) (localWeight i.1)).symm

theorem det_weightEquiv_product :
    LinearMap.det (weightEquiv (K := K) (E := E)).toLinearMap =
      ∏ w : InfinitePlace K, localWeight w ^ (w.mult * Module.finrank K E) := by
  classical
  let b := Pi.basis (fun w : InfinitePlace K =>
    Module.finBasis ℝ (CompletedCoefficient w ⊗[K] E))
  have hm : LinearMap.toMatrix b b (weightEquiv (K := K) (E := E)).toLinearMap =
      Matrix.diagonal (fun i => localWeight i.1) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change b.repr (weightEquiv (K := K) (E := E) (b j)) i = _
    rw [weightEquiv_piBasis, map_smul]
    by_cases hij : i = j
    · subst j
      simp [b, Pi.basis_repr_single]
    · simp [b, Pi.basis_repr_single, hij]
  rw [← LinearMap.det_toMatrix b, hm, Matrix.det_diagonal, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro w _
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    completedFibre_real_finrank]

open scoped Classical in
theorem det_weightEquiv :
    LinearMap.det (weightEquiv (K := K) (E := E)).toLinearMap =
      (2 : ℝ) ^ (Fintype.card {w : InfinitePlace K // w.IsComplex} * Module.finrank K E) := by
  classical
  rw [det_weightEquiv_product]
  have hfac (w : InfinitePlace K) :
      localWeight w ^ (w.mult * Module.finrank K E) =
        if w.IsComplex then (2 : ℝ) ^ Module.finrank K E else 1 := by
    by_cases hc : w.IsComplex
    · rw [ite_eq_left hc, localWeight_of_complex hc, hc.mult_eq_two, pow_mul]
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    · have hr := InfinitePlace.not_isComplex_iff_isReal.mp hc
      rw [ite_eq_right hc, localWeight_of_real hr, one_pow]
  simp only [hfac]
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const, ← Fintype.card_subtype, ← pow_mul, Nat.mul_comm]

theorem det_weightEquiv_pos :
    0 < LinearMap.det (weightEquiv (K := K) (E := E)).toLinearMap := by
  rw [det_weightEquiv]
  positivity

open scoped Classical in
theorem volume_weightEquiv_image
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (B : Set (CompletedVectorProduct K E)) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    letI := euclideanInnerProduct hξ
    letI : MeasurableSpace (CompletedVectorProduct K E) := borel _
    letI : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
    letI := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
    volume (weightEquiv (K := K) (E := E) '' B) =
      ENNReal.ofReal ((2 : ℝ) ^
        (Fintype.card {w : InfinitePlace K // w.IsComplex} * Module.finrank K E)) *
        volume B := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct hξ
  let : MeasurableSpace (CompletedVectorProduct K E) := borel _
  let : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
  have h := Measure.addHaar_image_linearMap volume
    (weightEquiv (K := K) (E := E)).toLinearMap B
  rw [det_weightEquiv, abs_of_pos (by positivity : (0 : ℝ) < 2 ^
    (Fintype.card {w : InfinitePlace K // w.IsComplex} * Module.finrank K E))] at h
  exact h

end ArakelovGeometry.NumberFieldArchimedeanWeightedJacobian
