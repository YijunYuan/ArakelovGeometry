/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberFieldArithmeticPolarVolume
public import ArakelovGeometry.NumberTheory.NumberFieldProjectiveSections
public import ArakelovGeometry.NumberTheory.NumberFieldProjectiveTraceDualGeneric

/-! # Actual polar lattice points and original trace-dual effective sections -/

@[expose] public section

noncomputable section
open NumberField Set
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldArithmeticPolarCount

open AdelicStructure NumberFieldArchimedeanVectorDiagonal NumberFieldArchimedeanEuclidean
  NumberFieldOrdinaryTraceDualNorm NumberFieldArithmeticProductBall
  NumberFieldProjectiveTraceDual NumberFieldProjectiveTraceDualGeneric
  NumberFieldCodifferentDual NumberFieldProjectiveGeneric
  NumberFieldArithmeticPolar NumberFieldArithmeticPolarVolume GeometryOfNumbers

attribute [local instance 2000] Algebra.toModule Algebra.toSMul
attribute [local instance] genericFiniteDimensional

universe u
variable {K : Type u} [Field K] [NumberField K]
  (M : Type u) [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- The original tensor diagonal followed by the actual trace isometry is a bijection
onto the actual continuous integral dual of the original diagonal lattice. -/
def traceTensorIntegralDualEquiv
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    letI := euclideanNormedAddCommGroup η
    letI := euclideanNormedSpace η
    (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) ≃
      integralDual (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
        (originalDiagonalMap (K := K) M).range := by
  let := euclideanNormedAddCommGroup η
  let := euclideanNormedSpace η
  let := euclideanInnerProduct hη
  let := ordinaryTraceDualNormedAddCommGroup η
  let := ordinaryTraceDualNormedSpace η
  let t (z : codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) :=
    ordinaryTraceDualIsometry hη (traceTensorDiagonalMap (K := K) M z)
  have ht (z) : t z ∈ integralDual (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
        (originalDiagonalMap (K := K) M).range := by
    erw [← traceTensorDiagonalMap_integralDual_image M η hη]
    exact ⟨traceTensorDiagonalMap (K := K) M z, ⟨z, rfl⟩, rfl⟩
  apply Equiv.ofBijective (fun z => ⟨t z, ht z⟩)
  constructor
  · intro z z' h
    apply traceTensorDiagonalMap_injective M
    apply (ordinaryTraceDualIsometry hη).injective
    exact congrArg Subtype.val h
  · rintro ⟨f, hf⟩
    erw [← traceTensorDiagonalMap_integralDual_image M η hη] at hf
    obtain ⟨g, ⟨z, rfl⟩, hg⟩ := hf
    exact ⟨z, Subtype.ext hg⟩

/-- The actual tensor-integral-dual bijection has its prescribed trace evaluation. -/
@[simp]
theorem traceTensorIntegralDualEquiv_apply
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (z : codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) :
    letI := euclideanNormedAddCommGroup η
    letI := euclideanNormedSpace η
    letI := ordinaryTraceDualNormedAddCommGroup η
    letI := ordinaryTraceDualNormedSpace η
    ((traceTensorIntegralDualEquiv M η hη z :
      integralDual (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
        (originalDiagonalMap (K := K) M).range) :
        StrongDual ℝ (CompletedVectorProduct K (K ⊗[𝓞 K] M))) =
      ordinaryTraceDualIsometry hη (traceTensorDiagonalMap (K := K) M z) := rfl

/-- Actual native polar membership is the sum-body condition on the original tensor
diagonal with its prescribed original generic-fibre norms. -/
theorem traceTensorIntegralDualEquiv_mem_polar_iff
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (z : codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) :
    letI := euclideanNormedAddCommGroup η
    letI := euclideanNormedSpace η
    ((traceTensorIntegralDualEquiv M η hη z :
      integralDual (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
        (originalDiagonalMap (K := K) M).range) :
        StrongDual ℝ (CompletedVectorProduct K (K ⊗[𝓞 K] M))) ∈
        StrongDual.polar ℝ (productBall η 1) ↔
      originalDiagonalMap (K := K)
        (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) z ∈
          sumBall (originalPrescribedTraceDualFamily M hη) := by
  let := euclideanNormedAddCommGroup η
  let := euclideanNormedSpace η
  let := ordinaryTraceDualNormedAddCommGroup η
  let := ordinaryTraceDualNormedSpace η
  rw [traceTensorIntegralDualEquiv_apply]
  erw [ordinaryTraceDualIsometry_mem_polar hη]
  change (∑ w : InfinitePlace K, (w.mult : ℝ) *
    η.dual.norm (normalizedInfinitePlacePoint w)
      ((1 : CompletedCoefficient w) ⊗ₜ[K] traceTensorInclusion (K := K) M z)) ≤ 1 ↔
    (∑ w : InfinitePlace K,
      (originalPrescribedTraceDualFamily M hη).norm (normalizedInfinitePlacePoint w)
        ((1 : CompletedCoefficient w) ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] z))) ≤ 1
  simp only [originalPrescribedTraceDualFamily_norm_original]

/-- Exact pointwise transport of all actual integral polar functionals to the original
codifferent tensor's actual sum-body sections. -/
def nativePolarPointsEquivTraceTensor
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    letI := euclideanNormedAddCommGroup η
    letI := euclideanNormedSpace η
    {f : integralDual (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
        (originalDiagonalMap (K := K) M).range //
      (f : StrongDual ℝ (CompletedVectorProduct K (K ⊗[𝓞 K] M))) ∈
        StrongDual.polar ℝ (productBall η 1)} ≃
      {z : codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M //
        originalDiagonalMap (K := K)
          (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) z ∈
            sumBall (originalPrescribedTraceDualFamily M hη)} := by
  let := euclideanNormedAddCommGroup η
  let := euclideanNormedSpace η
  exact ((traceTensorIntegralDualEquiv M η hη).subtypeEquiv
    (fun z => (traceTensorIntegralDualEquiv_mem_polar_iff M η hη z).symm)).symm

/-- The sum body is contained in the product body for any prescribed norm family. -/
theorem sumBall_subset_productBall
    {E : Type u} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) :
    sumBall ξ ⊆ productBall ξ 1 := by
  intro z hz w
  exact (Finset.single_le_sum (fun v _ => ξ.norm_nonneg _ (z v))
    (Finset.mem_univ w)).trans hz

/-- Every actual polar lattice point gives an effective section of the actual original
codifferent tensor, with its prescribed trace-dual norms. -/
theorem card_nativePolar_le_traceDual_effectiveSections
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    letI := euclideanNormedAddCommGroup η
    letI := euclideanNormedSpace η
    Nat.card {f : integralDual (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
        (originalDiagonalMap (K := K) M).range //
      (f : StrongDual ℝ (CompletedVectorProduct K (K ⊗[𝓞 K] M))) ∈
        StrongDual.polar ℝ (productBall η 1)} ≤
      Nat.card (effectiveSections (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)
        (originalPrescribedTraceDualFamily M hη)) := by
  let := euclideanNormedAddCommGroup η
  let := euclideanNormedSpace η
  let T := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M
  let ξ := originalPrescribedTraceDualFamily M hη
  let : Module.Finite ℤ M := Module.Finite.trans (𝓞 K) M
  let : Module.Finite ℤ T := Module.Finite.equiv (integerTensorEquiv (K := K) M).symm
  let : Module.Finite (𝓞 K) T := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) T
  let D := NumberFieldIntegralTraceDual.integralTraceDual (K := K) (E := K ⊗[𝓞 K] M)
    (NumberFieldInvertibleGeneric.genericImage (K := K) M)
  let e : T ≃ₗ[𝓞 K] D := traceTensorEquiv (K := K) M
  let : Module.Finite (𝓞 K) D := Module.Finite.equiv e
  let : Module.Projective (𝓞 K) D :=
    NumberFieldFullLattice.projective D (Submodule.FG.of_finite (N := D))
  let : Module.Projective (𝓞 K) T := Module.Projective.of_equiv e.symm
  let := (finite_effectiveSections T ξ).to_subtype
  rw [Nat.card_congr (nativePolarPointsEquivTraceTensor M η hη)]
  let j : {z : T // originalDiagonalMap (K := K) T z ∈ sumBall ξ} →
      effectiveSections T ξ := fun z => ⟨z.val, by
        erw [effectiveSections_eq_diagonal_preimage T ξ]
        exact sumBall_subset_productBall ξ z.property⟩
  apply Nat.card_le_card_of_injective j
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : effectiveSections T ξ => (z : T)) h

end ArakelovGeometry.NumberFieldArithmeticPolarCount
