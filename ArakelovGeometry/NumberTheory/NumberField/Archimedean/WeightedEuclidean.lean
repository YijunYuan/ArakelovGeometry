/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Archimedean.Euclidean

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import Mathlib.Topology.Sheaves.Init

/-!
# The degree-weighted actual Archimedean Euclidean product

The original completed product has norm squared equal to the sum of the local
degree times the original fibre norm squared. Its coordinates and real action
are unchanged. The same original diagonal lattice is discrete and full.
-/

@[expose] public section

noncomputable section
open NumberField
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldArchimedeanWeightedEuclidean

open NumberFieldArchimedeanVectorDiagonal NumberFieldArchimedeanEuclidean
  AdelicStructure NormFamily

variable {K : Type*} [Field K]

/-- The actual square root of the local Archimedean degree. -/
def localWeight (w : InfinitePlace K) : ℝ := Real.sqrt (w.mult : ℝ)

theorem localWeight_pos (w : InfinitePlace K) : 0 < localWeight w :=
  Real.sqrt_pos.mpr (by exact_mod_cast (InfinitePlace.mult_pos (w := w)))

theorem localWeight_sq (w : InfinitePlace K) : localWeight w ^ 2 = (w.mult : ℝ) :=
  Real.sq_sqrt (Nat.cast_nonneg _)

@[simp]
theorem localWeight_of_real {w : InfinitePlace K} (hw : w.IsReal) : localWeight w = 1 := by
  simp only [localWeight, hw.mult_eq_one, Nat.cast_one, Real.sqrt_one]

@[simp]
theorem localWeight_of_complex {w : InfinitePlace K} (hw : w.IsComplex) :
    localWeight w = Real.sqrt 2 := by
  simp only [localWeight, hw.mult_eq_two, Nat.cast_ofNat]

variable {E : Type*} [NumberField K] [AddCommGroup E] [Module K E]

/-- The explicit coordinate scaling on the same original completed vector product. -/
def weightEquiv : CompletedVectorProduct K E ≃ₗ[ℝ] CompletedVectorProduct K E :=
  LinearEquiv.piCongrRight (fun w =>
    LinearEquiv.smulOfNeZero ℝ (CompletedCoefficient w ⊗[K] E)
      (localWeight w) (localWeight_pos w).ne')

@[simp]
theorem weightEquiv_apply (z : CompletedVectorProduct K E) (w : InfinitePlace K) :
    (weightEquiv (K := K) (E := E)) z w = localWeight w • z w := rfl

/-- The actual degree-weighted L2 norm on the original completed product. -/
abbrev weightedNormedAddCommGroup
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) :
    NormedAddCommGroup (CompletedVectorProduct K E) := by
  let := euclideanNormedAddCommGroup ξ
  exact NormedAddCommGroup.induced _ _ weightEquiv.toLinearMap weightEquiv.injective

/-- The fixed usual real action with the actual weighted norm. -/
abbrev weightedNormedSpace
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) :
    letI := weightedNormedAddCommGroup ξ
    NormedSpace ℝ (CompletedVectorProduct K E) := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  exact NormedSpace.induced ℝ _ _ weightEquiv.toLinearMap

theorem weighted_norm_sq (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (z : CompletedVectorProduct K E) :
    letI := weightedNormedAddCommGroup ξ
    ‖z‖ ^ 2 = ∑ w : InfinitePlace K,
      (w.mult : ℝ) * (ξ.norm (normalizedInfinitePlacePoint w) (z w)) ^ 2 := by
  let : ∀ w : InfinitePlace K,
      NormedAddCommGroup (CompletedCoefficient w ⊗[K] E) :=
    fun w => ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let : ∀ w : InfinitePlace K, NormedSpace ℝ (CompletedCoefficient w ⊗[K] E) :=
    fun w => fibreRealNormedSpace ξ w
  let := euclideanNormedAddCommGroup ξ
  change ‖(weightEquiv (K := K) (E := E)) z‖ ^ 2 = _
  rw [euclidean_norm_sq]
  apply Finset.sum_congr rfl
  intro w _
  change ‖(weightEquiv (K := K) (E := E)) z w‖ ^ 2 = (w.mult : ℝ) * ‖z w‖ ^ 2
  rw [weightEquiv_apply, _root_.norm_smul, Real.norm_eq_abs,
    abs_of_pos (localWeight_pos w), mul_pow, localWeight_sq]

/-- Actual Hermitian fibres give the weighted inner product on the same original vectors. -/
@[instance_reducible]
def weightedInnerProduct
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    [hξ : ξ.IsHermitian] :
    letI := weightedNormedAddCommGroup ξ
    letI := weightedNormedSpace ξ
    InnerProductSpace ℝ (CompletedVectorProduct K E) := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct (ξ := ξ)
  exact InnerProductSpace.induced weightEquiv.toLinearMap

theorem weighted_discrete_diagonalLattice [FiniteDimensional K E]
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    letI := weightedNormedAddCommGroup ξ
    DiscreteTopology (diagonalLattice M) := by
  classical
  let := weightedNormedAddCommGroup ξ
  let := weightedNormedSpace ξ
  rw [diagonalLattice_eq_integerSpan M hfg hspan]
  infer_instance

open scoped Classical in
theorem weighted_isZLattice_diagonalLattice [FiniteDimensional K E]
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    letI := weightedNormedAddCommGroup ξ
    letI := weightedNormedSpace ξ
    letI := weighted_discrete_diagonalLattice ξ M hfg hspan
    IsZLattice ℝ (diagonalLattice M) := by
  let := weightedNormedAddCommGroup ξ
  let := weightedNormedSpace ξ
  let := weighted_discrete_diagonalLattice ξ M hfg hspan
  simpa only [diagonalLattice_eq_integerSpan M hfg hspan] using
    (inferInstance : IsZLattice ℝ
      (Submodule.span ℤ (Set.range (diagonalLatticeBasis M hfg hspan))))

end ArakelovGeometry.NumberFieldArchimedeanWeightedEuclidean

namespace ArakelovGeometry.NormFamily

open AdelicStructure NumberFieldArchimedeanVectorDiagonal
  NumberFieldArchimedeanWeightedEuclidean

variable {K E : Type*} [Field K] [NumberField K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}

theorem IsDominated.pure_globalBall_weighted_discrete (hdom : ξ.IsDominated)
    (hξ : ξ.IsUltrametricAtFinitePlaces) (hpure : ξ.IsPureAtFinitePlaces) :
    letI := weightedNormedAddCommGroup ξ
    DiscreteTopology (diagonalLattice (ξ.globalUnitBallModule)) :=
  weighted_discrete_diagonalLattice ξ _
    (hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure).1
    (hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure).2.2

open scoped Classical in
theorem IsDominated.pure_globalBall_weighted_isZLattice (hdom : ξ.IsDominated)
    (hξ : ξ.IsUltrametricAtFinitePlaces) (hpure : ξ.IsPureAtFinitePlaces) :
    letI := weightedNormedAddCommGroup ξ
    letI := weightedNormedSpace ξ
    letI := hdom.pure_globalBall_weighted_discrete hξ hpure
    IsZLattice ℝ (diagonalLattice (ξ.globalUnitBallModule)) :=
  weighted_isZLattice_diagonalLattice ξ _
    (hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure).1
    (hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure).2.2

end ArakelovGeometry.NormFamily
