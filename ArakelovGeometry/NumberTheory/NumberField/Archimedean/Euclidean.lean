/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Archimedean.VectorDiagonal
public import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Normalization.Hermitian
public import Mathlib.Analysis.InnerProductSpace.OfNorm

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import Mathlib.Topology.Sheaves.Init

/-!
# The Euclidean norm on the original Archimedean completed product

All coordinates are the actual prescribed completed tensor fibres. The finite
L2 norm is pulled back to the original product through the coordinate identity.
-/

@[expose] public section

noncomputable section
open NumberField
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldArchimedeanEuclidean

open NumberFieldArchimedeanVectorDiagonal AdelicStructure NormFamily

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]

/-- The usual real scalar action preserves the original completed fibre norm. -/
abbrev fibreRealNormedSpace
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) (w : InfinitePlace K) :
    letI := ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
    NormedSpace ℝ (CompletedCoefficient w ⊗[K] E) := by
  let := ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  exact
    { norm_smul_le := by
        intro r z
        change ξ.norm (normalizedInfinitePlacePoint w) (r • z) ≤
          ‖r‖ * ξ.norm (normalizedInfinitePlacePoint w) z
        rw [← IsScalarTower.algebraMap_smul (CompletedCoefficient w) r z, ξ.norm_smul]
        change ‖completedRealScalarMap w r‖ * _ ≤ ‖r‖ * _
        rw [norm_completedRealScalarMap, Real.norm_eq_abs] }

/-- The actual L2 norm, on the original coordinate product. -/
abbrev euclideanNormedAddCommGroup
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) :
    NormedAddCommGroup (CompletedVectorProduct K E) := by
  letI : ∀ w : InfinitePlace K,
      NormedAddCommGroup (CompletedCoefficient w ⊗[K] E) :=
    fun w => ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let e := (WithLp.linearEquiv 2 ℝ (CompletedVectorProduct K E)).symm
  exact NormedAddCommGroup.induced _ _ e.toLinearMap e.injective

/-- The fixed original real scalar action with the actual L2 norm. -/
abbrev euclideanNormedSpace
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) :
    letI := euclideanNormedAddCommGroup ξ
    NormedSpace ℝ (CompletedVectorProduct K E) := by
  letI : ∀ w : InfinitePlace K,
      NormedAddCommGroup (CompletedCoefficient w ⊗[K] E) :=
    fun w => ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  letI : ∀ w : InfinitePlace K, NormedSpace ℝ (CompletedCoefficient w ⊗[K] E) :=
    fun w => fibreRealNormedSpace ξ w
  exact NormedSpace.induced ℝ _ _
    (WithLp.linearEquiv 2 ℝ (CompletedVectorProduct K E)).symm.toLinearMap

theorem euclidean_norm_sq (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (z : CompletedVectorProduct K E) :
    letI := euclideanNormedAddCommGroup ξ
    ‖z‖ ^ 2 = ∑ w : InfinitePlace K, (ξ.norm (normalizedInfinitePlacePoint w) (z w)) ^ 2 := by
  let : ∀ w : InfinitePlace K,
      NormedAddCommGroup (CompletedCoefficient w ⊗[K] E) :=
    fun w => ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  exact PiLp.norm_sq_eq_of_L2 _ (WithLp.toLp 2 z)

theorem euclidean_norm (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (z : CompletedVectorProduct K E) :
    letI := euclideanNormedAddCommGroup ξ
    ‖z‖ = Real.sqrt
      (∑ w : InfinitePlace K, (ξ.norm (normalizedInfinitePlacePoint w) (z w)) ^ 2) := by
  let : ∀ w : InfinitePlace K,
      NormedAddCommGroup (CompletedCoefficient w ⊗[K] E) :=
    fun w => ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  exact PiLp.norm_eq_of_L2 (WithLp.toLp 2 z)

/-- The coordinate identity to the standard L2 product is an actual isometry. -/
def euclideanIsometry (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) :
    letI : ∀ w : InfinitePlace K,
        NormedAddCommGroup (CompletedCoefficient w ⊗[K] E) :=
      fun w => ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
    letI := euclideanNormedAddCommGroup ξ
    letI : SeminormedAddCommGroup (CompletedVectorProduct K E) :=
      (euclideanNormedAddCommGroup ξ).toSeminormedAddCommGroup
    CompletedVectorProduct K E ≃ₗᵢ[ℝ]
      PiLp 2 (fun w : InfinitePlace K => CompletedCoefficient w ⊗[K] E) := by
  let : ∀ w : InfinitePlace K,
      NormedAddCommGroup (CompletedCoefficient w ⊗[K] E) :=
    fun w => ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let := euclideanNormedAddCommGroup ξ
  letI : SeminormedAddCommGroup (CompletedVectorProduct K E) :=
    (euclideanNormedAddCommGroup ξ).toSeminormedAddCommGroup
  exact { (WithLp.linearEquiv 2 ℝ (CompletedVectorProduct K E)).symm with
    norm_map' := fun _ => rfl }

/-- Actual Hermitian fibre norms induce an inner product for the fixed real action. -/
@[instance_reducible]
def euclideanInnerProduct
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    [hξ : ξ.IsHermitian] :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    InnerProductSpace ℝ (CompletedVectorProduct K E) := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  apply InnerProductSpace.ofNorm ℝ
  intro x y
  simp only [← pow_two, euclidean_norm_sq]
  have h := (isHermitian_iff_parallelogram.mp hξ).2
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun w _ =>
    h (normalizedInfinitePlacePoint w) (normalizedInfinitePlacePoint_mem_inf w) (x w) (y w))
  simpa only [← pow_two, Finset.sum_add_distrib, ← Finset.mul_sum,
    Pi.add_apply, Pi.sub_apply] using hs

theorem euclidean_discrete_diagonalLattice [FiniteDimensional K E]
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    letI := euclideanNormedAddCommGroup ξ
    DiscreteTopology (diagonalLattice M) := by
  classical
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  rw [diagonalLattice_eq_integerSpan M hfg hspan]
  infer_instance

open scoped Classical in
theorem euclidean_isZLattice_diagonalLattice [FiniteDimensional K E]
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    letI := euclidean_discrete_diagonalLattice ξ M hfg hspan
    IsZLattice ℝ (diagonalLattice M) := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclidean_discrete_diagonalLattice ξ M hfg hspan
  simpa only [diagonalLattice_eq_integerSpan M hfg hspan] using
    (inferInstance : IsZLattice ℝ
      (Submodule.span ℤ (Set.range (diagonalLatticeBasis M hfg hspan))))

end ArakelovGeometry.NumberFieldArchimedeanEuclidean

namespace ArakelovGeometry.NormFamily

open AdelicStructure NumberFieldArchimedeanVectorDiagonal NumberFieldArchimedeanEuclidean

variable {K E : Type*} [Field K] [NumberField K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}

theorem IsDominated.pure_globalBall_euclidean_discrete (hdom : ξ.IsDominated)
    (hξ : ξ.IsUltrametricAtFinitePlaces) (hpure : ξ.IsPureAtFinitePlaces) :
    letI := euclideanNormedAddCommGroup ξ
    DiscreteTopology (diagonalLattice (ξ.globalUnitBallModule)) :=
  euclidean_discrete_diagonalLattice ξ _
    (hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure).1
    (hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure).2.2

open scoped Classical in
theorem IsDominated.pure_globalBall_euclidean_isZLattice (hdom : ξ.IsDominated)
    (hξ : ξ.IsUltrametricAtFinitePlaces) (hpure : ξ.IsPureAtFinitePlaces) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    letI := hdom.pure_globalBall_euclidean_discrete hξ hpure
    IsZLattice ℝ (diagonalLattice (ξ.globalUnitBallModule)) :=
  euclidean_isZLattice_diagonalLattice ξ _
    (hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure).1
    (hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure).2.2

end ArakelovGeometry.NormFamily
