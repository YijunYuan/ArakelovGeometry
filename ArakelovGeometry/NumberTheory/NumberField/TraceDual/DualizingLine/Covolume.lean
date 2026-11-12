/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Covolume.PrincipalScalar
public import ArakelovGeometry.NumberTheory.NumberField.TraceDual.DualizingLine.Basic

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Hermitian.Line
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Line
import ArakelovGeometry.NumberTheory.NumberField.Minkowski.Radius
import Mathlib.Topology.Sheaves.Init

/-! # Actual scalar dualizing-line metric and reciprocal ordinary covolume -/

@[expose] public section

noncomputable section
open NumberField MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldTraceDualizingLineCovolume

open AdelicStructure NumberFieldCodifferentDual NumberFieldTraceDualizingLine
  NumberFieldIntegralTraceDual NumberFieldArchimedeanVectorDiagonal
  NumberFieldArchimedeanEuclidean NumberFieldArchimedeanCovolume
  NumberFieldOrdinaryTraceDualNorm NumberFieldTraceDualCovolume
  NumberFieldPrincipalBasisScalarCovolume NormFamily
attribute [local instance 2000] Algebra.toModule Algebra.toSMul
attribute [local instance 3000] AddCommGroup.toIntModule

variable (K : Type*) [Field K] [NumberField K]

/-- The basis consisting of one for the scalar line. -/
abbrev scalarBasis : Module.Basis (Fin 1) K K := Module.Basis.singleton (Fin 1) K

/-- The norm family induced by the canonical scalar-line basis. -/
abbrev scalarFamily := basisFamily (scalarBasis K)

/-- Canonical scalar evaluation duality, the inverse of evaluation at one. -/
def scalarDualEquiv : K ≃ₗ[K] Module.Dual K K :=
  (LinearMap.ringLmapEquivSelf K K K).symm

omit [NumberField K] in
@[simp]
theorem scalarDualEquiv_apply (a x : K) : scalarDualEquiv K a x = a * x := by
  change x * a = a * x
  exact mul_comm x a

/-- Literal scalar codifferent versus intrinsic trace-integral dual, through the
canonical evaluation equivalence. -/
theorem scalarDualEquiv_codifferent_image :
    (codifferentModule K).map ((scalarDualEquiv K).toLinearMap.restrictScalars (𝓞 K)) =
      integralTraceDual (principalModule (scalarBasis K)) := by
  ext f
  constructor
  · rintro ⟨a, ha, rfl⟩
    apply (mem_integralTraceDual_iff_codifferent _ _).mpr
    intro x
    obtain ⟨r, hr⟩ := (mem_principalModule (scalarBasis K) (x : K)).mp x.property 0
    have hr' : (r : K) = (x : K) := by simpa [scalarBasis] using hr
    change scalarDualEquiv K a (x : K) ∈ codifferentModule K
    rw [scalarDualEquiv_apply, ← hr', mul_comm]
    exact (codifferentModule K).smul_mem r ha
  · intro hf
    let oneL : principalModule (scalarBasis K) :=
      ⟨1, Submodule.subset_span ⟨0, by simp [scalarBasis]⟩⟩
    have ha : f 1 ∈ codifferentModule K := by
      exact (mem_integralTraceDual_iff_codifferent _ _).mp hf oneL
    refine ⟨f 1, ha, ?_⟩
    exact (LinearMap.ringLmapEquivSelf K K K).symm_apply_apply f

private theorem scalarFamily_norm_one (w : InfinitePlace K) :
    (scalarFamily K).norm (normalizedInfinitePlacePoint w)
      ((1 : CompletedCoefficient w) ⊗ₜ[K] (1 : K)) = 1 := by
  rw [ofBasisHermitian_norm_of_infinite (scalarBasis K) _
    (normalizedInfinitePlacePoint_mem_inf w)]
  simp [basis_equivFun_one_tmul, scalarBasis]

/-- Scalar operator dual norm of multiplication by a, in the actual infinite fibre. -/
theorem scalar_dual_norm_tmul (w : InfinitePlace K) (a : CompletedCoefficient w) :
    (scalarFamily K).dual.norm (normalizedInfinitePlacePoint w)
      (a ⊗ₜ[K] scalarDualEquiv K 1) = ‖a‖ := by
  have h := (scalarFamily K).dual_norm_rational_eq_div (Module.finrank_self K)
    (one_ne_zero : (1 : K) ≠ 0) (scalarDualEquiv K 1) (normalizedInfinitePlacePoint w)
  rw [scalarFamily_norm_one] at h
  simp only [scalarDualEquiv_apply, one_mul, map_one, div_one] at h
  have hs := (scalarFamily K).dual.norm_smul (normalizedInfinitePlacePoint w) a
    ((1 : CompletedCoefficient w) ⊗ₜ[K] scalarDualEquiv K 1)
  simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, h] using hs

/-- Canonical scalar evaluation after actual completion at every infinite place. -/
def scalarCompletedDualEquiv : CompletedVectorProduct K K ≃ₗ[ℝ]
    CompletedVectorProduct K (Module.Dual K K) :=
  LinearEquiv.piCongrRight (fun w =>
    (LinearEquiv.baseChange K (CompletedCoefficient w) _ _ (scalarDualEquiv K)).restrictScalars ℝ)

/-- Actual prescribed local dualizing-line norm, through scalar evaluation. -/
theorem dualizingLine_norm_scalarDual (w : InfinitePlace K)
    (z : CompletedCoefficient w ⊗[K] K) :
    (dualizingLine K).norm (normalizedInfinitePlacePoint w) z =
      (w.mult : ℝ) * (scalarFamily K).dual.norm (normalizedInfinitePlacePoint w)
        (LinearEquiv.baseChange K (CompletedCoefficient w) _ _ (scalarDualEquiv K) z) := by
  let a := (TensorProduct.rid K (CompletedCoefficient w)) z
  have hz : z = a ⊗ₜ[K] (1 : K) := by
    simpa only [TensorProduct.rid_symm_apply] using
      ((TensorProduct.rid K (CompletedCoefficient w)).symm_apply_apply z).symm
  rw [hz, LinearEquiv.baseChange_tmul, dualizingLine_norm_infinite,
    scalar_dual_norm_tmul]

/-- The actual ordinary dualizing-line product is isometric to the independently
prescribed ordinary trace-dual product of the scalar primal line. -/
def dualizingLineOrdinaryTraceDualIsometry :
    letI := euclideanNormedAddCommGroup (dualizingLine K).toNormFamily
    letI := euclideanNormedSpace (dualizingLine K).toNormFamily
    letI := ordinaryTraceDualNormedAddCommGroup (scalarFamily K)
    letI := ordinaryTraceDualNormedSpace (scalarFamily K)
    CompletedVectorProduct K K ≃ₗᵢ[ℝ] CompletedVectorProduct K (Module.Dual K K) := by
  let := euclideanNormedAddCommGroup (dualizingLine K).toNormFamily
  let := euclideanNormedSpace (dualizingLine K).toNormFamily
  let := ordinaryTraceDualNormedAddCommGroup (scalarFamily K)
  let := ordinaryTraceDualNormedSpace (scalarFamily K)
  refine { scalarCompletedDualEquiv K with norm_map' := ?_ }
  intro z
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [ordinaryTraceDual_norm_sq, euclidean_norm_sq]
  apply Finset.sum_congr rfl
  intro w _
  exact congrArg (fun x : ℝ => x ^ 2) (dualizingLine_norm_scalarDual K w (z w)).symm

/-- Scalar evaluation commutes with the literal original rational diagonal. -/
theorem scalarCompletedDualEquiv_diagonal (a : K) :
    scalarCompletedDualEquiv K (vectorDiagonalMap (K := K) a) =
      vectorDiagonalMap (K := K) (scalarDualEquiv K a) := by
  ext w
  change (LinearEquiv.baseChange K (CompletedCoefficient w) _ _ (scalarDualEquiv K))
    (1 ⊗ₜ[K] a) = 1 ⊗ₜ[K] scalarDualEquiv K a
  rw [LinearEquiv.baseChange_tmul]

/-- The actual codifferent diagonal maps exactly to the intrinsic integral
trace-dual diagonal, through completed scalar evaluation. -/
theorem scalarCompletedDualEquiv_diagonal_image :
    (diagonalLattice (codifferentModule K)).map
      ((scalarCompletedDualEquiv K).toLinearMap.restrictScalars ℤ) =
        diagonalLattice (integralTraceDual (principalModule (scalarBasis K))) := by
  ext z
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
    change scalarCompletedDualEquiv K (vectorDiagonalMap (K := K) (a : K)) ∈
      diagonalLattice (integralTraceDual (principalModule (scalarBasis K)))
    rw [scalarCompletedDualEquiv_diagonal]
    refine ⟨⟨scalarDualEquiv K a, ?_⟩, rfl⟩
    rw [← scalarDualEquiv_codifferent_image]
    exact ⟨a, a.property, rfl⟩
  · rintro ⟨f, rfl⟩
    have hf : (f : Module.Dual K K) ∈ (codifferentModule K).map
        ((scalarDualEquiv K).toLinearMap.restrictScalars (𝓞 K)) := by
      rw [scalarDualEquiv_codifferent_image]
      exact f.property
    obtain ⟨a, ha, haf⟩ := hf
    refine ⟨vectorDiagonalMap (K := K) a, ⟨⟨a, ha⟩, rfl⟩, ?_⟩
    exact (scalarCompletedDualEquiv_diagonal K a).trans
      (congrArg (vectorDiagonalMap (K := K)) haf)

private theorem scalarCovolume_transport
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
    (e : V ≃ₗᵢ[ℝ] W) (L : Submodule ℤ V) (D : Submodule ℤ W)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (h : L.map (e.toLinearEquiv.toLinearMap.restrictScalars ℤ) = D) :
    letI := measureSpaceOfInnerProductSpace (E := V)
    letI := measureSpaceOfInnerProductSpace (E := W)
    ZLattice.covolume L volume = ZLattice.covolume D volume := by
  let := measureSpaceOfInnerProductSpace (E := V)
  let := measureSpaceOfInnerProductSpace (E := W)
  have hc : ZLattice.comap ℝ L e.symm.toLinearEquiv.toLinearMap = D := by
    rw [← h]
    ext y
    change e.symm y ∈ L ↔ ∃ a, a ∈ L ∧ e a = y
    constructor
    · intro hy
      exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
  have ht := ZLattice.covolume_comap L volume volume
    (e := e.symm.toContinuousLinearEquiv) e.symm.measurePreserving
  exact ht.symm.trans (congrArg
    (fun P : Submodule ℤ W => ZLattice.covolume P volume) hc)

/-- The actual scalar codifferent, in its independently prescribed dualizing-line
metric, has reciprocal ordinary integer covolume. -/
theorem dualizingLine_euclideanCovolume :
    euclideanCovolume (dualizingLine K).toNormFamily (hξ := (dualizingLine_isHermitian K))
      (codifferentModule K) =
        ((2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
          Real.sqrt |(NumberField.discr K : ℝ)|)⁻¹ := by
  let := euclideanNormedAddCommGroup (dualizingLine K).toNormFamily
  let := euclideanNormedSpace (dualizingLine K).toNormFamily
  let := euclideanInnerProduct (hξ := (dualizingLine_isHermitian K))
  let : MeasurableSpace (CompletedVectorProduct K K) := borel _
  let : BorelSpace (CompletedVectorProduct K K) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K K)
  let := ordinaryTraceDualNormedAddCommGroup (scalarFamily K)
  let := ordinaryTraceDualNormedSpace (scalarFamily K)
  let := ordinaryTraceDualInnerProduct (hξ := (basisFamily_hermitian (scalarBasis K)))
  let : MeasurableSpace (CompletedVectorProduct K (Module.Dual K K)) := borel _
  let : BorelSpace (CompletedVectorProduct K (Module.Dual K K)) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K (Module.Dual K K))
  let := euclidean_discrete_diagonalLattice (dualizingLine K).toNormFamily
    (codifferentModule K) (codifferent_fg K) (codifferent_full K)
  let := euclidean_isZLattice_diagonalLattice (dualizingLine K).toNormFamily
    (codifferentModule K) (codifferent_fg K) (codifferent_full K)
  have ht := scalarCovolume_transport (dualizingLineOrdinaryTraceDualIsometry K)
    (diagonalLattice (codifferentModule K))
    (diagonalLattice (integralTraceDual (principalModule (scalarBasis K))))
    (scalarCompletedDualEquiv_diagonal_image K)
  have hi := ordinaryTraceDualCovolume_eq_inv (scalarFamily K)
    (hξ := (basisFamily_hermitian (scalarBasis K))) (principalModule (scalarBasis K))
    (principalModule_fg (scalarBasis K)) (principalModule_full (scalarBasis K))
  have hb := basisEuclideanCovolume (scalarBasis K)
  simp only [Fintype.card_fin, pow_one] at hb
  exact ht.trans (hi.trans (congrArg (fun x : ℝ => x⁻¹) hb))

/-- The raw degree of the actual codifferent line, derived from its actual
canonical covolume and the accepted full-lattice degree--covolume identity. -/
theorem dualizingLine_degree_eq_two_log :
    (dualizingLine K).degree
      =
        2 * Real.log ((2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
          Real.sqrt |(NumberField.discr K : ℝ)|) := by
  let η :=
    (AdelicVectorBundle.scalarLine (normalizedNumberFieldAdelicStructure K)).toNormFamily.scale
    (archimedeanFactor K) (archimedeanFactor_pos K)
  have hη : η.IsHermitian :=
    η.isHermitian_of_finrank_one (Module.finrank_self K)
  have h := NumberFieldFullLattice.fullLattice_log_euclideanCovolume_eq_neg_degree
    (codifferentModule K) (codifferent_fg K) (codifferent_full K) η (hη := hη)
  change Real.log (euclideanCovolume (dualizingLine K).toNormFamily
    (hξ := (dualizingLine_isHermitian K)) (codifferentModule K)) =
    -(dualizingLine K).degree
      +
      (Module.finrank K K : ℝ) * Real.log
        ((2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
          Real.sqrt |(NumberField.discr K : ℝ)|) at h
  rw [dualizingLine_euclideanCovolume, Real.log_inv] at h
  simp only [Module.finrank_self, Nat.cast_one, one_mul] at h
  linarith

/-- Exact discriminant formula for the raw normalized-curve dualizing-line degree. -/
theorem dualizingLine_degree :
    (dualizingLine K).degree
      =
        Real.log |(NumberField.discr K : ℝ)| -
          2 * (InfinitePlace.nrComplexPlaces K : ℝ) * Real.log 2 := by
  rw [dualizingLine_degree_eq_two_log, NumberFieldMinkowskiRadius.log_covolume_constant]
  ring

end ArakelovGeometry.NumberFieldTraceDualizingLineCovolume
