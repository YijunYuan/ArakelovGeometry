/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Covolume.HermitianBasis
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import ArakelovGeometry.NumberTheory.NumberField.Covolume.Integer
import ArakelovGeometry.NumberTheory.NumberField.Covolume.PrincipalScalar
import Mathlib.Topology.Sheaves.Init

/-!
# Actual Hermitian lattice covolumes from an integral basis sublattice

The principal-basis scalar normalization and the infinite-place determinant
Jacobian give a covolume formula for an original full integral lattice
containing the principal span of a rational basis. The denominator is the
actual additive relative index. Identifying it with a determinant-lattice
index is a separate finite-place calculation.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped NumberField

namespace ArakelovGeometry.NumberFieldHermitianLatticeCovolume

open AdelicStructure NumberFieldArchimedeanCovolume
  NumberFieldHermitianBasisCovolume

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E]
  [Module K E] [FiniteDimensional K E]

/-- The actual principal basis lattice has its metric determinant and scalar factors. -/
theorem principal_euclideanCovolume
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (b : Module.Basis (Fin (Module.finrank K E)) K E) :
    euclideanCovolume ξ hξ (principalModule b) = basisDeterminantFactor ξ b *
      (((2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
        Real.sqrt |(NumberField.discr K : ℝ)|) ^ Module.finrank K E) := by
  rw [principalCovolume_eq_detFactor ξ hξ b]
  apply congrArg (basisDeterminantFactor ξ b * ·)
  simpa only [Fintype.card_fin, principalModule,
    NumberFieldPrincipalBasisScalarCovolume.principalModule] using
    NumberFieldPrincipalBasisScalarCovolume.basisEuclideanCovolume b

/-- The denominator is the relative index of the two original integral modules. -/
theorem euclideanCovolume_eq_div_principal_index
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (b : Module.Basis (Fin (Module.finrank K E)) K E)
    (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) (hbM : principalModule b ≤ M) :
    euclideanCovolume ξ hξ M =
      (basisDeterminantFactor ξ b *
        (((2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
          Real.sqrt |(NumberField.discr K : ℝ)|) ^ Module.finrank K E)) /
        (principalModule b).toAddSubgroup.relIndex M.toAddSubgroup := by
  rw [euclideanCovolume_eq_div_relIndex ξ hξ (principalModule b) M
    (principalModule_fg b) (principalModule_full b) hfg hspan hbM,
    principal_euclideanCovolume]

/-- The original additive index is positive, independently of taking its logarithm. -/
theorem principal_index_pos
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (b : Module.Basis (Fin (Module.finrank K E)) K E)
    (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) (hbM : principalModule b ≤ M) :
    0 < (principalModule b).toAddSubgroup.relIndex M.toAddSubgroup :=
  original_relIndex_pos ξ hξ (principalModule b) M (principalModule_fg b)
    (principalModule_full b) hfg hspan hbM

/-- The original basis sublattice has finite relative index in the original full lattice. -/
theorem principal_isFiniteRelIndex
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (b : Module.Basis (Fin (Module.finrank K E)) K E)
    (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) (hbM : principalModule b ≤ M) :
    (principalModule b).toAddSubgroup.IsFiniteRelIndex M.toAddSubgroup :=
  AddSubgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr
    (principal_index_pos ξ hξ b M hfg hspan hbM).ne'

theorem log_basisDeterminantFactor
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (b : Module.Basis (Fin (Module.finrank K E)) K E) :
    Real.log (basisDeterminantFactor ξ b) =
      ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (completedBasisDeterminantNorm ξ b w) := by
  classical
  rw [basisDeterminantFactor, Real.log_prod (fun w _ =>
    pow_ne_zero _ (completedBasisDeterminantNorm_pos ξ hξ b w).ne')]
  simp only [Real.log_pow]

/-- The logarithmic covolume retains the actual infinite determinant terms and
the actual original additive index, before finite-place degree identification. -/
theorem log_euclideanCovolume
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (b : Module.Basis (Fin (Module.finrank K E)) K E)
    (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) (hbM : principalModule b ≤ M) :
    Real.log (euclideanCovolume ξ hξ M) =
      (∑ w : InfinitePlace K, (w.mult : ℝ) *
        Real.log (completedBasisDeterminantNorm ξ b w)) +
      (Module.finrank K E : ℝ) * Real.log
        ((2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
          Real.sqrt |(NumberField.discr K : ℝ)|) -
      Real.log ((principalModule b).toAddSubgroup.relIndex M.toAddSubgroup : ℝ) := by
  have hscalar : 0 < (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
      Real.sqrt |(NumberField.discr K : ℝ)| := by
    apply mul_pos (by positivity)
    exact Real.sqrt_pos.2 (NumberFieldActualIntegerCovolume.discriminant_abs_pos K)
  have hindex : (0 : ℝ) <
      ((principalModule b).toAddSubgroup.relIndex M.toAddSubgroup : ℝ) := by
    exact_mod_cast principal_index_pos ξ hξ b M hfg hspan hbM
  rw [euclideanCovolume_eq_div_principal_index ξ hξ b M hfg hspan hbM,
    Real.log_div (mul_ne_zero (basisDeterminantFactor_pos ξ hξ b).ne'
      (pow_ne_zero _ hscalar.ne')) hindex.ne',
    Real.log_mul (basisDeterminantFactor_pos ξ hξ b).ne' (pow_ne_zero _ hscalar.ne'),
    Real.log_pow, log_basisDeterminantFactor ξ hξ b]

end ArakelovGeometry.NumberFieldHermitianLatticeCovolume
