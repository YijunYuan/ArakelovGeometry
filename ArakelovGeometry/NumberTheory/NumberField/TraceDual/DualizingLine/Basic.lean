/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Model.TraceDual.Projective.Basic
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Hermitian.Line
import ArakelovGeometry.NumberTheory.NumberField.Lattice.Full.GlobalBall
import ArakelovGeometry.NumberTheory.NumberField.Lattice.Line.Basic
import ArakelovGeometry.NumberTheory.NumberField.Lattice.Line.FullLatticeIndex
import Mathlib.Topology.Sheaves.Init

/-! # The actual codifferent line with its prescribed trace metric -/

@[expose] public section

noncomputable section
open NumberField MeasureTheory
open scoped TensorProduct nonZeroDivisors

namespace ArakelovGeometry.NumberFieldTraceDualizingLine

open AdelicStructure NumberFieldCodifferentDual NumberFieldFullLattice
attribute [local instance 2000] Algebra.toModule Algebra.toSMul

variable (K : Type*) [Field K] [NumberField K]

/-- The canonical trace codifferent contains its literal scalar generator. -/
theorem one_mem_codifferent : (1 : K) ∈ codifferentModule K :=
  (FractionalIdeal.one_le_dual_one ℤ ℚ (L := K) (B := 𝓞 K)) (by simp)

/-- Finite generation is produced from the actual fractional ideal over the Noetherian ring. -/
theorem codifferent_fg : (codifferentModule K).FG :=
  FractionalIdeal.fg_of_isNoetherianRing le_rfl _

/-- The literal codifferent spans its original scalar generic fibre. -/
theorem codifferent_full : Submodule.span K (codifferentModule K : Set K) = ⊤ := by
  apply top_unique
  intro x _
  have h := (Submodule.span K (codifferentModule K : Set K)).smul_mem x
    (Submodule.subset_span (one_mem_codifferent K))
  simpa only [smul_eq_mul, mul_one] using h

/-- The actual original codifferent module is invertible. -/
theorem codifferent_invertible : Module.Invertible (𝓞 K) (codifferentModule K) :=
  NumberFieldLineLattice.invertible_of_fg_of_span_eq_top_of_finrank_eq_one _
    (codifferent_fg K) (codifferent_full K) (Module.finrank_self K)

/-- The canonical generic scalar identification of the actual codifferent. -/
def codifferentGenericEquiv : K ⊗[𝓞 K] codifferentModule K ≃ₗ[K] K :=
  genericTensorEquiv _ (codifferent_full K)

@[simp]
theorem codifferentGenericEquiv_tmul (c : K) (a : codifferentModule K) :
    codifferentGenericEquiv K (c ⊗ₜ[𝓞 K] a) = c * (a : K) :=
  genericTensorEquiv_tmul _ (codifferent_full K) c a

/-- The literal codifferent identifies with the original integer trace dual of A,
using the canonical original projective tensor trace equivalence. -/
def codifferentIntegerTraceEquiv : codifferentModule K ≃ₗ[ℤ] Module.Dual ℤ (𝓞 K) :=
  ((TensorProduct.rid (𝓞 K) (codifferentModule K)).symm.restrictScalars ℤ).trans
    (((TensorProduct.congr (LinearEquiv.refl (𝓞 K) (codifferentModule K))
      (LinearMap.ringLmapEquivSelf (𝓞 K) (𝓞 K) (𝓞 K)).symm).restrictScalars ℤ).trans
        (NumberFieldProjectiveTraceDual.integerTensorEquiv (K := K) (𝓞 K)))

@[simp]
theorem codifferentIntegerTraceEquiv_apply (a : codifferentModule K) (b : 𝓞 K) :
    (codifferentIntegerTraceEquiv K a b : ℚ) =
      Algebra.trace ℚ K ((b : K) * (a : K)) := by
  change (NumberFieldProjectiveTraceDual.integerTensorEquiv (K := K) (𝓞 K)
    (a ⊗ₜ[𝓞 K] (LinearMap.ringLmapEquivSelf (𝓞 K) (𝓞 K) (𝓞 K)).symm 1) b : ℚ) = _
  rw [NumberFieldProjectiveTraceDual.integerTensorEquiv_tmul_apply]
  congr 1
  simp

/-- The source's A-action on its original integer dual is literal precomposition
by multiplication; the canonical trace identification respects it. -/
theorem codifferentIntegerTraceEquiv_smul_apply
    (c : 𝓞 K) (a : codifferentModule K) (b : 𝓞 K) :
    codifferentIntegerTraceEquiv K (c • a) b = codifferentIntegerTraceEquiv K a (c * b) := by
  apply (Int.cast_injective (α := ℚ))
  rw [codifferentIntegerTraceEquiv_apply, codifferentIntegerTraceEquiv_apply]
  congr 1
  simp [mul_left_comm, mul_comm]

/-- The source trace generator as an actual integer functional on the original A. -/
def traceGenerator : Module.Dual ℤ (𝓞 K) :=
  codifferentIntegerTraceEquiv K ⟨1, one_mem_codifferent K⟩

@[simp]
theorem traceGenerator_apply (b : 𝓞 K) :
    (traceGenerator K b : ℚ) = Algebra.trace ℚ K (b : K) := by
  rw [traceGenerator, codifferentIntegerTraceEquiv_apply]
  simp

/-- The prescribed trace-generator factor at actual infinite places, with value one
at finite places before their norms are replaced by the actual codifferent gauges. -/
def archimedeanFactor (ω : (normalizedNumberFieldAdelicStructure K).Ω) : ℝ := by
  classical
  exact if hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωinf then
    ((normalizedInfinitePlaceEquiv.symm ⟨ω, hω⟩).mult : ℝ) else 1

theorem archimedeanFactor_pos (ω : (normalizedNumberFieldAdelicStructure K).Ω) :
    0 < archimedeanFactor K ω := by
  classical
  unfold archimedeanFactor
  split
  · exact_mod_cast InfinitePlace.mult_pos
  · exact zero_lt_one

@[simp]
theorem archimedeanFactor_infinite (w : InfinitePlace K) :
    archimedeanFactor K (normalizedInfinitePlacePoint w) = (w.mult : ℝ) := by
  classical
  rw [archimedeanFactor, dite_eq_left (normalizedInfinitePlacePoint_mem_inf w)]
  change (((normalizedInfinitePlaceEquiv (K := K)).symm
    (normalizedInfinitePlaceEquiv w)).mult : ℝ) = _
  rw [Equiv.symm_apply_apply]

/-- The actual adelic scalar line with the literal codifferent finite lattice and the
prescribed trace-generator norms at infinity. -/
def dualizingLine : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) K :=
  fullLatticeAdelicBundle (codifferentModule K) (codifferent_fg K) (codifferent_full K)
    ((AdelicVectorBundle.scalarLine (normalizedNumberFieldAdelicStructure K)).toNormFamily.scale
      (archimedeanFactor K) (archimedeanFactor_pos K))

theorem dualizingLine_isLine : (dualizingLine K).IsLine := Module.finrank_self K

theorem dualizingLine_isHermitian :
    (dualizingLine K).IsHermitian normalizedNumberFieldArchimedeanCompletions :=
  (dualizingLine K).toNormFamily.isHermitian_of_finrank_one (Module.finrank_self K)
    normalizedNumberFieldArchimedeanCompletions

/-- Every finite completed norm is the scalar gauge of the actual codifferent tensor image. -/
theorem dualizingLine_norm_prime (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (z : ((normalizedNumberFieldAdelicStructure K).ϕ
      (ActualPrimeIndexing.normalizedPrimeParameter p)).Completion ⊗[K] K) :
    (dualizingLine K).norm (ActualPrimeIndexing.normalizedPrimeParameter p) z =
      scalarLatticeGauge
        (F := ((normalizedNumberFieldAdelicStructure K).ϕ
          (ActualPrimeIndexing.normalizedPrimeParameter p)).Completion)
        (NumberFieldModel.completedLatticeSpan (codifferentModule K) p : Set _) z :=
  fullLatticeGaugeFamily_norm_prime _ (codifferent_fg K) (codifferent_full K) _ p z

/-- The finite completed unit ball is literally the completed codifferent lattice. -/
theorem dualizingLine_completedUnitBall_eq (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (dualizingLine K).toNormFamily.completedUnitBall
      (ActualPrimeIndexing.normalizedPrimeParameter p) =
        (NumberFieldModel.completedLatticeSpan (codifferentModule K) p : Set _) :=
  fullLatticeGaugeFamily_completedUnitBall_eq _ (codifferent_fg K) (codifferent_full K) _ p

theorem dualizingLine_isPureAtFinitePlaces :
    (dualizingLine K).toNormFamily.IsPureAtFinitePlaces :=
  fullLatticeGaugeFamily_isPureAtFinitePlaces _ (codifferent_fg K) (codifferent_full K) _

/-- The original global integral unit ball is exactly the actual codifferent. -/
theorem dualizingLine_globalUnitBall_eq :
    (dualizingLine K).toNormFamily.globalUnitBall = (codifferentModule K : Set K) :=
  fullLatticeGaugeFamily_globalUnitBall_eq _ (codifferent_fg K) (codifferent_full K) _

/-- Every prescribed infinite completed norm is the actual trace factor times the
original scalar absolute value. -/
theorem dualizingLine_norm_infinite (w : InfinitePlace K)
    (a : NumberFieldArchimedeanVectorDiagonal.CompletedCoefficient w) :
    (dualizingLine K).norm (normalizedInfinitePlacePoint w) (a ⊗ₜ[K] (1 : K)) =
      (w.mult : ℝ) * ‖a‖ := by
  change (fullLatticeGaugeFamily (codifferentModule K) (codifferent_fg K) (codifferent_full K)
    ((AdelicVectorBundle.scalarLine (normalizedNumberFieldAdelicStructure K)).toNormFamily.scale
      (archimedeanFactor K) (archimedeanFactor_pos K))).norm
        (normalizedInfinitePlacePoint w) (a ⊗ₜ[K] (1 : K)) = _
  rw [fullLatticeGaugeFamily_norm_not_finite _ (codifferent_fg K) (codifferent_full K) _ _
    (normalizedInfinitePlacePoint_mem_inf w), NormFamily.scale_norm,
    archimedeanFactor_infinite, AdelicVectorBundle.scalarLine_norm_tmul_one]

theorem dualizingLine_norm_generator (w : InfinitePlace K) :
    (dualizingLine K).norm (normalizedInfinitePlacePoint w)
      ((1 : NumberFieldArchimedeanVectorDiagonal.CompletedCoefficient w) ⊗ₜ[K] (1 : K)) =
        (w.mult : ℝ) := by
  rw [dualizingLine_norm_infinite, norm_one, mul_one]

theorem dualizingLine_norm_generator_real (w : InfinitePlace K) (hw : w.IsReal) :
    (dualizingLine K).norm (normalizedInfinitePlacePoint w)
      ((1 : NumberFieldArchimedeanVectorDiagonal.CompletedCoefficient w) ⊗ₜ[K] (1 : K)) = 1 := by
  rw [dualizingLine_norm_generator, hw.mult_eq_one]
  norm_num

theorem dualizingLine_norm_generator_complex (w : InfinitePlace K) (hw : w.IsComplex) :
    (dualizingLine K).norm (normalizedInfinitePlacePoint w)
      ((1 : NumberFieldArchimedeanVectorDiagonal.CompletedCoefficient w) ⊗ₜ[K] (1 : K)) = 2 := by
  rw [dualizingLine_norm_generator, hw.mult_eq_two]
  norm_num

/-- The norm statement for the literal source trace functional, transported through
its proved original integer-dual and generic scalar identifications. -/
theorem dualizingLine_norm_source_trace (w : InfinitePlace K) :
    (dualizingLine K).norm (normalizedInfinitePlacePoint w)
      ((1 : NumberFieldArchimedeanVectorDiagonal.CompletedCoefficient w) ⊗ₜ[K]
        codifferentGenericEquiv K ((1 : K) ⊗ₜ[𝓞 K]
          (codifferentIntegerTraceEquiv K).symm (traceGenerator K))) = (w.mult : ℝ) := by
  rw [traceGenerator, LinearEquiv.symm_apply_apply, codifferentGenericEquiv_tmul]
  simpa only [one_mul] using dualizingLine_norm_generator K w

end ArakelovGeometry.NumberFieldTraceDualizingLine
