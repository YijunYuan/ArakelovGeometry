/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Minima.Basic
public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic
public import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Normalization.Hermitian
public import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Purity.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs

import ArakelovGeometry.AdelicVectorBundle.Minima.Basis
import ArakelovGeometry.AdelicVectorBundle.Minima.Restriction
import ArakelovGeometry.NumberTheory.NumberField.Minkowski.SmallVector
import Mathlib.Topology.Sheaves.Init

/-! # The actual first minimum of a pure Hermitian number-field bundle -/

@[expose] public section

noncomputable section

open NumberField MeasureTheory

namespace ArakelovGeometry.NumberFieldHermitianFirstMinimum

open AdelicStructure NumberFieldFullLattice

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- The actual pure bundle equals its own full integral model, so the produced vector belongs
to its literal finite global ball and has its original adelic vector degree. -/
theorem exists_integral_nonzero_large_degree
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K))
    [hV : V.toNormFamily.IsHermitian]
    [hpure : V.toNormFamily.IsPureAtFinitePlaces] (hn : 0 < Module.finrank K V) :
    ∃ s : {x : V // x ≠ 0}, s.val ∈ V.toNormFamily.globalUnitBall ∧
      V.slope -
        (Module.finrank ℚ K : ℝ) / 2 * Real.log (Module.finrank K V : ℝ) -
          Real.log |(NumberField.discr K : ℝ)| / 2 ≤ V.vectorDegree s := by
  obtain ⟨hfg, hspan, he⟩ :=
    V.isDominated.exists_pure_fullLatticeGaugeFamily_eq hV.1 hpure
  have heV : fullLatticeAdelicBundle (V.toNormFamily.globalUnitBallModule (hξ := hV.1))
      hfg hspan V.toNormFamily = V :=
    AdelicVectorBundle.ext
      (hξ := (fullLatticeAdelicBundle (V.toNormFamily.globalUnitBallModule (hξ := hV.1))
        hfg hspan V.toNormFamily).toIsAdelic) (hη := V.toIsAdelic) he
  obtain ⟨s, hs, hd⟩ := NumberFieldArithmeticSmallVector.exists_integral_nonzero_large_degree
    (V.toNormFamily.globalUnitBallModule (hξ := hV.1)) hfg hspan V.toNormFamily hn
  have hmean := congrArg (fun W : AdelicVectorBundle
    (normalizedNumberFieldAdelicStructure K) ↦ W.slope) heV
  rw [hmean, NormFamily.vectorDegree_eq_neg_integral] at hd
  refine ⟨s, hs, ?_⟩
  rw [AdelicVectorBundle.vectorDegree, NormFamily.vectorDegree_eq_neg_integral]
  change _ ≤ -(∫ ω, (fullLatticeGaugeFamily
    (V.toNormFamily.globalUnitBallModule (hξ := hV.1)) hfg hspan V.toNormFamily).logNorm s.val ω
      ∂(normalizedNumberFieldAdelicStructure K).v) at hd
  rwa [he] at hd

/-- Every actual nonzero restricted slope gives the source bound for the original first
minimum. The produced vector is transported through the actual subspace inclusion. -/
theorem restrict_slope_sub_error_le_firstMinimum
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K))
    [hV : V.toNormFamily.IsHermitian]
    [hpure : V.toNormFamily.IsPureAtFinitePlaces] (hn : 0 < Module.finrank K V)
    (F : Submodule K V) (hF : 0 < Module.finrank K F) :
    (((V.restrictOfNormMeasurability F).slope
      -
        ((Module.finrank ℚ K : ℝ) / 2 * Real.log (Module.finrank K V : ℝ) +
          Real.log |(NumberField.discr K : ℝ)| / 2) : ℝ) : EReal) ≤
            V.maximalLogarithmicMinimum := by
  let W := V.restrictOfNormMeasurability F
  obtain ⟨s, _, hs⟩ := exists_integral_nonzero_large_degree W (hV := (hV.restrict F))
    (hpure := (hpure.restrict F)) hF
  let t : {x : V // x ≠ 0} := ⟨s.val.val, fun h => s.property (Subtype.ext h)⟩
  have hdegree : W.vectorDegree s = V.vectorDegree t :=
    V.vectorDegree_restrictOfNormMeasurability F s
  rw [hdegree] at hs
  have hlog : Real.log (Module.finrank K F : ℝ) ≤
      Real.log (Module.finrank K V : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by change (0 : ℝ) < _; exact Nat.cast_pos.mpr hF)
      (by change (0 : ℝ) < _; exact Nat.cast_pos.mpr hn)
      (Nat.cast_le.mpr F.finrank_le)
  have herror := mul_le_mul_of_nonneg_left hlog
    (by positivity : 0 ≤ (Module.finrank ℚ K : ℝ) / 2)
  have hlower : W.slope -
      ((Module.finrank ℚ K : ℝ) / 2 * Real.log (Module.finrank K V : ℝ) +
        Real.log |(NumberField.discr K : ℝ)| / 2) ≤ V.vectorDegree t := by
    linarith
  have hminimum : (V.vectorDegree t : EReal) ≤ V.maximalLogarithmicMinimum :=
    V.coe_le_logarithmicMinimum_of_linearIndependent (fun _ : Fin 1 => t)
      (linearIndependent_unique_iff.mpr t.property) (fun _ => le_rfl)
  exact (EReal.coe_le_coe hlower).trans hminimum

/-- The ordinary first-minimum estimate on the actual pure Hermitian bundle and actual
maximal slope, without a target bound, attainment, or finite-value premise. -/
theorem maximalSlope_sub_error_le_firstMinimum
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K))
    [hV : V.toNormFamily.IsHermitian]
    [hpure : V.toNormFamily.IsPureAtFinitePlaces] (hn : 0 < Module.finrank K V) :
    V.maximalSlope -
      (((Module.finrank ℚ K : ℝ) / 2 * Real.log (Module.finrank K V : ℝ) +
        Real.log |(NumberField.discr K : ℝ)| / 2 : ℝ) : EReal) ≤
          V.maximalLogarithmicMinimum := by
  apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mpr
  apply iSup_le
  intro F
  have h := restrict_slope_sub_error_le_firstMinimum V hn F.val F.property
  rw [EReal.coe_sub] at h
  exact (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mp h

end ArakelovGeometry.NumberFieldHermitianFirstMinimum
