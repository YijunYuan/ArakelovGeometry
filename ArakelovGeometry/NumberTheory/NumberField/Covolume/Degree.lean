/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Countable
public import ArakelovGeometry.AdelicVectorBundle.Degree.Basic
public import ArakelovGeometry.NumberTheory.NumberField.Covolume.HermitianBasis
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs

import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.Analysis.Determinant.ExactSequence
import ArakelovGeometry.NumberTheory.NumberField.Archimedean.DeterminantIntegral
import ArakelovGeometry.NumberTheory.NumberField.Covolume.IntegralBasis
import ArakelovGeometry.NumberTheory.NumberField.Lattice.Index.Global
import ArakelovGeometry.NumberTheory.NumberField.Local.Determinant.PrincipalGauge
import Mathlib.Topology.Sheaves.Init

/-! # The determinant degree and actual covolume of a full number-field lattice -/

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField TensorProduct

namespace ArakelovGeometry.NumberFieldFullLattice

open AdelicStructure ActualPrimeIndexing NumberFieldPrincipalDeterminantGauge
  NumberFieldHermitianBasisCovolume NumberFieldHermitianLatticeCovolume
  NumberFieldArchimedeanCovolume

attribute [local instance 2000] Algebra.toModule Algebra.toSMul

variable {K E : Type*} [Field K] [NumberField K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The canonical adelic bundle from the already constructed actual full-lattice norm family. -/
def fullLatticeAdelicBundle
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤)
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) E) :
    AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E :=
  AdelicVectorBundle.ofMeasurableDominated (fullLatticeGaugeFamily L hfg hspan η)
    (hm := (NormFamily.isMeasurable_of_discrete _))
    (hd := (fullLatticeGaugeFamily_coherent_and_dominated L hfg hspan η).2)

@[simp]
theorem fullLatticeAdelicBundle_toNormFamily
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤)
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) E) :
    (fullLatticeAdelicBundle L hfg hspan η).toNormFamily =
      fullLatticeGaugeFamily L hfg hspan η := rfl

omit [FiniteDimensional K E] in
/-- Prescribing Hermitian infinite norms makes the actual full-lattice family Hermitian. -/
instance fullLatticeGaugeFamily_isHermitian
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤)
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [hη : η.IsHermitian] :
    (fullLatticeGaugeFamily L hfg hspan η).IsHermitian
      := by
  refine ⟨fullLatticeGaugeFamily_isUltrametric L hfg hspan η, ?_⟩
  intro ω hω
  obtain ⟨c, hc⟩ := hη.2 ω hω
  refine ⟨c, fun z => ?_⟩
  rw [fullLatticeGaugeFamily_norm_not_finite L hfg hspan η ω hω]
  exact hc z

omit [AddCommGroup E] [Module K E] [FiniteDimensional K E] in
/-- Integrable functions on the literal finite locus sum over the actual primes and masses. -/
theorem normalized_finite_integral_eq_tsum
    (f : (normalizedNumberFieldAdelicStructure K).Ω → ℝ)
    (hf : IntegrableOn f (normalizedNumberFieldAdelicStructure K).Ωfin
      (normalizedNumberFieldAdelicStructure K).v) :
    (∫ ω in (normalizedNumberFieldAdelicStructure K).Ωfin,
      f ω ∂(normalizedNumberFieldAdelicStructure K).v) =
      ∑' p : HeightOneSpectrum (𝓞 K),
        (normalizedNumberFieldAdelicStructure K).v.real {normalizedPrimeParameter p} *
          f (normalizedPrimeParameter p) := by
  let S := normalizedNumberFieldAdelicStructure K
  let : Countable S.Ω := inferInstanceAs
    (Countable {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
  let : MeasurableSingletonClass S.Ω := inferInstanceAs
    (MeasurableSingletonClass {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
  have hset : MeasurableSet S.Ωfin := by
    simpa only [Ωinf, Ωfin, Set.compl_ofPred, not_not] using S.measurableSet_Ωinf.compl
  have hint : Integrable (S.Ωfin.indicator f) S.v :=
    (integrable_indicator_iff hset).mpr hf
  rw [← integral_indicator hset, integral_countable hint]
  let g := fun ω : S.Ω => S.v.real {ω} • S.Ωfin.indicator f ω
  have hsupport : Function.support g ⊆ S.Ωfin := by
    intro ω hω
    by_contra hfin
    exact hω (by simp [g, Set.indicator_of_notMem hfin])
  change ∑' ω : S.Ω, g ω = _
  rw [← tsum_subtype_eq_of_support_subset hsupport,
    ← (normalizedPrimeEquivFinite (K := K)).tsum_eq]
  apply tsum_congr
  intro p
  change S.v.real {normalizedPrimeParameter p} *
    S.Ωfin.indicator f (normalizedPrimeParameter p) = _
  rw [Set.indicator_of_mem (normalizedPrimeParameter_mem_fin p)]

/-- A fixed rational determinant wedge has its finite degree contribution equal to the
actual original lattice index, with all normalization weights produced by the curve. -/
theorem fullLatticeGaugeFamily_finite_integral_neg_log_basis
    (b : Module.Basis (Fin (Module.finrank K E)) K E)
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (hb : principalModule b ≤ L)
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) E) :
    (∫ ω in (normalizedNumberFieldAdelicStructure K).Ωfin,
      -(fullLatticeGaugeFamily L hfg hspan η).determinant.logNorm
        (exteriorPower.ιMulti K _ b) ω ∂(normalizedNumberFieldAdelicStructure K).v) =
      Real.log ((principalModule b).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) := by
  let V := fullLatticeAdelicBundle L hfg hspan η
  have hint : IntegrableOn (fun ω =>
      -(fullLatticeGaugeFamily L hfg hspan η).determinant.logNorm
        (exteriorPower.ιMulti K _ b) ω) (normalizedNumberFieldAdelicStructure K).Ωfin
          (normalizedNumberFieldAdelicStructure K).v :=
    ((V.determinantOfMeasurableBase
   ).integrable_logNorm
      (exteriorPower.ιMulti K _ b)).neg.integrableOn
  rw [normalized_finite_integral_eq_tsum _ hint,
    integralLattice_log_relIndex_eq_tsum_localLength (principalModule b) L hb
      (principalModule_fg b) hfg (principalModule_full b) hspan]
  apply tsum_congr
  intro p
  rw [fullLatticeGaugeFamily_determinant_log_basis b L hfg hspan hb η p,
    neg_mul, neg_neg, ← mul_assoc, normalized_weighted_prime_log_scale]
  exact mul_comm _ _

/-- The genuine determinant degree splits into the original finite index and the actual
Archimedean determinant logarithmic norm integral. -/
theorem fullLatticeAdelicBundle_degree_eq_index_sub_integral
    (b : Module.Basis (Fin (Module.finrank K E)) K E)
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (hb : principalModule b ≤ L)
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) E) :
    (fullLatticeAdelicBundle L hfg hspan η).degree
      =
      Real.log ((principalModule b).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) -
        ∫ ω in (normalizedNumberFieldAdelicStructure K).Ωinf,
          (fullLatticeGaugeFamily L hfg hspan η).determinant.logNorm
            (exteriorPower.ιMulti K _ b) ω ∂(normalizedNumberFieldAdelicStructure K).v := by
  let V := fullLatticeAdelicBundle L hfg hspan η
  have hu : exteriorPower.ιMulti K (Module.finrank K E) b ≠ 0 := by
    intro hz
    have h := congrArg (determinantCoordinateEquiv b) hz
    rw [determinantCoordinateEquiv_ιMulti, b.det_self, map_zero] at h
    exact one_ne_zero h
  rw [V.degree_eq_neg_integral
    ⟨_, hu⟩]
  have hint := (V.determinantOfMeasurableBase
   ).integrable_logNorm
      (exteriorPower.ιMulti K _ b)
  have hsplit := integral_add_compl (normalizedNumberFieldAdelicStructure K).measurableSet_Ωinf
    hint
  have hfin := fullLatticeGaugeFamily_finite_integral_neg_log_basis b L hfg hspan hb η
  rw [integral_neg] at hfin
  have hcompl : (normalizedNumberFieldAdelicStructure K).Ωinfᶜ =
      (normalizedNumberFieldAdelicStructure K).Ωfin := by
    simp only [Ωinf, Ωfin, Set.compl_ofPred, not_not]
  rw [hcompl] at hsplit
  change (∫ ω in (normalizedNumberFieldAdelicStructure K).Ωinf,
      (fullLatticeGaugeFamily L hfg hspan η).determinant.logNorm
        (exteriorPower.ιMulti K _ b) ω ∂(normalizedNumberFieldAdelicStructure K).v) +
    (∫ ω in (normalizedNumberFieldAdelicStructure K).Ωfin,
      (fullLatticeGaugeFamily L hfg hspan η).determinant.logNorm
        (exteriorPower.ιMulti K _ b) ω ∂(normalizedNumberFieldAdelicStructure K).v) =
      (∫ ω, (fullLatticeGaugeFamily L hfg hspan η).determinant.logNorm
        (exteriorPower.ιMulti K _ b) ω ∂(normalizedNumberFieldAdelicStructure K).v) at hsplit
  change -(∫ ω, (fullLatticeGaugeFamily L hfg hspan η).determinant.logNorm
    (exteriorPower.ιMulti K _ b) ω ∂(normalizedNumberFieldAdelicStructure K).v) = _
  linarith

/-- The original full Hermitian lattice covolume equals its actual determinant degree,
with the ordinary scalar discriminant normalization. No contained basis is assumed. -/
theorem fullLattice_log_euclideanCovolume_eq_neg_degree
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤)
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [hη : η.IsHermitian] :
    Real.log (euclideanCovolume (fullLatticeGaugeFamily L hfg hspan η)
      (hξ := (fullLatticeGaugeFamily_isHermitian L hfg hspan η)) L) =
      -(fullLatticeAdelicBundle L hfg hspan η).degree
        +
        (Module.finrank K E : ℝ) * Real.log
          ((2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
            Real.sqrt |(NumberField.discr K : ℝ)|) := by
  obtain ⟨b, hb⟩ := exists_principalModule_le L hspan
  have hv := log_euclideanCovolume_eq_integral (fullLatticeGaugeFamily L hfg hspan η)
    (hξ := (fullLatticeGaugeFamily_isHermitian L hfg hspan η)) b L hfg hspan hb
  have hd := fullLatticeAdelicBundle_degree_eq_index_sub_integral b L hfg hspan hb η
  linarith

/-- Exponentiating the actual degree identity gives the ordinary full-lattice covolume. -/
theorem fullLattice_euclideanCovolume_eq_exp_neg_degree
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤)
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [hη : η.IsHermitian] :
    euclideanCovolume (fullLatticeGaugeFamily L hfg hspan η)
      (hξ := (fullLatticeGaugeFamily_isHermitian L hfg hspan η)) L =
      Real.exp (-(fullLatticeAdelicBundle L hfg hspan η).degree
        +
        (Module.finrank K E : ℝ) * Real.log
          ((2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
            Real.sqrt |(NumberField.discr K : ℝ)|)) := by
  rw [← fullLattice_log_euclideanCovolume_eq_neg_degree L hfg hspan η,
    Real.exp_log (euclideanCovolume_pos _ L hfg hspan)]

end ArakelovGeometry.NumberFieldFullLattice
