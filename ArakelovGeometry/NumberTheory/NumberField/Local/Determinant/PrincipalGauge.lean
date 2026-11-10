/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Covolume.HermitianBasis
public import ArakelovGeometry.NumberTheory.NumberField.Local.Determinant.Gauge
public import ArakelovGeometry.NumberTheory.NumberField.Local.Determinant.Index
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Rational
import ArakelovGeometry.NumberTheory.NumberField.Local.Determinant.Comparison
import ArakelovGeometry.NumberTheory.NumberField.Local.Determinant.DVRIndex
import ArakelovGeometry.NumberTheory.NumberField.Local.Determinant.Valuation
import Mathlib.RingTheory.PicardGroup
import Mathlib.Topology.Sheaves.Init

/-! # The fixed rational basis wedge in actual finite lattice determinant gauges -/

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField TensorProduct

namespace ArakelovGeometry.NumberFieldPrincipalDeterminantGauge

open AdelicStructure ActualPrimeIndexing NumberFieldFullLattice
  NumberFieldLocalDeterminantGauge NumberFieldLocalDeterminantComparison
  NumberFieldHermitianBasisCovolume

attribute [local instance 2000] Algebra.toModule Algebra.toSMul

variable {K E : Type*} [Field K] [NumberField K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local notation "principalCoefficientRing" => fun (p : HeightOneSpectrum (𝓞 K)) ↦
  AdelicStructure.rationalLocalRing (normalizedNumberFieldAdelicStructure K)
    (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p)

omit [FiniteDimensional K E] in
/-- The actual localized principal module is the local span of its original basis. -/
theorem rationalLocalSpan_principalModule
    (b : Module.Basis (Fin (Module.finrank K E)) K E) (p : HeightOneSpectrum (𝓞 K)) :
    rationalLocalSpan (principalModule b) p =
      Submodule.span (principalCoefficientRing p) (Set.range b) := by
  exact Submodule.span_span_of_tower (𝓞 K) (principalCoefficientRing p) (Set.range b)

/-- A prescribed rational basis is a basis of its actual integral local span. -/
def principalLocalBasis
    (b : Module.Basis (Fin (Module.finrank K E)) K E) (p : HeightOneSpectrum (𝓞 K)) :
    Module.Basis (Fin (Module.finrank K E)) (principalCoefficientRing p)
      (rationalLocalSpan (principalModule b) p) :=
  (b.restrictScalars (principalCoefficientRing p)).map
    (LinearEquiv.ofEq _ _ (rationalLocalSpan_principalModule b p).symm)

omit [FiniteDimensional K E] in
@[simp]
theorem principalLocalBasis_coe
    (b : Module.Basis (Fin (Module.finrank K E)) K E) (p : HeightOneSpectrum (𝓞 K))
    (i : Fin (Module.finrank K E)) : (principalLocalBasis b p i : E) = b i := by
  change ((b.restrictScalars (principalCoefficientRing p)) i : E) = b i
  exact b.restrictScalars_apply (principalCoefficientRing p) i

omit [FiniteDimensional K E] in
/-- The actual local inclusion determinant is computed in the one fixed rational basis. -/
theorem principalLocalBasis_det_coe
    (b : Module.Basis (Fin (Module.finrank K E)) K E)
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (hb : principalModule b ≤ L)
    (p : HeightOneSpectrum (𝓞 K)) :
    ((LinearMap.toMatrix (principalLocalBasis b p) (rationalLocalBasisFinrank L hfg hspan p)
      (rationalLocalLatticeInclusion hb p)).det : K) = (localRankBasis L hfg hspan p).det b := by
  classical
  rw [Module.Basis.det_apply]
  have hm : (LinearMap.toMatrix (principalLocalBasis b p)
      (rationalLocalBasisFinrank L hfg hspan p) (rationalLocalLatticeInclusion hb p)).map
        (algebraMap (principalCoefficientRing p) K) =
      (localRankBasis L hfg hspan p).toMatrix b := by
    ext i j
    simp only [Matrix.map_apply, LinearMap.toMatrix_apply, Module.Basis.toMatrix_apply]
    have hc := localRankBasis_repr_coe L hfg hspan p
      (rationalLocalLatticeInclusion hb p (principalLocalBasis b p j)) i
    simpa only [rationalLocalLatticeInclusion, Submodule.inclusion_apply,
      principalLocalBasis_coe] using hc.symm
  rw [← hm]
  exact (algebraMap (principalCoefficientRing p) K).map_det _

omit [FiniteDimensional K E] in
/-- The actual local quotient length in the prescribed fixed rational basis. -/
theorem principal_local_length_eq_addVal_det
    (b : Module.Basis (Fin (Module.finrank K E)) K E)
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (hb : principalModule b ≤ L)
    (p : HeightOneSpectrum (𝓞 K)) :
    Module.length (principalCoefficientRing p)
      (rationalLocalSpan L p ⧸ rationalLocalLatticeImage hb p) =
      IsDiscreteValuationRing.addVal (principalCoefficientRing p)
        (LinearMap.toMatrix (principalLocalBasis b p) (rationalLocalBasisFinrank L hfg hspan p)
          (rationalLocalLatticeInclusion hb p)).det := by
  let c := rationalLocalBasisFinrank L hfg hspan p
  have hlen := DVRDeterminantIndex.length_quotient_eq_addVal_det
    (rationalLocalLatticeImage hb p) c
    ((principalLocalBasis b p).map (rationalLocalLatticeImageEquiv hb p))
  have hmat : LinearMap.toMatrix
      ((principalLocalBasis b p).map (rationalLocalLatticeImageEquiv hb p)) c
      (rationalLocalLatticeImage hb p).subtype =
      LinearMap.toMatrix (principalLocalBasis b p) c (rationalLocalLatticeInclusion hb p) := by
    ext i j
    simp only [LinearMap.toMatrix_apply, Module.Basis.map_apply,
      rationalLocalLatticeImageEquiv_coe, Submodule.subtype_apply]
  exact hlen.trans (congrArg
    (fun A => IsDiscreteValuationRing.addVal (principalCoefficientRing p) A.det) hmat)

/-- One fixed original rational basis wedge computes every actual finite local length. -/
theorem fullLatticeGaugeFamily_determinant_log_basis
    (b : Module.Basis (Fin (Module.finrank K E)) K E)
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (hb : principalModule b ≤ L)
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (p : HeightOneSpectrum (𝓞 K)) :
    (fullLatticeGaugeFamily L hfg hspan η).determinant.logNorm
      (exteriorPower.ιMulti K _ b) (normalizedPrimeParameter p) =
      -normalizedPlaceLogScale (normalizedPrimeParameter p) *
        ((Module.length (principalCoefficientRing p)
          (rationalLocalSpan L p ⧸ rationalLocalLatticeImage hb p)).toNat : ℝ) := by
  classical
  let A := LinearMap.toMatrix (principalLocalBasis b p)
    (rationalLocalBasisFinrank L hfg hspan p) (rationalLocalLatticeInclusion hb p)
  have hdetK : (A.det : K) ≠ 0 := by
    rw [principalLocalBasis_det_coe b L hfg hspan hb p]
    exact ((localRankBasis L hfg hspan p).isUnit_det b).ne_zero
  have hdet : A.det ≠ 0 := by
    intro hz
    exact hdetK (by rw [hz]; exact map_zero (algebraMap (principalCoefficientRing p) K))
  change Real.log ((fullLatticeGaugeFamily L hfg hspan η).determinant.norm _ _) = _
  rw [fullLatticeGaugeFamily_determinant_norm_rational_wedge,
    ← principalLocalBasis_det_coe b L hfg hspan hb p,
    AdelicStructure.norm_algebraMap_eq_absValue,
    principal_local_length_eq_addVal_det b L hfg hspan hb p,
    normalizedPlaceLogScale_prime]
  exact rationalLocal_normalized_log p A.det hdet

end ArakelovGeometry.NumberFieldPrincipalDeterminantGauge
