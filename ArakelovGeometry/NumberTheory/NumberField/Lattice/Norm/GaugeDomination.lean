/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Norm.Gauge
public import ArakelovGeometry.NumberTheory.NumberField.Local.Lattice.PrincipalFrame
public import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Impurity.Basic

import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Subquotient
import ArakelovGeometry.NumberTheory.NumberField.Lattice.Coherence.Criteria
import ArakelovGeometry.NumberTheory.NumberField.Lattice.Coherence.FiniteGeneration
import ArakelovGeometry.NumberTheory.NumberField.Lattice.Coherence.Model
import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Impurity.Distance
import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Normalization.Hermitian

/-!
# Domination, the literal global ball, and actual impurity

Genuine coherence reconstructs each actual completed ball from the literal
global integral module. Its finite generation supplies a common completed
frame outside finitely many actual primes and proves domination of the
actual lattice-gauge family. This gives source Proposition 4.4.9.
-/

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal TensorProduct NumberField

noncomputable section

namespace ArakelovGeometry.NormFamily

open AdelicStructure ActualPrimeIndexing CompletedUnitBallGauge NumberFieldModel

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

variable (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
  [hξ : ξ.IsUltrametric]

/-- Genuine coherence identifies the literal completed global span with
the literal completed norm unit ball, via the original canonical tensor map. -/
theorem HasFiniteNormExceptions.completedUnitBallModule_eq_completedLatticeSpan
    (hc : ξ.HasFiniteNormExceptions) (p : HeightOneSpectrum (𝓞 K)) :
    ξ.completedUnitBallModule (normalizedPrimeParameter p)
      (normalizedPrimeParameter_mem_fin p) =
      completedLatticeSpan (ξ.globalUnitBallModule) p := by
  let := completedVector_integralScalarTower (E := E) p
  let B := ξ.completedUnitBallModule (normalizedPrimeParameter p)
    (normalizedPrimeParameter_mem_fin p)
  have hm : completedLatticeTensorMap (ξ.globalUnitBallModule) p =
      B.subtype.comp (ξ.normalizedGlobalUnitBallCompletedTensorMap p) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    rw [completedLatticeTensorMap_tmul, LinearMap.comp_apply,
      ξ.normalizedGlobalUnitBallCompletedTensorMap_tmul]
    change (a : ((normalizedNumberFieldAdelicStructure K).ϕ
      (normalizedPrimeParameter p)).Completion) ⊗ₜ[K] (x : E) =
      (a : ((normalizedNumberFieldAdelicStructure K).ϕ
        (normalizedPrimeParameter p)).Completion) • (1 ⊗ₜ[K] (x : E))
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hs := (hc.normalizedGlobalUnitBallCompletedTensorMap_bijective hξ p).surjective
  rw [← range_completedLatticeTensorMap, hm, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr hs, Submodule.map_top, Submodule.range_subtype]

/-- Actual coherence and finite generation produce a common rational
completed frame for the actual gauge family away from finitely many primes. -/
theorem HasFiniteNormExceptions.exists_latticeGaugeFamily_basis_norm_off_finite
    (hc : ξ.HasFiniteNormExceptions) (hfg : (ξ.globalUnitBallModule).FG)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι K E) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ p ∉ T, ∀ z,
      (ξ.latticeGaugeFamily).norm (normalizedPrimeParameter p) z =
        (ofBasis (normalizedNumberFieldAdelicStructure K) E b).norm
          (normalizedPrimeParameter p) z := by
  classical
  have hspan := (hasFiniteNormExceptions_iff_span_normalizedGlobalUnitBall_eq_top ξ).mp hc
  obtain ⟨f, hf, hfinite, hframe⟩ := exists_completed_lattice_gauge_frame
    (ξ.globalUnitBallModule) hfg hspan b
  refine ⟨hfinite.toFinset, ?_⟩
  intro p hp z
  have hpf : f ∉ p.asIdeal := by simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hp
  rw [ξ.latticeGaugeFamily_norm_finite _ (normalizedPrimeParameter_mem_fin p)]
  unfold completedUnitBallGauge
  rw [← ξ.coe_completedUnitBallModule _ (normalizedPrimeParameter_mem_fin p),
    hc.completedUnitBallModule_eq_completedLatticeSpan ξ p]
  exact hframe p hpf z

/-- Finite generation and genuine coherence prove domination of the produced
actual gauge family; no model norm or domination conclusion is assumed. -/
theorem HasFiniteNormExceptions.latticeGaugeFamily_isDominated
    (hc : ξ.HasFiniteNormExceptions) (hfg : (ξ.globalUnitBallModule).FG) :
    (ξ.latticeGaugeFamily).IsDominated := by
  let b := Module.finBasis K E
  obtain ⟨T, hT⟩ := hc.exists_latticeGaugeFamily_basis_norm_off_finite ξ hfg b
  exact isDominated_of_basisGauge_eq_off_finite_primes (ξ.latticeGaugeFamily) b T hT

include hξ in
/-- Domination and genuine coherence make the literal source impurity finite. -/
theorem IsDominated.globalImpurity_ne_top
    (hd : ξ.IsDominated) (hc : ξ.HasFiniteNormExceptions) : ξ.globalImpurity ≠ ⊤ := by
  have hg := hc.latticeGaugeFamily_isDominated ξ
    (hd.fg_normalizedGlobalUnitBallModule hξ)
  have hs := (ξ.isStronglyDominated_iff_isDominated_of_ultrametric
   ).mpr hd
  have hgs := ((ξ.latticeGaugeFamily).isStronglyDominated_iff_isDominated_of_ultrametric
    (hξ := (ξ.latticeGaugeFamily_isUltrametric))).mpr hg
  apply (ξ.globalImpurity_ne_top_iff_localDist_hasIntegrableUpperBound).mpr
  exact (hs.localDist hgs ((normalizedNumberFieldAdelicStructure K).v_Ωinf_lt_top_of_isRCLike
   )).1

/-- Source Proposition 4.4.9 on the actual normalized curve: under genuine
coherence, domination is equivalent to finite generation and finite impurity. -/
theorem isDominated_iff_globalUnitBall_fg_and_globalImpurity_ne_top
    [hc : ξ.HasFiniteNormExceptions] :
    ξ.IsDominated ↔ (ξ.globalUnitBallModule).FG ∧ ξ.globalImpurity ≠ ⊤ := by
  constructor
  · intro hd
    exact ⟨hd.fg_normalizedGlobalUnitBallModule hξ, hd.globalImpurity_ne_top ξ hc⟩
  · rintro ⟨hfg, hσ⟩
    exact ξ.isDominated_of_latticeGaugeFamily_of_globalImpurity_ne_top
      (hg := (hc.latticeGaugeFamily_isDominated ξ hfg)) hσ

end ArakelovGeometry.NormFamily
