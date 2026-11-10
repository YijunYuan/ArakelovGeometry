/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldImpurityDistance
import ArakelovGeometry.NumberTheory.NumberFieldPrincipalCompletedFrame
import ArakelovGeometry.NumberTheory.NormFamilyNormalizedLatticeModel
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldNormalizationHermitian
import ArakelovGeometry.AdelicVectorBundle.StrongSubquotient

/-!
# Domination, the literal global ball, and actual impurity

Genuine coherence reconstructs each actual completed ball from the literal
global integral module. Its finite generation supplies a common completed
frame outside finitely many actual primes and proves domination of the
actual lattice-gauge family. This gives source Proposition 4.4.9.
-/

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal TensorProduct NumberField

noncomputable section

namespace ArakelovGeometry.NormFamily

open AdelicStructure ActualPrimeIndexing CompletedUnitBallGauge NumberFieldModel

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

variable (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
  (hξ : ξ.IsUltrametric)

/-- Genuine coherence identifies the literal completed global span with
the literal completed norm unit ball, via the original canonical tensor map. -/
theorem HasFiniteNormExceptions.completedUnitBallModule_eq_completedLatticeSpan
    (hc : ξ.HasFiniteNormExceptions) (p : HeightOneSpectrum (𝓞 K)) :
    ξ.completedUnitBallModule (normalizedPrimeParameter p)
      (normalizedPrimeParameter_mem_fin p) hξ =
      completedLatticeSpan (ξ.globalUnitBallModule hξ) p := by
  let := completedVector_integralScalarTower (E := E) p
  let B := ξ.completedUnitBallModule (normalizedPrimeParameter p)
    (normalizedPrimeParameter_mem_fin p) hξ
  have hm : completedLatticeTensorMap (ξ.globalUnitBallModule hξ) p =
      B.subtype.comp (ξ.normalizedGlobalUnitBallCompletedTensorMap hξ p) := by
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
    (hc : ξ.HasFiniteNormExceptions) (hfg : (ξ.globalUnitBallModule hξ).FG)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι K E) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ p ∉ T, ∀ z,
      (ξ.latticeGaugeFamily hξ).norm (normalizedPrimeParameter p) z =
        (ofBasis (normalizedNumberFieldAdelicStructure K) E b).norm
          (normalizedPrimeParameter p) z := by
  classical
  have hspan := (hasFiniteNormExceptions_iff_span_normalizedGlobalUnitBall_eq_top ξ hξ).mp hc
  obtain ⟨f, hf, hfinite, hframe⟩ := exists_completed_lattice_gauge_frame
    (ξ.globalUnitBallModule hξ) hfg hspan b
  refine ⟨hfinite.toFinset, ?_⟩
  intro p hp z
  have hpf : f ∉ p.asIdeal := by simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hp
  rw [ξ.latticeGaugeFamily_norm_finite hξ _ (normalizedPrimeParameter_mem_fin p)]
  unfold completedUnitBallGauge
  rw [← ξ.coe_completedUnitBallModule _ (normalizedPrimeParameter_mem_fin p) hξ,
    hc.completedUnitBallModule_eq_completedLatticeSpan ξ hξ p]
  exact hframe p hpf z

/-- Finite generation and genuine coherence prove domination of the produced
actual gauge family; no model norm or domination conclusion is assumed. -/
theorem HasFiniteNormExceptions.latticeGaugeFamily_isDominated
    (hc : ξ.HasFiniteNormExceptions) (hfg : (ξ.globalUnitBallModule hξ).FG) :
    (ξ.latticeGaugeFamily hξ).IsDominated := by
  let b := Module.finBasis K E
  obtain ⟨T, hT⟩ := hc.exists_latticeGaugeFamily_basis_norm_off_finite ξ hξ hfg b
  exact isDominated_of_basisGauge_eq_off_finite_primes (ξ.latticeGaugeFamily hξ) b T hT

include hξ in
/-- Domination and genuine coherence make the literal source impurity finite. -/
theorem IsDominated.globalImpurity_ne_top
    (hd : ξ.IsDominated) (hc : ξ.HasFiniteNormExceptions) : ξ.globalImpurity ≠ ⊤ := by
  have hg := hc.latticeGaugeFamily_isDominated ξ hξ
    (hd.fg_normalizedGlobalUnitBallModule hξ)
  have hs := (ξ.isStronglyDominated_iff_isDominated_of_ultrametric hξ
    normalizedNumberFieldArchimedeanCompletions).mpr hd
  have hgs := ((ξ.latticeGaugeFamily hξ).isStronglyDominated_iff_isDominated_of_ultrametric
    (ξ.latticeGaugeFamily_isUltrametric hξ) normalizedNumberFieldArchimedeanCompletions).mpr hg
  apply (ξ.globalImpurity_ne_top_iff_localDist_hasIntegrableUpperBound hξ).mpr
  exact (hs.localDist hgs ((normalizedNumberFieldAdelicStructure K).v_Ωinf_lt_top_of_isRCLike
    normalizedNumberFieldArchimedeanCompletions)).1

/-- Source Proposition 4.4.9 on the actual normalized curve: under genuine
coherence, domination is equivalent to finite generation and finite impurity. -/
theorem isDominated_iff_globalUnitBall_fg_and_globalImpurity_ne_top
    (hc : ξ.HasFiniteNormExceptions) :
    ξ.IsDominated ↔ (ξ.globalUnitBallModule hξ).FG ∧ ξ.globalImpurity ≠ ⊤ := by
  constructor
  · intro hd
    exact ⟨hd.fg_normalizedGlobalUnitBallModule hξ, hd.globalImpurity_ne_top ξ hξ hc⟩
  · rintro ⟨hfg, hσ⟩
    exact ξ.isDominated_of_latticeGaugeFamily_of_globalImpurity_ne_top hξ
      (hc.latticeGaugeFamily_isDominated ξ hξ hfg) hσ

end ArakelovGeometry.NormFamily
