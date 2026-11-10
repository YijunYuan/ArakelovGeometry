/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberFieldLocalDeterminantGauge
public import ArakelovGeometry.NumberTheory.NumberFieldLocalDeterminantValuation

/-!
# Actual local determinant gauges and localized quotient lengths
-/

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct

namespace ArakelovGeometry.NumberFieldLocalDeterminantComparison

open AdelicStructure ActualPrimeIndexing NumberFieldFullLattice NumberFieldLocalDeterminantGauge

attribute [local instance 2000] Algebra.toModule Algebra.toSMul

variable {K E : Type*} [Field K] [NumberField K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local notation "comparisonCoefficientRing" => fun (p : HeightOneSpectrum (𝓞 K)) ↦
  AdelicStructure.rationalLocalRing (normalizedNumberFieldAdelicStructure K)
    (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p)

omit [FiniteDimensional K E] in
/-- The generic rank-reindexed basis consists of the original vectors of the local basis. -/
theorem localRankBasis_coe (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K))
    (i : Fin (Module.finrank K E)) :
    localRankBasis L hfg hspan p i = (rationalLocalBasisFinrank L hfg hspan p i : E) := by
  simp only [localRankBasis, rationalLocalBasisFinrank, Module.Basis.reindex_apply,
    rationalLocalGenericBasis_coe]

omit [FiniteDimensional K E] in
/-- Actual local coordinates map to the rational coordinates in the produced generic basis. -/
theorem localRankBasis_repr_coe (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K))
    (x : rationalLocalSpan L p) (i : Fin (Module.finrank K E)) :
    (localRankBasis L hfg hspan p).repr (x : E) i =
      algebraMap (comparisonCoefficientRing p) K
        ((rationalLocalBasisFinrank L hfg hspan p).repr x i) := by
  let b := rationalLocalBasisFinrank L hfg hspan p
  let β := localRankBasis L hfg hspan p
  have hsum : (x : E) = ∑ j, algebraMap (comparisonCoefficientRing p) K (b.repr x j) • β j := by
    have hx := congrArg (fun y : rationalLocalSpan L p => (y : E)) (b.sum_repr x)
    rw [Submodule.coe_sum] at hx
    rw [← hx]
    apply Finset.sum_congr rfl
    intro j _
    rw [show β j = (b j : E) from localRankBasis_coe L hfg hspan p j]
    rfl
  change β.repr (x : E) i = algebraMap (comparisonCoefficientRing p) K (b.repr x i)
  rw [hsum]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Module.Basis.repr_self_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [FiniteDimensional K E] in
/-- The literal local inclusion matrix maps to the rational generic coordinate matrix. -/
theorem map_localInclusionMatrix
    (L₀ L : Submodule (𝓞 K) E) (h : L₀ ≤ L) (hfg₀ : L₀.FG) (hfg : L.FG)
    (hspan₀ : Submodule.span K (L₀ : Set E) = ⊤)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K)) :
    (LinearMap.toMatrix (rationalLocalBasisFinrank L₀ hfg₀ hspan₀ p)
      (rationalLocalBasisFinrank L hfg hspan p) (rationalLocalLatticeInclusion h p)).map
        (algebraMap (comparisonCoefficientRing p) K) =
      (localRankBasis L hfg hspan p).toMatrix (localRankBasis L₀ hfg₀ hspan₀ p) := by
  ext i j
  simp only [Matrix.map_apply, LinearMap.toMatrix_apply, Module.Basis.toMatrix_apply]
  rw [localRankBasis_coe L₀ hfg₀ hspan₀ p j]
  exact (localRankBasis_repr_coe L hfg hspan p
    (rationalLocalLatticeInclusion h p (rationalLocalBasisFinrank L₀ hfg₀ hspan₀ p j)) i).symm

omit [FiniteDimensional K E] in
/-- The actual local inclusion determinant is the rational coordinate determinant. -/
theorem localInclusion_det_coe
    (L₀ L : Submodule (𝓞 K) E) (h : L₀ ≤ L) (hfg₀ : L₀.FG) (hfg : L.FG)
    (hspan₀ : Submodule.span K (L₀ : Set E) = ⊤)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K)) :
    ((LinearMap.toMatrix (rationalLocalBasisFinrank L₀ hfg₀ hspan₀ p)
      (rationalLocalBasisFinrank L hfg hspan p) (rationalLocalLatticeInclusion h p)).det : K) =
      (localRankBasis L hfg hspan p).det (localRankBasis L₀ hfg₀ hspan₀ p) := by
  rw [Module.Basis.det_apply, ← map_localInclusionMatrix L₀ L h hfg₀ hfg hspan₀ hspan p]
  exact (algebraMap (comparisonCoefficientRing p) K).map_det _

/-- The completed finite determinant gauge of the smaller actual local basis wedge
reads the actual local quotient length, with the produced normalized scale. -/
theorem fullLatticeGaugeFamily_determinant_log_localInclusion
    (L₀ L : Submodule (𝓞 K) E) (h : L₀ ≤ L) (hfg₀ : L₀.FG) (hfg : L.FG)
    (hspan₀ : Submodule.span K (L₀ : Set E) = ⊤)
    (hspan : Submodule.span K (L : Set E) = ⊤)
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (p : HeightOneSpectrum (𝓞 K)) :
    Real.log ((fullLatticeGaugeFamily L hfg hspan η).determinant.norm
      (normalizedPrimeParameter p)
      ((1 : ((normalizedNumberFieldAdelicStructure K).ϕ
        (normalizedPrimeParameter p)).Completion) ⊗ₜ[K]
          exteriorPower.ιMulti K _ (localRankBasis L₀ hfg₀ hspan₀ p))) =
      -normalizedPlaceLogScale (normalizedPrimeParameter p) *
        ((Module.length (comparisonCoefficientRing p)
          (rationalLocalSpan L p ⧸ rationalLocalLatticeImage h p)).toNat : ℝ) := by
  rw [fullLatticeGaugeFamily_determinant_norm_rational_wedge,
    ← localInclusion_det_coe L₀ L h hfg₀ hfg hspan₀ hspan p,
    AdelicStructure.norm_algebraMap_eq_absValue]
  exact rationalLocalLattice_normalized_log_det L₀ L h hfg₀ hfg hspan₀ hspan p

end ArakelovGeometry.NumberFieldLocalDeterminantComparison
