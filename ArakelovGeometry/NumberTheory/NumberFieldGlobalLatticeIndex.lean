/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberFieldFiniteModuleCardinality
public import ArakelovGeometry.NumberTheory.NumberFieldFullLatticeIntegerBasis
public import ArakelovGeometry.NumberTheory.NumberFieldLocalDeterminantValuation
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# The global index of the original full number-field lattices

The quotient is the literal quotient of the original integral lattices. Its
finite cardinality, its actual local cokernels, and the local-length product
are derived without assuming a global determinant-index comparison.
-/

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain TensorProduct
open scoped NumberField TensorProduct

namespace ArakelovGeometry.NumberFieldFullLattice

open AdelicStructure ActualPrimeIndexing NumberFieldFiniteModule
attribute [local instance 2000] Algebra.toModule Algebra.toSMul

universe u v
variable {K : Type u} [Field K] [NumberField K]
  {E : Type v} [AddCommGroup E] [Module K E]

/-- The image of the smaller original lattice inside the larger original lattice. -/
def integralLatticeImage (L₀ L : Submodule (𝓞 K) E) : Submodule (𝓞 K) L :=
  L₀.comap L.subtype

/-- The actual original submodule and its inclusion image are canonically identified. -/
def integralLatticeImageEquiv {L₀ L : Submodule (𝓞 K) E} (h : L₀ ≤ L) :
    integralLatticeImage L₀ L ≃ₗ[𝓞 K] L₀ :=
  Submodule.comapSubtypeEquivOfLe h

omit [NumberField K] in
/-- Its quotient cardinality is exactly the additive relative index. -/
theorem integralLatticeQuotient_card_eq_relIndex (L₀ L : Submodule (𝓞 K) E) :
    Nat.card (L ⧸ integralLatticeImage L₀ L) =
      L₀.toAddSubgroup.relIndex L.toAddSubgroup := rfl

local notation "indexLocalRing" => fun (p : HeightOneSpectrum (𝓞 K)) ↦
  AdelicStructure.rationalLocalRing (normalizedNumberFieldAdelicStructure K)
    (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p)

/-- Scalar extension of the original inclusion is the actual local inclusion. -/
theorem rationalLocalTensorEquiv_inclusion {L₀ L : Submodule (𝓞 K) E} (h : L₀ ≤ L)
    (p : HeightOneSpectrum (𝓞 K)) :
    (rationalLocalTensorEquiv L p).toLinearMap ∘ₗ
        AlgebraTensorModule.lTensor (indexLocalRing p) (indexLocalRing p)
          (Submodule.inclusion h) =
      rationalLocalLatticeInclusion h p ∘ₗ (rationalLocalTensorEquiv L₀ p).toLinearMap := by
  apply AlgebraTensorModule.ext
  intro r x
  apply Subtype.ext
  change (rationalLocalTensorEquiv L p (r ⊗ₜ[𝓞 K] Submodule.inclusion h x) : E) =
    (rationalLocalTensorEquiv L₀ p (r ⊗ₜ[𝓞 K] x) : E)
  rw [rationalLocalTensorEquiv_tmul, rationalLocalTensorEquiv_tmul]
  rfl

/-- The original inclusion image extends to the actual local inclusion image. -/
theorem map_integralLatticeImage_tensor_range {L₀ L : Submodule (𝓞 K) E} (h : L₀ ≤ L)
    (p : HeightOneSpectrum (𝓞 K)) :
    Submodule.map (rationalLocalTensorEquiv L p).toLinearMap
      (AlgebraTensorModule.lTensor (indexLocalRing p) (indexLocalRing p)
        (integralLatticeImage L₀ L).subtype).range = rationalLocalLatticeImage h p := by
  let e := LinearEquiv.baseChange (𝓞 K) (indexLocalRing p) _ _
    (integralLatticeImageEquiv h).symm
  let f := AlgebraTensorModule.lTensor (indexLocalRing p) (indexLocalRing p)
    (integralLatticeImage L₀ L).subtype
  have hf : f ∘ₗ e.toLinearMap =
      AlgebraTensorModule.lTensor (indexLocalRing p) (indexLocalRing p)
        (Submodule.inclusion h) := by
    apply AlgebraTensorModule.ext
    intro r x
    rfl
  calc
    _ = ((rationalLocalTensorEquiv L p).toLinearMap ∘ₗ f).range :=
      (LinearMap.range_comp f (rationalLocalTensorEquiv L p).toLinearMap).symm
    _ = (((rationalLocalTensorEquiv L p).toLinearMap ∘ₗ f) ∘ₗ e.toLinearMap).range :=
      (e.range_comp _).symm
    _ = (rationalLocalLatticeInclusion h p ∘ₗ
        (rationalLocalTensorEquiv L₀ p).toLinearMap).range := by
      rw [LinearMap.comp_assoc, hf, rationalLocalTensorEquiv_inclusion]
    _ = _ := (rationalLocalTensorEquiv L₀ p).range_comp _

/-- The literal original quotient localizes to the literal actual local cokernel. -/
def integralLatticeQuotientLocalEquiv {L₀ L : Submodule (𝓞 K) E} (h : L₀ ≤ L)
    (p : HeightOneSpectrum (𝓞 K)) :
    indexLocalRing p ⊗[𝓞 K] (L ⧸ integralLatticeImage L₀ L) ≃ₗ[indexLocalRing p]
      rationalLocalSpan L p ⧸ rationalLocalLatticeImage h p :=
  (AlgebraTensorModule.tensorQuotientEquiv (indexLocalRing p) (𝓞 K)
    (indexLocalRing p) (integralLatticeImage L₀ L)).trans
    (Submodule.Quotient.equiv _ _ (rationalLocalTensorEquiv L p)
      (map_integralLatticeImage_tensor_range h p))

variable [FiniteDimensional K E]

/-- Finite generation and full rational span prove finiteness of the original quotient. -/
theorem integralLatticeQuotient_finite (L₀ L : Submodule (𝓞 K) E) (h : L₀ ≤ L)
    (hfg₀ : L₀.FG) (hfg : L.FG)
    (hspan₀ : Submodule.span K (L₀ : Set E) = ⊤)
    (hspan : Submodule.span K (L : Set E) = ⊤) :
    Finite (L ⧸ integralLatticeImage L₀ L) := by
  let := finite_integer L hfg
  let := free_integer L hfg
  let N := (integralLatticeImage L₀ L).restrictScalars ℤ
  have hrank : Module.finrank ℤ N = Module.finrank ℤ L := by
    change Module.finrank ℤ (integralLatticeImage L₀ L) = _
    rw [(integralLatticeImageEquiv h).restrictScalars ℤ |>.finrank_eq,
      finrank_integer L₀ hfg₀ hspan₀, finrank_integer L hfg hspan]
  let := Submodule.finiteQuotientOfFreeOfRankEq N hrank
  exact Finite.of_equiv (L ⧸ N)
    (Submodule.Quotient.restrictScalarsEquiv ℤ (integralLatticeImage L₀ L)).toEquiv

open Classical in
/-- One list of actual primes computes the original relative index and every
literal local quotient length, without an index-comparison assumption. -/
theorem integralLattice_exists_primeFactors
    (L₀ L : Submodule (𝓞 K) E) (h : L₀ ≤ L) (hfg₀ : L₀.FG) (hfg : L.FG)
    (hspan₀ : Submodule.span K (L₀ : Set E) = ⊤)
    (hspan : Submodule.span K (L : Set E) = ⊤) :
    ∃ P : List (HeightOneSpectrum (𝓞 K)),
      L₀.toAddSubgroup.relIndex L.toAddSubgroup =
        (P.map fun p => Ideal.absNorm p.asIdeal).prod ∧
      ∀ p : HeightOneSpectrum (𝓞 K),
        Module.length (indexLocalRing p)
          (rationalLocalSpan L p ⧸ rationalLocalLatticeImage h p) = (P.count p : ℕ∞) := by
  classical
  let := integralLatticeQuotient_finite L₀ L h hfg₀ hfg hspan₀ hspan
  obtain ⟨P, hcard, hlength⟩ := exists_primeFactors (K := K) (L ⧸ integralLatticeImage L₀ L)
  refine ⟨P, (integralLatticeQuotient_card_eq_relIndex L₀ L).symm.trans hcard, ?_⟩
  intro p
  let := rationalCoefficients_isLocalization p
  exact (integralLatticeQuotientLocalEquiv h p).length_eq.symm.trans
    (hlength p (indexLocalRing p))

/-- Only finitely many actual primes contribute to the original lattice index. -/
theorem rationalLocalLattice_length_support_finite
    (L₀ L : Submodule (𝓞 K) E) (h : L₀ ≤ L) (hfg₀ : L₀.FG) (hfg : L.FG)
    (hspan₀ : Submodule.span K (L₀ : Set E) = ⊤)
    (hspan : Submodule.span K (L : Set E) = ⊤) :
    (Function.support fun p : HeightOneSpectrum (𝓞 K) =>
      Module.length (indexLocalRing p)
        (rationalLocalSpan L p ⧸ rationalLocalLatticeImage h p)).Finite := by
  classical
  obtain ⟨P, _, hlength⟩ := integralLattice_exists_primeFactors L₀ L h hfg₀ hfg hspan₀ hspan
  apply P.toFinset.finite_toSet.subset
  intro p hp
  by_contra h
  have hc : P.count p = 0 := List.count_eq_zero_of_not_mem (by simpa using h)
  apply hp
  dsimp only
  rw [hlength p, hc, Nat.cast_zero]

/-- The original additive relative index is the product of the actual residue
norms raised to the actual local quotient lengths. The preceding finiteness
theorems justify both the natural exponents and the finite product. -/
theorem integralLattice_relIndex_eq_finprod_localLength
    (L₀ L : Submodule (𝓞 K) E) (h : L₀ ≤ L) (hfg₀ : L₀.FG) (hfg : L.FG)
    (hspan₀ : Submodule.span K (L₀ : Set E) = ⊤)
    (hspan : Submodule.span K (L : Set E) = ⊤) :
    L₀.toAddSubgroup.relIndex L.toAddSubgroup =
      ∏ᶠ p : HeightOneSpectrum (𝓞 K), Ideal.absNorm p.asIdeal ^
        (Module.length (indexLocalRing p)
          (rationalLocalSpan L p ⧸ rationalLocalLatticeImage h p)).toNat := by
  classical
  obtain ⟨P, hcard, hlength⟩ := integralLattice_exists_primeFactors L₀ L h hfg₀ hfg hspan₀ hspan
  rw [hcard, list_prod_absNorm_eq_finprod]
  apply finprod_congr
  intro p
  rw [hlength p, ENat.toNat_natCast]

/-- The finite contribution in the global index formula is a genuine finite
logarithmic sum over actual primes. -/
theorem integralLattice_log_relIndex_eq_tsum_localLength
    (L₀ L : Submodule (𝓞 K) E) (h : L₀ ≤ L) (hfg₀ : L₀.FG) (hfg : L.FG)
    (hspan₀ : Submodule.span K (L₀ : Set E) = ⊤)
    (hspan : Submodule.span K (L : Set E) = ⊤) :
    Real.log (L₀.toAddSubgroup.relIndex L.toAddSubgroup) =
      ∑' p : HeightOneSpectrum (𝓞 K),
        ((Module.length (indexLocalRing p)
          (rationalLocalSpan L p ⧸ rationalLocalLatticeImage h p)).toNat : ℝ) *
            Real.log (Ideal.absNorm p.asIdeal) := by
  classical
  let ℓ := fun p : HeightOneSpectrum (𝓞 K) => Module.length (indexLocalRing p)
    (rationalLocalSpan L p ⧸ rationalLocalLatticeImage h p)
  have hs : (Function.support ℓ).Finite :=
    rationalLocalLattice_length_support_finite L₀ L h hfg₀ hfg hspan₀ hspan
  let s := hs.toFinset
  have hzero (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ s) : ℓ p = 0 := by
    exact not_not.mp (by simpa only [s, Set.Finite.mem_toFinset, Function.mem_support] using hp)
  have hprod : L₀.toAddSubgroup.relIndex L.toAddSubgroup =
      ∏ p ∈ s, Ideal.absNorm p.asIdeal ^ (ℓ p).toNat := by
    rw [integralLattice_relIndex_eq_finprod_localLength L₀ L h hfg₀ hfg hspan₀ hspan]
    apply finprod_eq_finsetProd_of_mulSupport_subset
    intro p hp
    by_contra hps
    exact hp (by simp only [ℓ, hzero p hps, ENat.toNat_zero, pow_zero])
  rw [hprod, Nat.cast_prod]
  simp only [Nat.cast_pow]
  rw [Real.log_prod (fun p _ => pow_ne_zero _ (Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot)))]
  simp_rw [Real.log_pow]
  exact (tsum_eq_sum (s := s) (fun p hp => by
    simp only [ℓ, hzero p hp, ENat.toNat_zero, Nat.cast_zero, zero_mul])).symm

/-- The actual normalization weights turn the local determinant logarithms
into the logarithm of the original additive relative index. -/
theorem integralLattice_log_relIndex_eq_weighted_tsum_log_det
    (L₀ L : Submodule (𝓞 K) E) (h : L₀ ≤ L) (hfg₀ : L₀.FG) (hfg : L.FG)
    (hspan₀ : Submodule.span K (L₀ : Set E) = ⊤)
    (hspan : Submodule.span K (L : Set E) = ⊤) :
    Real.log (L₀.toAddSubgroup.relIndex L.toAddSubgroup) =
      ∑' p : HeightOneSpectrum (𝓞 K),
        (normalizedNumberFieldAdelicStructure K).v.real {normalizedPrimeParameter p} *
          (-Real.log ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p)
            ((LinearMap.toMatrix (rationalLocalBasisFinrank L₀ hfg₀ hspan₀ p)
              (rationalLocalBasisFinrank L hfg hspan p)
              (rationalLocalLatticeInclusion h p)).det : K))) := by
  rw [integralLattice_log_relIndex_eq_tsum_localLength L₀ L h hfg₀ hfg hspan₀ hspan]
  apply tsum_congr
  intro p
  rw [rationalLocalLattice_normalized_log_det L₀ L h hfg₀ hfg hspan₀ hspan p,
    neg_mul, neg_neg, ← mul_assoc, normalized_weighted_prime_log_scale]
  exact mul_comm _ _

end ArakelovGeometry.NumberFieldFullLattice
