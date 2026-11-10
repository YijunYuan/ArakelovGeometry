/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.HermitianBasis
import ArakelovGeometry.NumberTheory.NormFamilyNormalizedLatticeModel
import ArakelovGeometry.NumberTheory.NormalizedNumberFieldInfiniteMass
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldNormalizationHermitian
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# The actual nonpure rational plane obstruction

The norms use the actual completed fibres of the rationally normalized
number-field curve. One finite norm is a sheared coordinate maximum with
second weight `sqrt p`; infinity retains the Euclidean coordinate norm.
-/

open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NonpureNumberFieldMinkowskiObstruction

open AdelicStructure ActualPrimeIndexing NormFamily

abbrev S := normalizedNumberFieldAdelicStructure ℚ
abbrev Plane := Fin 2 → ℚ

def standardBasis : Module.Basis (Fin 2) ℚ Plane := Pi.basisFun ℚ (Fin 2)

def primeIdeal (p : Nat.Primes) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p

def primePoint (p : Nat.Primes) : S.Ω := normalizedPrimeParameter (primeIdeal p)

theorem primePoint_mem_fin (p : Nat.Primes) : primePoint p ∈ S.Ωfin :=
  normalizedPrimeParameter_mem_fin _

def completedCoordinates (ω : S.Ω) :
    ((S.ϕ ω).Completion ⊗[ℚ] Plane) ≃ₗ[(S.ϕ ω).Completion]
      (Fin 2 → (S.ϕ ω).Completion) :=
  (standardBasis.baseChange (S.ϕ ω).Completion).equivFun

def firstCoordinate (ω : S.Ω) :
    ((S.ϕ ω).Completion ⊗[ℚ] Plane) →ₗ[(S.ϕ ω).Completion] (S.ϕ ω).Completion :=
  (LinearMap.proj 0).comp (completedCoordinates ω).toLinearMap

def shearedCoordinate (a : ℤ) (ω : S.Ω) :
    ((S.ϕ ω).Completion ⊗[ℚ] Plane) →ₗ[(S.ϕ ω).Completion] (S.ϕ ω).Completion :=
  (((LinearMap.proj 1 : (Fin 2 → (S.ϕ ω).Completion) →ₗ[(S.ϕ ω).Completion]
      (S.ϕ ω).Completion)) - algebraMap ℚ (S.ϕ ω).Completion (a : ℚ) •
        LinearMap.proj 0).comp (completedCoordinates ω).toLinearMap

/-- A literal weighted maximum seminorm on the actual completed fibre. -/
def exceptionalSeminorm (p : Nat.Primes) (a : ℤ) (ω : S.Ω) :
    Seminorm (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[ℚ] Plane) :=
  ((normSeminorm (S.ϕ ω).Completion (S.ϕ ω).Completion).comp (firstCoordinate ω)) ⊔
    (NNReal.mk (Real.sqrt (p : ℝ)) (Real.sqrt_nonneg _)) •
      ((normSeminorm (S.ϕ ω).Completion (S.ϕ ω).Completion).comp (shearedCoordinate a ω))

theorem exceptionalSeminorm_apply (p : Nat.Primes) (a : ℤ) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[ℚ] Plane) :
    exceptionalSeminorm p a ω z = max ‖completedCoordinates ω z 0‖
      (Real.sqrt (p : ℝ) * ‖completedCoordinates ω z 1 -
        algebraMap ℚ (S.ϕ ω).Completion (a : ℚ) * completedCoordinates ω z 0‖) := rfl

theorem exceptionalSeminorm_eq_zero_iff (p : Nat.Primes) (a : ℤ) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[ℚ] Plane) :
    exceptionalSeminorm p a ω z = 0 ↔ z = 0 := by
  have hp : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast p.property.pos)
  constructor
  · intro hz
    rw [exceptionalSeminorm_apply] at hz
    have hx : completedCoordinates ω z 0 = 0 := by
      apply norm_eq_zero.mp
      apply le_antisymm _ (norm_nonneg _)
      exact (le_max_left _ _).trans_eq hz
    have hy : completedCoordinates ω z 1 = 0 := by
      have hle := (le_max_right _ _).trans_eq hz
      rw [hx, mul_zero, sub_zero] at hle
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (completedCoordinates ω z 1)]
    apply (completedCoordinates ω).injective
    ext i
    fin_cases i
    · exact hx
    · exact hy
  · rintro rfl
    exact map_zero (exceptionalSeminorm p a ω)

/-- The original actual completed family of the rational obstruction. -/
def family (p : Nat.Primes) (a : ℤ) : NormFamily S Plane := by
  classical
  exact
    { norm := fun ω => if ω = primePoint p then exceptionalSeminorm p a ω
        else (ofBasisHermitian S Plane standardBasis).norm ω
      norm_eq_zero_iff := fun ω z => by
        split_ifs
        · exact exceptionalSeminorm_eq_zero_iff p a ω z
        · exact (ofBasisHermitian S Plane standardBasis).norm_eq_zero_iff ω z }

theorem family_norm_prime (p : Nat.Primes) (a : ℤ)
    (z : (S.ϕ (primePoint p)).Completion ⊗[ℚ] Plane) :
    (family p a).norm (primePoint p) z = exceptionalSeminorm p a (primePoint p) z := by
  classical
  simp [family]

theorem family_norm_off_prime (p : Nat.Primes) (a : ℤ) (ω : S.Ω)
    (hω : ω ≠ primePoint p) (z : (S.ϕ ω).Completion ⊗[ℚ] Plane) :
    (family p a).norm ω z = (ofBasisHermitian S Plane standardBasis).norm ω z := by
  classical
  simp only [family, if_neg hω]

theorem exceptionalSeminorm_add_le_max (p : Nat.Primes) (a : ℤ) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (z w : (S.ϕ ω).Completion ⊗[ℚ] Plane) :
    exceptionalSeminorm p a ω (z + w) ≤
      max (exceptionalSeminorm p a ω z) (exceptionalSeminorm p a ω w) := by
  change max ‖firstCoordinate ω (z + w)‖
      (Real.sqrt (p : ℝ) * ‖shearedCoordinate a ω (z + w)‖) ≤
    max (max ‖firstCoordinate ω z‖ (Real.sqrt (p : ℝ) * ‖shearedCoordinate a ω z‖))
      (max ‖firstCoordinate ω w‖ (Real.sqrt (p : ℝ) * ‖shearedCoordinate a ω w‖))
  rw [map_add, map_add, max_max_max_comm]
  apply max_le_max
  · exact norm_add_le_max_of_finite S ω hω _ _
  · rw [← mul_max_of_nonneg _ _ (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (norm_add_le_max_of_finite S ω hω _ _)
      (Real.sqrt_nonneg _)

theorem family_isUltrametric (p : Nat.Primes) (a : ℤ) : (family p a).IsUltrametric := by
  intro ω hω z w
  by_cases hp : ω = primePoint p
  · subst ω
    simp only [family_norm_prime]
    exact exceptionalSeminorm_add_le_max p a _ hω z w
  · simp only [family_norm_off_prime p a ω hp]
    exact ofBasisHermitian_isUltrametric standardBasis ω hω z w

/-- The family is a genuine finite modification of completed basis norms. -/
theorem family_coherent_and_dominated (p : Nat.Primes) (a : ℤ) :
    (family p a).HasFiniteNormExceptions ∧ (family p a).IsDominated := by
  classical
  apply coherent_and_dominated_of_basisGauge_eq_off_finite_primes
    (family p a) standardBasis {primeIdeal p}
  intro q hq z
  have hqp : normalizedPrimeParameter q ≠ primePoint p := by
    intro h
    exact hq (Finset.mem_singleton.mpr (normalizedPrimeParameter_injective h))
  rw [family_norm_off_prime p a _ hqp,
    ofBasisHermitian_norm_of_finite standardBasis _ (normalizedPrimeParameter_mem_fin q)]

theorem family_isMeasurable (p : Nat.Primes) (a : ℤ) : (family p a).IsMeasurable := by
  let : DiscreteMeasurableSpace S.Ω := inferInstanceAs
    (DiscreteMeasurableSpace {ω : AbsoluteValue.Place ℚ // ω ≠ AbsoluteValue.trivialPlace ℚ})
  exact (family p a).isMeasurable_of_discrete

theorem family_dual_isMeasurable (p : Nat.Primes) (a : ℤ) : (family p a).dual.IsMeasurable := by
  let : DiscreteMeasurableSpace S.Ω := inferInstanceAs
    (DiscreteMeasurableSpace {ω : AbsoluteValue.Place ℚ // ω ≠ AbsoluteValue.trivialPlace ℚ})
  exact (family p a).dual.isMeasurable_of_discrete

theorem family_norm_infinite (p : Nat.Primes) (a : ℤ) (ω : S.Ω) (hω : ω ∈ S.Ωinf)
    (z : (S.ϕ ω).Completion ⊗[ℚ] Plane) :
    (family p a).norm ω z =
      Real.sqrt (∑ i : Fin 2, ‖completedCoordinates ω z i‖ ^ 2) := by
  have hne : ω ≠ primePoint p := fun h => hω (h ▸ primePoint_mem_fin p)
  rw [family_norm_off_prime p a ω hne, ofBasisHermitian_norm_of_infinite standardBasis ω hω]
  rfl

theorem family_isHermitian (p : Nat.Primes) (a : ℤ) :
    (family p a).IsHermitian (normalizedNumberFieldArchimedeanCompletions (K := ℚ)) := by
  refine ⟨family_isUltrametric p a, fun ω hω => ?_⟩
  obtain ⟨c, hc⟩ := (ofBasisHermitian_isHermitian standardBasis
    (normalizedNumberFieldArchimedeanCompletions (K := ℚ))).2 ω hω
  refine ⟨c, fun z => ?_⟩
  rw [family_norm_off_prime p a ω (fun h => hω (h ▸ primePoint_mem_fin p))]
  exact hc z

/-- The actual bundle carries both measurable norms and proved domination. -/
def bundle (p : Nat.Primes) (a : ℤ) : AdelicVectorBundle S Plane where
  toNormFamily := family p a
  isMeasurable := family_isMeasurable p a
  dual_isMeasurable := family_dual_isMeasurable p a
  isDominated := (family_coherent_and_dominated p a).2

theorem exceptionalSeminorm_rational (p : Nat.Primes) (a : ℤ) (ω : S.Ω) (x : Plane) :
    exceptionalSeminorm p a ω (1 ⊗ₜ[ℚ] x) =
      max (S.ϕ ω (x 0)) (Real.sqrt (p : ℝ) * S.ϕ ω (x 1 - (a : ℚ) * x 0)) := by
  have hc (i : Fin 2) : completedCoordinates ω (1 ⊗ₜ[ℚ] x) i =
      algebraMap ℚ (S.ϕ ω).Completion (x i) := by
    simp only [completedCoordinates, basis_equivFun_one_tmul, standardBasis]
    rfl
  rw [exceptionalSeminorm_apply, hc 0, hc 1, ← map_mul, ← map_sub,
    S.norm_algebraMap_eq_absValue, S.norm_algebraMap_eq_absValue]

theorem family_norm_prime_rational (p : Nat.Primes) (a : ℤ) (x : Plane) :
    (family p a).norm (primePoint p) (1 ⊗ₜ[ℚ] x) =
      max (S.ϕ (primePoint p) (x 0))
        (Real.sqrt (p : ℝ) * S.ϕ (primePoint p) (x 1 - (a : ℚ) * x 0)) := by
  rw [family_norm_prime, exceptionalSeminorm_rational]

end ArakelovGeometry.NonpureNumberFieldMinkowskiObstruction
