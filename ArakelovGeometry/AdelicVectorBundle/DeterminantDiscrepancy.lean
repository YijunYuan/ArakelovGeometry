/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.DegreeDual

/-!
# Determinant discrepancy and the defect in degree duality

The discrepancy uses the actual completed determinant and dual determinant
norms. Independence of a paired determinant generator gives its intrinsic
interpretation, while rational generators yield measurability and integrability.
-/

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- A fixed nonzero rational generator of the determinant line. -/
def determinantGenerator : ⋀[K]^(Module.finrank K E) E :=
  Module.finBasisOfFinrankEq K _ NormFamily.determinant_finrank 0

/-- Its canonically paired generator of the determinant of the dual. -/
def dualDeterminantGenerator :
    ⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E) :=
  (determinantDualEquiv K E).symm
    ((Module.finBasisOfFinrankEq K _ NormFamily.determinant_finrank).coord 0)

theorem determinantGenerator_ne_zero : determinantGenerator (K := K) (E := E) ≠ 0 :=
  (Module.finBasisOfFinrankEq K _ NormFamily.determinant_finrank).ne_zero 0

theorem determinantGenerator_pairing :
    determinantDualEquiv K E (dualDeterminantGenerator (K := K) (E := E))
      (determinantGenerator (K := K) (E := E)) = 1 := by
  simp [determinantGenerator, dualDeterminantGenerator, Module.Basis.coord_apply]

theorem dualDeterminantGenerator_ne_zero :
    dualDeterminantGenerator (K := K) (E := E) ≠ 0 := by
  intro h
  have hp := determinantGenerator_pairing (K := K) (E := E)
  rw [h, map_zero, LinearMap.zero_apply] at hp
  exact zero_ne_one hp

theorem completedDeterminantGenerator_pairing (ω : S.Ω) :
    completedDeterminantPairing K (S.ϕ ω).Completion E
      (1 ⊗ₜ[K] dualDeterminantGenerator (K := K) (E := E))
      (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E)) = 1 := by
  simp [completedDeterminantPairing, determinantGenerator_pairing,
    LinearMap.baseChange_tmul]

namespace NormFamily

variable (ξ : NormFamily S E)

/-- The intrinsic determinant discrepancy, expressed through one rational
pair of dual determinant generators. -/
def determinantDiscrepancy (ω : S.Ω) : ℝ :=
  (ξ.determinant.norm ω (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E)) *
    ξ.dual.determinant.norm ω (1 ⊗ₜ[K] dualDeterminantGenerator (K := K) (E := E)))⁻¹

theorem determinantDiscrepancy_pos (ω : S.Ω) : 0 < ξ.determinantDiscrepancy ω :=
  inv_pos.mpr (mul_pos
    (ξ.determinant.norm_rational_pos ω determinantGenerator_ne_zero)
    (ξ.dual.determinant.norm_rational_pos ω dualDeterminantGenerator_ne_zero))

/-- The source lower bound follows from the general completed pairing inequality. -/
theorem one_le_determinantDiscrepancy (ω : S.Ω) : 1 ≤ ξ.determinantDiscrepancy ω := by
  have h := ξ.determinant_norm_mul_dual_le_norm_pairing ω
    (1 ⊗ₜ[K] dualDeterminantGenerator (K := K) (E := E))
    (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E))
  rw [completedDeterminantGenerator_pairing, norm_one] at h
  exact (one_le_inv₀ (mul_pos
    (ξ.determinant.norm_rational_pos ω determinantGenerator_ne_zero)
    (ξ.dual.determinant.norm_rational_pos ω dualDeterminantGenerator_ne_zero))).2 h

theorem log_determinantDiscrepancy_nonneg (ω : S.Ω) :
    0 ≤ Real.log (ξ.determinantDiscrepancy ω) :=
  Real.log_nonneg (ξ.one_le_determinantDiscrepancy ω)

/-- The logarithmic discrepancy is the sum of two genuine rational
logarithmic determinant norms with opposite signs. -/
theorem log_determinantDiscrepancy (ω : S.Ω) :
    Real.log (ξ.determinantDiscrepancy ω) =
      -ξ.determinant.logNorm (determinantGenerator (K := K) (E := E)) ω -
        ξ.dual.determinant.logNorm (dualDeterminantGenerator (K := K) (E := E)) ω := by
  rw [determinantDiscrepancy, Real.log_inv, Real.log_mul
    (ξ.determinant.norm_rational_pos ω determinantGenerator_ne_zero).ne'
    (ξ.dual.determinant.norm_rational_pos ω dualDeterminantGenerator_ne_zero).ne']
  dsimp only [logNorm]
  ring

/-- Any completed determinant pair with pairing one computes the same
intrinsic discrepancy; the choice of rational generators is irrelevant. -/
theorem determinantDiscrepancy_eq_inv_norm_mul (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E)))
    (w : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E))
    (hp : completedDeterminantPairing K (S.ϕ ω).Completion E z w = 1) :
    ξ.determinantDiscrepancy ω =
      (ξ.determinant.norm ω w * ξ.dual.determinant.norm ω z)⁻¹ := by
  let w₀ := (1 : (S.ϕ ω).Completion) ⊗ₜ[K] determinantGenerator (K := K) (E := E)
  let z₀ := (1 : (S.ϕ ω).Completion) ⊗ₜ[K] dualDeterminantGenerator (K := K) (E := E)
  have hw₀ : w₀ ≠ 0 := by
    intro hw
    have hp₀ := completedDeterminantGenerator_pairing (S := S) (E := E) ω
    change completedDeterminantPairing K (S.ϕ ω).Completion E z₀ w₀ = 1 at hp₀
    rw [hw, map_zero] at hp₀
    exact zero_ne_one hp₀
  have hz₀ : z₀ ≠ 0 := by
    intro hz
    have hp₀ := completedDeterminantGenerator_pairing (S := S) (E := E) ω
    change completedDeterminantPairing K (S.ϕ ω).Completion E z₀ w₀ = 1 at hp₀
    rw [hz, map_zero, LinearMap.zero_apply] at hp₀
    exact zero_ne_one hp₀
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one
    (show Module.finrank (S.ϕ ω).Completion
        ((S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) = 1 by
      rw [Module.finrank_baseChange]; exact determinant_finrank) hw₀ w
  obtain ⟨b, hb⟩ := exists_smul_eq_of_finrank_eq_one
    (show Module.finrank (S.ϕ ω).Completion
        ((S.ϕ ω).Completion ⊗[K]
          (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E))) = 1 by
      rw [Module.finrank_baseChange]; exact determinant_finrank) hz₀ z
  have hab : a * b = 1 := by
    rw [← ha, ← hb] at hp
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, w₀, z₀,
      completedDeterminantGenerator_pairing, mul_one] using hp
  have hn : ‖a‖ * ‖b‖ = 1 := by
    simpa only [norm_mul, norm_one, mul_comm] using congrArg (fun t : (S.ϕ ω).Completion ↦ ‖t‖) hab
  have he : ξ.determinant.norm ω w * ξ.dual.determinant.norm ω z =
      ξ.determinant.norm ω w₀ * ξ.dual.determinant.norm ω z₀ := by
    rw [← ha, ← hb, ξ.determinant.norm_smul, ξ.dual.determinant.norm_smul]
    calc
      (‖a‖ * ξ.determinant.norm ω w₀) * (‖b‖ * ξ.dual.determinant.norm ω z₀) =
          (‖a‖ * ‖b‖) * (ξ.determinant.norm ω w₀ * ξ.dual.determinant.norm ω z₀) := by ring
      _ = _ := by rw [hn, one_mul]
  rw [he]
  rfl

/-- Measurability is derived from the two actual rational determinant norm
functions, rather than assumed for the discrepancy itself. -/
theorem measurable_determinantDiscrepancy
    (hm : ξ.determinant.IsMeasurable) (hd : ξ.dual.determinant.IsMeasurable) :
    Measurable ξ.determinantDiscrepancy :=
  ((hm determinantGenerator).mul (hd dualDeterminantGenerator)).inv

variable {hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}

/-- Hermitian determinant duality makes the discrepancy identically one. -/
theorem IsHermitian.determinantDiscrepancy_eq_one (hξ : ξ.IsHermitian hS) (ω : S.Ω) :
    ξ.determinantDiscrepancy ω = 1 := by
  have h := hξ.norm_completedDeterminantPairing_eq ξ ω
    (1 ⊗ₜ[K] dualDeterminantGenerator (K := K) (E := E))
    (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E))
  rw [completedDeterminantGenerator_pairing, norm_one] at h
  rw [determinantDiscrepancy, ← h, inv_one]

/-- Rank zero has the scalar unit determinant line and discrepancy one. -/
theorem determinantDiscrepancy_eq_one_of_finrank_eq_zero
    (hr : Module.finrank K E = 0) (ω : S.Ω) : ξ.determinantDiscrepancy ω = 1 := by
  have h := ξ.norm_completedDeterminantPairing_of_finrank_eq_zero hr ω
    (1 ⊗ₜ[K] dualDeterminantGenerator (K := K) (E := E))
    (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E))
  rw [completedDeterminantGenerator_pairing, norm_one] at h
  rw [determinantDiscrepancy, ← h, inv_one]

end NormFamily

namespace AdelicVectorBundle

/-- The discrepancy of an adelic bundle is measurable under exactly the
source's standing measurability alternative. -/
theorem measurable_determinantDiscrepancy (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    Measurable V.toNormFamily.determinantDiscrepancy :=
  V.toNormFamily.measurable_determinantDiscrepancy
    (V.isMeasurable.determinant_of_discrete_or_countable hS)
    ((V.dualOfMeasurableBase hS).isMeasurable.determinant_of_discrete_or_countable hS)

/-- Both genuine determinant lines are adelic, so their logarithmic
norms supply integrability of the logarithmic discrepancy. -/
theorem integrable_log_determinantDiscrepancy (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    Integrable (fun ω ↦ Real.log (V.toNormFamily.determinantDiscrepancy ω)) S.v := by
  have hm := (V.determinantOfMeasurableBase hS hN).integrable_logNorm
    (determinantGenerator (K := K) (E := E))
  have hd := ((V.dualOfMeasurableBase hS).determinantOfMeasurableBase hS hN).integrable_logNorm
    (dualDeterminantGenerator (K := K) (E := E))
  change Integrable (V.toNormFamily.determinant.logNorm determinantGenerator) S.v at hm
  change Integrable (V.toNormFamily.dual.determinant.logNorm dualDeterminantGenerator) S.v at hd
  exact (hm.neg.sub hd).congr (Filter.Eventually.of_forall fun ω ↦
    (V.toNormFamily.log_determinantDiscrepancy ω).symm)

/-- The degree-duality defect is the integral of the intrinsic local
determinant discrepancy, in every rank. -/
theorem degree_add_degree_dual_eq_integral_log_determinantDiscrepancy [S.IsProper]
    (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.degree hS hN + (V.dualOfMeasurableBase hS).degree hS hN =
      ∫ ω, Real.log (V.toNormFamily.determinantDiscrepancy ω) ∂S.v := by
  let f := V.toNormFamily.determinant.logNorm (determinantGenerator (K := K) (E := E))
  let g := V.toNormFamily.dual.determinant.logNorm
    (dualDeterminantGenerator (K := K) (E := E))
  have hm : Integrable f S.v := (V.determinantOfMeasurableBase hS hN).integrable_logNorm _
  have hd : Integrable g S.v :=
    ((V.dualOfMeasurableBase hS).determinantOfMeasurableBase hS hN).integrable_logNorm _
  rw [V.degree_eq_neg_integral hS hN ⟨_, determinantGenerator_ne_zero⟩,
    (V.dualOfMeasurableBase hS).degree_eq_neg_integral hS hN
      ⟨_, dualDeterminantGenerator_ne_zero⟩]
  change -(∫ ω, f ω ∂S.v) + -(∫ ω, g ω ∂S.v) = _
  have hm' : Integrable (fun ω ↦ -f ω) S.v := hm.neg
  have he : (∫ ω, Real.log (V.toNormFamily.determinantDiscrepancy ω) ∂S.v) =
      ∫ ω, -f ω - g ω ∂S.v :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω ↦
      V.toNormFamily.log_determinantDiscrepancy ω)
  rw [integral_sub hm' hd, integral_neg] at he
  rw [he]
  ring

/-- Degree plus dual degree is nonnegative, with no Hermitian hypothesis. -/
theorem degree_add_degree_dual_nonneg [S.IsProper] (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    0 ≤ V.degree hS hN + (V.dualOfMeasurableBase hS).degree hS hN := by
  rw [V.degree_add_degree_dual_eq_integral_log_determinantDiscrepancy hS hN]
  exact integral_nonneg (fun ω ↦ V.toNormFamily.log_determinantDiscrepancy_nonneg ω)

end AdelicVectorBundle


end

end ArakelovGeometry
