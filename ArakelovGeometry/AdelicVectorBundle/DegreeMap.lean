/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.Degree
import ArakelovGeometry.AdelicVectorBundle.DeterminantMap
import ArakelovGeometry.AdelicVectorBundle.LineMapHeight

/-!
# Degree comparison through determinant maps

Proposition4.3.18 follows from the actual completed determinant operator bound
and the height identity for maps of adelic lines. The comparison retains the
lower integral and its possible value `⊤`. Rank zero uses the scalar determinant
and the explicit convention `0 * ⊥ = 0` in `EReal`.
-/

open MeasureTheory Filter

namespace ArakelovGeometry

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- Injectivity passes to the canonical equal-rank determinant map. -/
theorem determinantMap_injective (f : E →ₗ[K] F)
    (hr : Module.finrank K E = Module.finrank K F) (hf : Function.Injective f) :
    Function.Injective (determinantMap K f hr) :=
  (exteriorPowerDegreeEquiv K F hr).injective.comp
    (_root_.exteriorPower.map_injective_field hf)

omit [FiniteDimensional K F] in
/-- The determinant of an injective equal-rank map is nonzero, including rank zero. -/
theorem determinantMap_ne_zero_of_injective (f : E →ₗ[K] F)
    (hr : Module.finrank K E = Module.finrank K F) (hf : Function.Injective f) :
    determinantMap K f hr ≠ 0 := by
  let : Nontrivial (⋀[K]^(Module.finrank K E) E) :=
    Module.nontrivial_of_finrank_pos (by rw [NormFamily.determinant_finrank]; decide)
  exact LinearMap.ne_zero_of_injective (determinantMap_injective f hr hf)

namespace NormFamily

/-- Taking logarithms of the proved completed determinant operator estimate. -/
theorem determinantMap_localHeight_le (ξ : NormFamily S E) (η : NormFamily S F)
    (f : E →ₗ[K] F) (hr : Module.finrank K E = Module.finrank K F)
    (hf : f ≠ 0) (hd : determinantMap K f hr ≠ 0) (ω : S.Ω) :
    ξ.determinant.localHeight η.determinant ⟨determinantMap K f hr, hd⟩ ω ≤
      (Module.finrank K E : ℝ) * ξ.localHeight η ⟨f, hf⟩ ω := by
  have h := Real.log_le_log (ξ.determinant.operatorNorm_pos η.determinant ω hd)
    (ξ.determinantMap_operatorNorm_le_pow η ω f hr)
  rw [Real.log_pow] at h
  exact h

end NormFamily

namespace AdelicVectorBundle

variable [S.IsProper]

/-- Determinant-map height is exactly source degree minus target degree.
The sign is the one in source(4.31), correcting its final proof line(4.33). -/
theorem determinantMap_mapHeight_eq_degree_sub
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (e : E ≃ₗ[K] F) :
    (V.determinantOfMeasurableBase hS hN).mapHeight
        (W.determinantOfMeasurableBase hS hN) (determinantMap K e.toLinearMap e.finrank_eq) =
      ((V.degree hS hN - W.degree hS hN : ℝ) : EReal) :=
  (V.determinantOfMeasurableBase hS hN).mapHeight_eq_lineDegree_sub
    (W.determinantOfMeasurableBase hS hN)
    (V.determinantOfMeasurableBase_isLine hS hN)
    (W.determinantOfMeasurableBase_isLine hS hN)
    (determinantMap_ne_zero_of_injective e.toLinearMap e.finrank_eq e.injective)

/-- In rank zero the actual determinant is a unit-line map of height zero. -/
theorem determinantMap_mapHeight_eq_zero_of_finrank_eq_zero
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (e : E ≃ₗ[K] F) (hz : Module.finrank K E = 0) :
    (V.determinantOfMeasurableBase hS hN).mapHeight
        (W.determinantOfMeasurableBase hS hN)
        (determinantMap K e.toLinearMap e.finrank_eq) = 0 := by
  rw [V.determinantMap_mapHeight_eq_degree_sub W hS hN e,
    V.degree_eq_zero_of_finrank_eq_zero hS hN hz,
    W.degree_eq_zero_of_finrank_eq_zero hS hN (e.finrank_eq.symm.trans hz)]
  simp only [sub_self, EReal.coe_zero]

/-- The full degree-map inequality uses the actual lower-integral height,
including a possibly infinite height and the rank-zero determinant convention. -/
theorem degree_le_degree_add_rank_mul_mapHeight
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (e : E ≃ₗ[K] F) :
    (V.degree hS hN : EReal) ≤ (W.degree hS hN : EReal) +
      (Module.finrank K E : EReal) * V.mapHeight W e.toLinearMap := by
  by_cases hz : Module.finrank K E = 0
  · have hzF : Module.finrank K F = 0 := e.finrank_eq.symm.trans hz
    rw [V.degree_eq_zero_of_finrank_eq_zero hS hN hz,
      W.degree_eq_zero_of_finrank_eq_zero hS hN hzF, hz]
    simp only [Nat.cast_zero, EReal.coe_zero, zero_mul, add_zero, le_refl]
  · have hp : 0 < Module.finrank K E := Nat.pos_of_ne_zero hz
    let : Nontrivial E := Module.nontrivial_of_finrank_pos hp
    have hf : e.toLinearMap ≠ 0 := LinearMap.ne_zero_of_injective e.injective
    have hd := determinantMap_ne_zero_of_injective e.toLinearMap e.finrank_eq e.injective
    have hl := lowerEnvelopeIntegral_mono (μ := S.v) (Eventually.of_forall
      (V.toNormFamily.determinantMap_localHeight_le W.toNormFamily
        e.toLinearMap e.finrank_eq hf hd))
    rw [lowerEnvelopeIntegral_const_mul _ (Nat.cast_pos.mpr hp)] at hl
    change lowerEnvelopeIntegral
      ((V.determinantOfMeasurableBase hS hN).toNormFamily.localHeight
        (W.determinantOfMeasurableBase hS hN).toNormFamily
          ⟨determinantMap K e.toLinearMap e.finrank_eq, hd⟩) S.v ≤ _ at hl
    rw [← (V.determinantOfMeasurableBase hS hN).mapHeight_eq_lowerEnvelopeIntegral
        (W.determinantOfMeasurableBase hS hN) hd,
      ← V.mapHeight_eq_lowerEnvelopeIntegral W hf,
      V.determinantMap_mapHeight_eq_degree_sub W hS hN e, EReal.coe_sub] at hl
    have ht := (EReal.sub_le_iff_le_add
      (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).mp hl
    simpa only [EReal.coe_natCast, add_comm] using ht

end AdelicVectorBundle

end ArakelovGeometry
