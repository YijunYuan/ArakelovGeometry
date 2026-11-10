/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Measurable norm families

Measurability tests the norms of fixed rational vectors in the actual
completed fibres (Chen–Moriwaki, §4.1.3, PDF page 239). It is distinct
from domination; together the two conditions give integrable logarithmic
norms, as needed for adelic degrees.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E]
  {F : Type w'} [AddCommGroup F] [Module K F]

/-- Every fixed rational vector has a measurable norm evaluation. -/
def IsMeasurable (ξ : NormFamily S E) : Prop :=
  ∀ x : E, Measurable (fun ω ↦ ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x))

/-- Measurable norm evaluations have measurable logarithms, including at zero. -/
theorem IsMeasurable.logNorm {ξ : NormFamily S E} (hξ : ξ.IsMeasurable) (x : E) :
    Measurable (ξ.logNorm x) := (hξ x).log

/-- It suffices to test logarithmic norms on nonzero rational vectors. -/
theorem isMeasurable_iff_logNorm (ξ : NormFamily S E) :
    ξ.IsMeasurable ↔ ∀ x : E, x ≠ 0 → Measurable (ξ.logNorm x) := by
  refine ⟨fun h x _ ↦ h.logNorm x, ?_⟩
  intro h x
  by_cases hx : x = 0
  · simp only [hx, TensorProduct.tmul_zero, norm_zero]
    exact measurable_const
  · convert (h x hx).exp using 1
    ext ω
    exact (Real.exp_log (ξ.norm_rational_pos ω hx)).symm

/-- A norm family on the zero space is measurable. -/
theorem isMeasurable_of_subsingleton [Subsingleton E] (ξ : NormFamily S E) :
    ξ.IsMeasurable := by
  intro x
  simp only [ξ.norm_eq_zero_of_subsingleton]
  exact measurable_const

/-- On a discrete measurable parameter space every norm family is measurable. -/
theorem isMeasurable_of_discrete [DiscreteMeasurableSpace S.Ω] (ξ : NormFamily S E) :
    ξ.IsMeasurable := fun _ ↦ Measurable.of_discrete

/-- Pullback along an injective rational map preserves measurability. -/
theorem IsMeasurable.pullback {ξ : NormFamily S E} (hξ : ξ.IsMeasurable)
    (f : F →ₗ[K] E) (hf : Function.Injective f) : (ξ.pullback f hf).IsMeasurable := by
  intro x
  exact hξ (f x)

/-- Subspace restriction preserves measurability without countability assumptions. -/
theorem IsMeasurable.restrict {ξ : NormFamily S E} (hξ : ξ.IsMeasurable)
    (F : Submodule K E) : (ξ.restrict F).IsMeasurable :=
  hξ.pullback F.subtype F.subtype_injective

/-- A rational linear equivalence preserves and reflects measurability. -/
theorem isMeasurable_pullback_iff (ξ : NormFamily S E) (e : F ≃ₗ[K] E) :
    (ξ.pullback e.toLinearMap e.injective).IsMeasurable ↔ ξ.IsMeasurable := by
  refine ⟨?_, fun h ↦ h.pullback e.toLinearMap e.injective⟩
  intro h x
  obtain ⟨y, rfl⟩ := e.surjective x
  exact h y

/-- Positive measurable rescaling preserves measurable norm families. -/
theorem IsMeasurable.scale {ξ : NormFamily S E} (hξ : ξ.IsMeasurable)
    (f : S.Ω → ℝ) (hf : ∀ ω, 0 < f ω) (hm : Measurable f) :
    (ξ.scale f hf).IsMeasurable := by
  intro x
  exact hm.mul (hξ x)

/-- Positive measurable rescaling also reflects measurability. -/
theorem isMeasurable_scale_iff (ξ : NormFamily S E) (f : S.Ω → ℝ)
    (hf : ∀ ω, 0 < f ω) (hm : Measurable f) :
    (ξ.scale f hf).IsMeasurable ↔ ξ.IsMeasurable := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.scale f hf hm⟩
  simpa only [scale_inv_scale] using
    h.scale (fun ω ↦ (f ω)⁻¹) (fun ω ↦ inv_pos.mpr (hf ω)) hm.inv

/-- A measurable dominated norm family has integrable rational logarithmic norms.
This is the genuine envelope-to-integral bridge used for vector degrees. -/
theorem IsDominated.integrable_logNorm [FiniteDimensional K E]
    {ξ : NormFamily S E} (hd : ξ.IsDominated) (hm : ξ.IsMeasurable) (x : E) :
    Integrable (ξ.logNorm x) S.v := by
  by_cases hx : x = 0
  · have hz : ξ.logNorm x = 0 := by
      funext ω
      simp [NormFamily.logNorm, hx]
    rw [hz]
    exact integrable_zero S.Ω ℝ S.v
  · exact (hd.logNorm_bounds hx).integrable (hm.logNorm x).aestronglyMeasurable

end ArakelovGeometry.NormFamily
