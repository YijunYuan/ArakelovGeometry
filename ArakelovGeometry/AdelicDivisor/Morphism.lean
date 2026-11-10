/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Morphism.Basic
public import ArakelovGeometry.AdelicDivisor.Principal
import Mathlib.Combinatorics.Matroid.Init

/-!
# Divisors under morphisms of adelic curves

The maps are the canonical `L¹` pullback and fibre integral already supplied
by a Chapter 3 morphism. Degree preservation, effectivity of pullback and
compatibility with actual principal logarithms follow from its defining laws.
-/

@[expose] public section

open MeasureTheory Filter

namespace ArakelovGeometry.AdelicDivisor

universe u v u' v'

variable {K : Type u} [Field K] {L : Type u'} [Field L]
  {C : AdelicStructure.{u, v} K} {D : AdelicStructure.{u', v'} L}
  (α : AdelicStructure.Hom C D)

/-- Pullback of divisors is the canonical `L¹` linear isometry. -/
noncomputable abbrev pullback : AdelicDivisor D →ₗᵢ[ℝ] AdelicDivisor C := α.pullback

/-- Pushforward of divisors is the actual real-linear fibre integral supplied
by the adelic morphism. No continuity or positivity is added. -/
abbrev pushforward : AdelicDivisor C →ₗ[ℝ] AdelicDivisor D := α.fibreIntegral

/-- Pullback is represented by composition with the map of parameter spaces. -/
theorem coeFn_pullback (ζ : AdelicDivisor D) :
    pullback α ζ =ᵐ[C.v] ζ ∘ α.baseMap := α.coeFn_pullback ζ

/-- Pullback is an isometry for the actual `L¹` divisor norm. -/
theorem isometry_pullback : Isometry (pullback α) := (pullback α).isometry

/-- Pullback preserves the divisor norm. -/
@[simp]
theorem norm_pullback (ζ : AdelicDivisor D) : ‖pullback α ζ‖ = ‖ζ‖ :=
  (pullback α).norm_map ζ

/-- The disintegration identity retracts pullback on divisor classes. -/
@[simp]
theorem pushforward_pullback (ζ : AdelicDivisor D) : pushforward α (pullback α ζ) = ζ :=
  α.fibreIntegral_pullback_apply ζ

/-- Degree is preserved under pullback, by the measure-preserving integral identity. -/
@[simp]
theorem degree_pullback (ζ : AdelicDivisor D) : degree C (pullback α ζ) = degree D ζ := by
  rw [degree_eq_integral, degree_eq_integral]
  exact (integral_congr_ae (coeFn_pullback α ζ)).trans
    (α.integral_comp (L1.integrable_coeFn ζ))

/-- Degree is preserved under the actual fibre-integral pushforward. -/
@[simp]
theorem degree_pushforward (ζ : AdelicDivisor C) : degree D (pushforward α ζ) = degree C ζ := by
  rw [degree_eq_integral, degree_eq_integral]
  exact α.integral_fibreIntegral ζ

/-- Pullback carries effective divisors to effective divisors. -/
theorem IsEffective.pullback {ζ : AdelicDivisor D} (hζ : IsEffective D ζ) :
    IsEffective C (pullback α ζ) := by
  filter_upwards [coeFn_pullback α ζ, α.measurePreserving.quasiMeasurePreserving.ae hζ]
    with ω heq hω
  rwa [heq]

/-- Pullback is independent of the chosen integrable representative and is
the class of its composition with the parameter map. -/
theorem pullback_ofIntegrable (f : D.Ω → ℝ) (hf : Integrable f D.v) :
    pullback α (ofIntegrable D f hf) =
      ofIntegrable C (f ∘ α.baseMap) (α.integrable_comp hf) := by
  apply Lp.ext
  exact (coeFn_pullback α _).trans
    ((α.measurePreserving.quasiMeasurePreserving.ae_eq_comp hf.coeFn_toL1).trans
      (α.integrable_comp hf).coeFn_toL1.symm)

/-- Compatibility of absolute values transports the actual logarithmic
divisor of a field unit through the contravariant field map. -/
@[simp]
theorem pullback_principal (a : Lˣ) :
    pullback α (principal D a) = principal C (Units.map α.fieldMap.toMonoidHom a) := by
  apply Lp.ext
  filter_upwards [coeFn_pullback α (principal D a),
    α.measurePreserving.quasiMeasurePreserving.ae (coeFn_principal D a),
    coeFn_principal C (Units.map α.fieldMap.toMonoidHom a)] with ω hp hD hC
  rw [hp, hC]
  change principal D a (α.baseMap ω) =
    -Real.log (C.ϕ ω (α.fieldMap (a : L)))
  rw [hD, α.absoluteValue_comp]

end ArakelovGeometry.AdelicDivisor
