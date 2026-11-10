/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.BundleCountable
import ArakelovGeometry.AdelicVectorBundle.BundleTensor
import ArakelovGeometry.AdelicVectorBundle.CountableTensorMeasurable
import ArakelovGeometry.AdelicVectorBundle.LineDegree
import ArakelovGeometry.AdelicVectorBundle.DeterminantComparison

/-!
# Arakelov degree of an adelic vector bundle

Definition 4.3.7 is the line degree of the actual determinant norm family.
The source's discrete-base or common-countable-subfield hypothesis supplies
determinant measurability; it is not a premise on the resulting determinant.
This file proves the generator formula, rank-zero value and order comparison.
-/

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Both alternatives in the source give measurability of the actual determinant. -/
theorem NormFamily.IsMeasurable.determinant_of_discrete_or_countable
    {ξ : NormFamily S E} (hξ : ξ.IsMeasurable)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    ξ.determinant.IsMeasurable := by
  rcases hS with hS | hS
  · let := hS
    exact ξ.determinant.isMeasurable_of_discrete
  · exact hξ.determinant_of_common_countable_dense_subfield hS

namespace AdelicVectorBundle

/-- The canonical determinant adelic line with its measurability proved automatically. -/
noncomputable def determinantOfMeasurableBase (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    AdelicVectorBundle S (⋀[K]^(Module.finrank K E) E) :=
  V.determinant (V.isMeasurable.determinant_of_discrete_or_countable hS) hN

@[simp]
theorem determinantOfMeasurableBase_toNormFamily (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.determinantOfMeasurableBase hS hN).toNormFamily = V.toNormFamily.determinant := rfl

theorem determinantOfMeasurableBase_isLine (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.determinantOfMeasurableBase hS hN).IsLine := NormFamily.determinant_finrank

/-- The Arakelov degree is the degree of the actual determinant adelic line. -/
noncomputable def degree [S.IsProper] (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) : ℝ :=
  (V.determinantOfMeasurableBase hS hN).lineDegree
    (V.determinantOfMeasurableBase_isLine hS hN)

/-- Any nonzero rational determinant vector computes the same degree. -/
theorem degree_eq_neg_integral [S.IsProper] (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (s : {x : ⋀[K]^(Module.finrank K E) E // x ≠ 0}) :
    V.degree hS hN = -(∫ ω, V.toNormFamily.determinant.logNorm s.val ω ∂S.v) :=
  lineDegree_eq_neg_integral _ _ s

omit [FiniteDimensional K E] in
/-- In rank zero the empty determinant wedge has nonzero rational coordinate. -/
theorem determinant_empty_ne_zero (h : Module.finrank K E = 0) :
    _root_.exteriorPower.ιMulti K (Module.finrank K E) (fun _ ↦ (0 : E)) ≠ 0 := by
  have hz : ∀ n : ℕ, n = 0 →
      _root_.exteriorPower.ιMulti K n (fun _ ↦ (0 : E)) ≠ 0 := by
    rintro n rfl he
    have := congrArg (_root_.exteriorPower.zeroEquiv K E) he
    exact one_ne_zero (by simpa only [_root_.exteriorPower.zeroEquiv_ιMulti, map_zero] using this)
  exact hz _ h

/-- The zero bundle has degree zero; its determinant is the scalar unit line. -/
theorem degree_eq_zero_of_finrank_eq_zero [S.IsProper] (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : Module.finrank K E = 0) : V.degree hS hN = 0 := by
  apply lineDegree_eq_zero_of_norm_eq_one _ _
    ⟨_, determinant_empty_ne_zero hr⟩
  intro ω
  change V.toNormFamily.determinant.norm ω _ = 1
  simpa only [norm_one] using V.toNormFamily.determinant_norm_empty_tmul hr ω 1 (fun _ ↦ 0)

/-- Enlarging every completed norm decreases degree. -/
theorem degree_antitone [S.IsProper] (V W : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (h : V.toNormFamily ≤ W.toNormFamily) : W.degree hS hN ≤ V.degree hS hN := by
  let s := (V.determinantOfMeasurableBase hS hN).lineGenerator
    (V.determinantOfMeasurableBase_isLine hS hN)
  rw [V.degree_eq_neg_integral hS hN s, W.degree_eq_neg_integral hS hN s]
  apply neg_le_neg
  apply integral_mono_ae
    ((V.determinantOfMeasurableBase hS hN).integrable_logNorm s.val)
    ((W.determinantOfMeasurableBase hS hN).integrable_logNorm s.val)
  exact Filter.Eventually.of_forall fun ω ↦ Real.log_le_log
    (V.toNormFamily.determinant.norm_rational_pos ω s.property)
    (NormFamily.determinant_mono h ω _)

end AdelicVectorBundle

end ArakelovGeometry
