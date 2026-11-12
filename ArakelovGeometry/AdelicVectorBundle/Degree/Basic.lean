/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Tensor.Basic
public import ArakelovGeometry.AdelicVectorBundle.Degree.Line
public import ArakelovGeometry.AdelicVectorBundle.Measurability.Density.Basic

import ArakelovGeometry.AdelicVectorBundle.Determinant.Comparison
import ArakelovGeometry.AdelicVectorBundle.Measurability.Tensor
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Arakelov degree of an adelic vector bundle

Definition 4.3.7 is the line degree of the actual determinant norm family.
The source's discrete-base or common-countable-subfield hypothesis supplies
determinant measurability; it is not a premise on the resulting determinant.
This file proves the generator formula, rank-zero value and order comparison.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Both alternatives in the source give measurability of the actual determinant. -/
theorem NormFamily.IsMeasurable.determinant_of_discrete_or_countable
    {ξ : NormFamily S E} (hξ : ξ.IsMeasurable)
    [hS : S.HasMeasurableBase] :
    ξ.determinant.IsMeasurable := by
  rcases hS.discrete_or_countable with hS | hS
  · let := hS
    exact ξ.determinant.isMeasurable_of_discrete
  · exact hξ.determinant_of_common_countable_dense_subfield hS

instance NormFamily.instIsMeasurableDeterminant (ξ : NormFamily S E)
    [ξ.IsMeasurable] [S.HasMeasurableBase] : ξ.determinant.IsMeasurable :=
  NormFamily.IsMeasurable.determinant_of_discrete_or_countable inferInstance

namespace AdelicVectorBundle

/-- The canonical determinant adelic line with its measurability proved automatically. -/
noncomputable def determinantOfMeasurableBase (V : AdelicVectorBundle S E)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    AdelicVectorBundle S (⋀[K]^(Module.finrank K E) E) :=
  V.determinant

@[simp]
theorem determinantOfMeasurableBase_toNormFamily (V : AdelicVectorBundle S E)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (V.determinantOfMeasurableBase).toNormFamily = V.toNormFamily.determinant := rfl

instance determinantOfMeasurableBase_isLine (V : AdelicVectorBundle S E)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (V.determinantOfMeasurableBase).IsLine := ⟨NormFamily.determinant_finrank⟩

/-- The Arakelov degree is the degree of the actual determinant adelic line. -/
noncomputable def degree [S.IsProper] (V : AdelicVectorBundle S E)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] : ℝ :=
  (V.determinantOfMeasurableBase).lineDegree
    (hV := (V.determinantOfMeasurableBase_isLine))

/-- Any nonzero rational determinant vector computes the same degree. -/
theorem degree_eq_neg_integral [S.IsProper] (V : AdelicVectorBundle S E)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (s : {x : ⋀[K]^(Module.finrank K E) E // x ≠ 0}) :
    V.degree = -(∫ ω, V.toNormFamily.determinant.logNorm s.val ω ∂S.v) :=
  lineDegree_eq_neg_integral _ s

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
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (hr : Module.finrank K E = 0) : V.degree = 0 := by
  apply lineDegree_eq_zero_of_norm_eq_one _
    ⟨_, determinant_empty_ne_zero hr⟩
  intro ω
  change V.toNormFamily.determinant.norm ω _ = 1
  simpa only [norm_one] using V.toNormFamily.determinant_norm_empty_tmul hr ω 1 (fun _ ↦ 0)

/-- Enlarging every completed norm decreases degree. -/
theorem degree_antitone [S.IsProper] (V W : AdelicVectorBundle S E)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (h : V.toNormFamily ≤ W.toNormFamily) : W.degree ≤ V.degree := by
  let s := (V.determinantOfMeasurableBase).lineGenerator
    (hV := (V.determinantOfMeasurableBase_isLine))
  rw [V.degree_eq_neg_integral s, W.degree_eq_neg_integral s]
  apply neg_le_neg
  apply integral_mono_ae
    ((V.determinantOfMeasurableBase).integrable_logNorm s.val)
    ((W.determinantOfMeasurableBase).integrable_logNorm s.val)
  exact Filter.Eventually.of_forall fun ω ↦ Real.log_le_log
    (V.toNormFamily.determinant.norm_rational_pos ω s.property)
    (NormFamily.determinant_mono h ω _)

end AdelicVectorBundle

end ArakelovGeometry
