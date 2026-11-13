/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Bidual
public import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Basic
public import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.Basic

import ArakelovGeometry.AdelicVectorBundle.Degree.ExactSequence.Basic
import ArakelovGeometry.AdelicVectorBundle.Degree.ExactSequence.Dual
import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.Isometry
import ArakelovGeometry.AdelicVectorBundle.Determinant.Bidual
import ArakelovGeometry.AdelicVectorBundle.Dual.Bidual
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Riemann--Roch for actual positive degree

Testing every actual rational subspace and its quotient-dual annihilator gives
the first positive-degree dual inequality. Actual triple-dual norms and bidual
determinant degree then give both source error bounds. Positive degrees are
proved finite before subtraction is reduced to real arithmetic; no maximizing
subspace or numerical Riemann--Roch hypothesis is used.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Every actual subspace and its actual quotient-dual annihilator give
the positive-degree upper bound. No original ultrametricity is assumed. -/
theorem positiveDegree_le_degree_add_positiveDegree_dual (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    V.positiveDegree ≤ (V.degree : EReal) +
      (V.dualOfMeasurableBase).positiveDegree := by
  obtain ⟨c, hc⟩ := (V.dualOfMeasurableBase).exists_positiveDegree_eq_coe
  apply V.positiveDegree_le
  intro U
  have hQ := (V.dualOfMeasurableBase).degree_restrict_le_positiveDegree
    U.dualAnnihilator
  rw [← V.degree_dual_quotient_eq_degree_restrict_annihilator U, hc] at hQ
  have hQr := EReal.coe_le_coe_iff.mp hQ
  have hδ := (V.quotientOfMeasurableBase U).determinantDiscrepancy_nonneg
  rw [(V.quotientOfMeasurableBase U).determinantDiscrepancy_eq_degree_add_degree_dual
] at hδ
  have hdeg := V.degree_restrict_add_degree_quotient_le U
  rw [hc, ← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  linarith

/-- Subtraction by the proved finite dual positive degree gives the first
source Riemann--Roch comparison, including rank zero. -/
theorem positiveDegree_sub_dual_le_degree (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    V.positiveDegree - (V.dualOfMeasurableBase).positiveDegree ≤
      (V.degree : EReal) := by
  apply (EReal.sub_le_iff_le_add (Or.inr (EReal.coe_ne_top _))
    (Or.inr (EReal.coe_ne_bot _))).mpr
  exact V.positiveDegree_le_degree_add_positiveDegree_dual

omit [S.IsProper] in
/-- The dual of the actual bidual bundle is exactly the original actual
dual bundle, by the all-completed-vector triple-dual norm identity. -/
theorem dual_bidualOfMeasurableBase (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase] :
    (V.bidualOfMeasurableBase).dualOfMeasurableBase =
      V.dualOfMeasurableBase := by
  apply AdelicVectorBundle.ext
    (hξ := V.bidualOfMeasurableBase.dualOfMeasurableBase.toIsAdelic)
    (hη := V.dualOfMeasurableBase.toIsAdelic)
  exact V.toNormFamily.dual_dual_pullback_dual_eq

/-- The actual bidual on the original rational space and the actual
double dual have equal positive degree under canonical evaluation. -/
theorem positiveDegree_bidual_eq_doubleDual (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (V.bidualOfMeasurableBase).positiveDegree =
      ((V.dualOfMeasurableBase).dualOfMeasurableBase).positiveDegree := by
  apply positiveDegree_eq_of_completed_isometry _ _ (Module.evalEquiv K V)
  intro ω z
  rfl

/-- Original ultrametricity outside infinity and usual Archimedean duality
identify the actual original bundle with its bidual on every fibre. -/
theorem positiveDegree_bidual_eq_of_isUltrametric (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsUltrametric] :
    (V.bidualOfMeasurableBase).positiveDegree = V.positiveDegree := by
  have he : V.bidualOfMeasurableBase = V := by
    apply AdelicVectorBundle.ext
      (hξ := V.bidualOfMeasurableBase.toIsAdelic) (hη := V.toIsAdelic)
    simpa only [bidualOfMeasurableBase_toNormFamily] using
      V.toNormFamily.dual_dual_pullback_eq
  rw [he]

/-- Source (4.39) for every actual adelic bundle, retaining the actual
bidual positive degree when original finite-place norms are not ultrametric. -/
theorem riemannRoch_inequality (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    0 ≤ (V.degree : EReal) -
      ((V.bidualOfMeasurableBase).positiveDegree -
        (V.dualOfMeasurableBase).positiveDegree) ∧
      (V.degree : EReal) -
        ((V.bidualOfMeasurableBase).positiveDegree -
          (V.dualOfMeasurableBase).positiveDegree) ≤
        (V.determinantDiscrepancy : EReal) := by
  obtain ⟨a, ha⟩ := (V.bidualOfMeasurableBase).exists_positiveDegree_eq_coe
  obtain ⟨b, hb⟩ := (V.dualOfMeasurableBase).exists_positiveDegree_eq_coe
  have hl := (V.bidualOfMeasurableBase).positiveDegree_sub_dual_le_degree
  rw [V.dual_bidualOfMeasurableBase, V.degree_bidualOfMeasurableBase,
    ha, hb, ← EReal.coe_sub] at hl
  have hlr := EReal.coe_le_coe_iff.mp hl
  have hu := (V.dualOfMeasurableBase).positiveDegree_sub_dual_le_degree
  rw [← V.positiveDegree_bidual_eq_doubleDual, ha, hb, ← EReal.coe_sub] at hu
  have hur := EReal.coe_le_coe_iff.mp hu
  have hδ := V.determinantDiscrepancy_eq_degree_add_degree_dual
  rw [ha, hb, ← EReal.coe_sub, ← EReal.coe_sub]
  constructor
  · exact_mod_cast (show 0 ≤ V.degree - (a - b) by linarith)
  · exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- Source (4.40) with the original bundle positive degree, under precisely
the original outside-infinity ultrametricity assumption. -/
theorem riemannRoch_inequality_of_isUltrametric (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsUltrametric] :
    0 ≤ (V.degree : EReal) -
      (V.positiveDegree - (V.dualOfMeasurableBase).positiveDegree) ∧
      (V.degree : EReal) -
        (V.positiveDegree - (V.dualOfMeasurableBase).positiveDegree) ≤
        (V.determinantDiscrepancy : EReal) := by
  simpa only [V.positiveDegree_bidual_eq_of_isUltrametric] using
    V.riemannRoch_inequality

/-- For actual Hermitian bundles the Riemann--Roch discrepancy vanishes,
so the original degree is the difference of the two actual positive degrees. -/
theorem degree_eq_positiveDegree_sub_dual_of_isHermitian (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] :
    (V.degree : EReal) = V.positiveDegree -
      (V.dualOfMeasurableBase).positiveDegree := by
  obtain ⟨a, ha⟩ := V.exists_positiveDegree_eq_coe
  obtain ⟨b, hb⟩ := (V.dualOfMeasurableBase).exists_positiveDegree_eq_coe
  have h := V.riemannRoch_inequality_of_isUltrametric (hV := hV.1)
  rw [V.determinantDiscrepancy_eq_zero_of_isHermitian, EReal.coe_zero,
    ha, hb, ← EReal.coe_sub, ← EReal.coe_sub] at h
  have hz : (V.degree - (a - b) : EReal) = 0 := le_antisymm h.2 h.1
  have hzr : V.degree - (a - b) = 0 := by exact_mod_cast hz
  rw [ha, hb, ← EReal.coe_sub]
  apply congrArg (fun r : ℝ ↦ (r : EReal))
  linarith

end

end ArakelovGeometry.AdelicVectorBundle
