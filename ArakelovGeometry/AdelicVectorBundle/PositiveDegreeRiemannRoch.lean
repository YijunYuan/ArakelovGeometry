/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DegreeBidual
public import ArakelovGeometry.AdelicVectorBundle.DegreeExactSequenceDual
public import ArakelovGeometry.AdelicVectorBundle.PositiveDegreeIsometry

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
theorem positiveDegree_le_degree_add_positiveDegree_dual (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.positiveDegree hS hN ≤ (V.degree hS hN : EReal) +
      (V.dualOfMeasurableBase hS).positiveDegree hS hN := by
  obtain ⟨c, hc⟩ := (V.dualOfMeasurableBase hS).exists_positiveDegree_eq_coe hS hN
  apply V.positiveDegree_le hS hN
  intro U
  have hQ := (V.dualOfMeasurableBase hS).degree_restrict_le_positiveDegree hS hN
    U.dualAnnihilator
  rw [← V.degree_dual_quotient_eq_degree_restrict_annihilator U hS hN, hc] at hQ
  have hQr := EReal.coe_le_coe_iff.mp hQ
  have hδ := (V.quotientOfMeasurableBase U hS).determinantDiscrepancy_nonneg
  rw [(V.quotientOfMeasurableBase U hS).determinantDiscrepancy_eq_degree_add_degree_dual
    hS hN] at hδ
  have hdeg := V.degree_restrict_add_degree_quotient_le U hS hN
  rw [hc, ← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  linarith

/-- Subtraction by the proved finite dual positive degree gives the first
source Riemann--Roch comparison, including rank zero. -/
theorem positiveDegree_sub_dual_le_degree (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.positiveDegree hS hN - (V.dualOfMeasurableBase hS).positiveDegree hS hN ≤
      (V.degree hS hN : EReal) := by
  apply (EReal.sub_le_iff_le_add (Or.inr (EReal.coe_ne_top _))
    (Or.inr (EReal.coe_ne_bot _))).mpr
  exact V.positiveDegree_le_degree_add_positiveDegree_dual hS hN

omit [S.IsProper] in
/-- The dual of the actual bidual bundle is exactly the original actual
dual bundle, by the all-completed-vector triple-dual norm identity. -/
theorem dual_bidualOfMeasurableBase (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    (V.bidualOfMeasurableBase hS).dualOfMeasurableBase hS =
      V.dualOfMeasurableBase hS := by
  apply AdelicVectorBundle.ext
  simp only [dualOfMeasurableBase_toNormFamily, bidualOfMeasurableBase_toNormFamily]
  exact V.toNormFamily.dual_dual_pullback_dual_eq

/-- The actual bidual on the original rational space and the actual
double dual have equal positive degree under canonical evaluation. -/
theorem positiveDegree_bidual_eq_doubleDual (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.bidualOfMeasurableBase hS).positiveDegree hS hN =
      ((V.dualOfMeasurableBase hS).dualOfMeasurableBase hS).positiveDegree hS hN := by
  apply positiveDegree_eq_of_completed_isometry _ _ (Module.evalEquiv K E) hS hN
  intro ω z
  rfl

/-- Original ultrametricity outside infinity and usual Archimedean duality
identify the actual original bundle with its bidual on every fibre. -/
theorem positiveDegree_bidual_eq_of_isUltrametric (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsUltrametric) :
    (V.bidualOfMeasurableBase hS).positiveDegree hS hN = V.positiveDegree hS hN := by
  have he : V.bidualOfMeasurableBase hS = V := by
    apply AdelicVectorBundle.ext
    simpa only [bidualOfMeasurableBase_toNormFamily] using
      V.toNormFamily.dual_dual_pullback_eq hV hN
  rw [he]

/-- Source (4.39) for every actual adelic bundle, retaining the actual
bidual positive degree when original finite-place norms are not ultrametric. -/
theorem riemannRoch_inequality (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    0 ≤ (V.degree hS hN : EReal) -
      ((V.bidualOfMeasurableBase hS).positiveDegree hS hN -
        (V.dualOfMeasurableBase hS).positiveDegree hS hN) ∧
      (V.degree hS hN : EReal) -
        ((V.bidualOfMeasurableBase hS).positiveDegree hS hN -
          (V.dualOfMeasurableBase hS).positiveDegree hS hN) ≤
        (V.determinantDiscrepancy : EReal) := by
  obtain ⟨a, ha⟩ := (V.bidualOfMeasurableBase hS).exists_positiveDegree_eq_coe hS hN
  obtain ⟨b, hb⟩ := (V.dualOfMeasurableBase hS).exists_positiveDegree_eq_coe hS hN
  have hl := (V.bidualOfMeasurableBase hS).positiveDegree_sub_dual_le_degree hS hN
  rw [V.dual_bidualOfMeasurableBase hS, V.degree_bidualOfMeasurableBase hS hN,
    ha, hb, ← EReal.coe_sub] at hl
  have hlr := EReal.coe_le_coe_iff.mp hl
  have hu := (V.dualOfMeasurableBase hS).positiveDegree_sub_dual_le_degree hS hN
  rw [← V.positiveDegree_bidual_eq_doubleDual hS hN, ha, hb, ← EReal.coe_sub] at hu
  have hur := EReal.coe_le_coe_iff.mp hu
  have hδ := V.determinantDiscrepancy_eq_degree_add_degree_dual hS hN
  rw [ha, hb, ← EReal.coe_sub, ← EReal.coe_sub]
  constructor
  · exact_mod_cast (show 0 ≤ V.degree hS hN - (a - b) by linarith)
  · exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- Source (4.40) with the original bundle positive degree, under precisely
the original outside-infinity ultrametricity assumption. -/
theorem riemannRoch_inequality_of_isUltrametric (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsUltrametric) :
    0 ≤ (V.degree hS hN : EReal) -
      (V.positiveDegree hS hN - (V.dualOfMeasurableBase hS).positiveDegree hS hN) ∧
      (V.degree hS hN : EReal) -
        (V.positiveDegree hS hN - (V.dualOfMeasurableBase hS).positiveDegree hS hN) ≤
        (V.determinantDiscrepancy : EReal) := by
  simpa only [V.positiveDegree_bidual_eq_of_isUltrametric hS hN hV] using
    V.riemannRoch_inequality hS hN

/-- For actual Hermitian bundles the Riemann--Roch discrepancy vanishes,
so the original degree is the difference of the two actual positive degrees. -/
theorem degree_eq_positiveDegree_sub_dual_of_isHermitian (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) :
    (V.degree hS hN : EReal) = V.positiveDegree hS hN -
      (V.dualOfMeasurableBase hS).positiveDegree hS hN := by
  obtain ⟨a, ha⟩ := V.exists_positiveDegree_eq_coe hS hN
  obtain ⟨b, hb⟩ := (V.dualOfMeasurableBase hS).exists_positiveDegree_eq_coe hS hN
  have h := V.riemannRoch_inequality_of_isUltrametric hS hN hV.1
  rw [V.determinantDiscrepancy_eq_zero_of_isHermitian hN hV, EReal.coe_zero,
    ha, hb, ← EReal.coe_sub, ← EReal.coe_sub] at h
  have hz : (V.degree hS hN - (a - b) : EReal) = 0 := le_antisymm h.2 h.1
  have hzr : V.degree hS hN - (a - b) = 0 := by exact_mod_cast hz
  rw [ha, hb, ← EReal.coe_sub]
  apply congrArg (fun r : ℝ ↦ (r : EReal))
  linarith

end

end ArakelovGeometry.AdelicVectorBundle
