/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Slope.Subquotient
public import HarderNarasimhan.PayoffFunction.Convex
public import HarderNarasimhan.PayoffFunction.Semistable.Defs

import ArakelovGeometry.AdelicVectorBundle.Degree.Supermodular
import ArakelovGeometry.AdelicVectorBundle.Slope.LinearMap
import ArakelovGeometry.AdelicVectorBundle.Slope.Quotient
import Mathlib.RingTheory.Artinian.Module

/-!
# The maximal-slope game of an adelic vector bundle

The payoff uses actual restriction and quotient norms. Its maximum transform is
unchanged, and its first-player value equals the minimal slope on every interval.
This realizes the general, possibly non-Hermitian setting of Chen–Jeannin's
Harder–Narasimhan Games, Remark 2.5 and Theorem 3.10.
-/

@[expose] public section

open HarderNarasimhan
open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u w w'

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- An injective contraction cannot decrease maximal slope. -/
theorem maximalSlope_le_of_completed_contraction
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (f : V →ₗ[K] W) (hf : Function.Injective f)
    (hcontract : ∀ ω z, W.norm ω (f.baseChange (S.ϕ ω).Completion z) ≤ V.norm ω z) :
    V.maximalSlope ≤ W.maximalSlope := by
  have hheight := V.mapHeight_le_zero_of_completed_contraction W f hcontract
  exact (V.maximalSlope_le_maximalSlope_add_mapHeight_of_injective W f hf).trans
    (by simpa only [add_zero] using add_le_add le_rfl hheight)

variable (V : AdelicVectorBundle S)
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]

/-- The maximal-slope payoff of the actual normed subquotient of an interval. -/
def maximalSlopePayoff : PayoffFunction (Submodule K V) EReal :=
  ⟨fun I ↦ ((V.restrictOfMeasurableBase I.right).quotientOfMeasurableBase
    (I.left.comap I.right.subtype)).maximalSlope⟩

/-- The second-isomorphism contraction gives convexity of the adelic game. -/
instance maximalSlopePayoff_isConvex : (V.maximalSlopePayoff).IsConvex where
  le U W hUW := by
    change ((V.restrictOfMeasurableBase U).quotientOfMeasurableBase
      ((U ⊓ W).comap U.subtype)).maximalSlope ≤ _
    rw [Submodule.comap_inf]
    apply maximalSlope_le_of_completed_contraction _ _
      (LinearMap.quotientInfEquivSupQuotient U W).toLinearMap
      (LinearMap.quotientInfEquivSupQuotient U W).injective
    exact V.toNormFamily.quotientInfEquivSupQuotient_norm_le U W

/-- Enlarging the upper subspace embeds one normed subquotient into another. -/
theorem maximalSlope_subquotient_mono (A B C : Submodule K V) (hBC : B ≤ C) :
    ((V.restrictOfMeasurableBase B).quotientOfMeasurableBase
      (A.comap B.subtype)).maximalSlope ≤
    ((V.restrictOfMeasurableBase C).quotientOfMeasurableBase
      (A.comap C.subtype)).maximalSlope := by
  let P := A.comap B.subtype
  let Q := A.comap C.subtype
  let i : B →ₗ[K] C := Submodule.inclusion hBC
  have hcomap : Q.comap i = P := rfl
  let f : (B ⧸ P) →ₗ[K] (C ⧸ Q) := P.mapQ Q i hcomap.ge
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_mapQ, hcomap, Submodule.mkQ_map_self]
  apply maximalSlope_le_of_completed_contraction _ _ f hf
  intro ω z
  apply ((V.toNormFamily.restrict B).le_quotientSeminorm_iff
    P.mkQ P.mkQ_surjective ω z _).mpr
  intro x hx
  have hcomm := DFunLike.congr_fun
    (congrArg (fun g ↦ g.baseChange (S.ϕ ω).Completion)
      (Submodule.mapQ_mkQ P Q i (h := hcomap.ge))) x
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at hcomm
  change ((V.toNormFamily.restrict C).quotient Q).norm ω
      (f.baseChange (S.ϕ ω).Completion z) ≤ (V.toNormFamily.restrict B).norm ω x
  rw [← hx, hcomm]
  have h := (V.toNormFamily.restrict C).quotient_norm_mk_le Q ω
    (i.baseChange (S.ϕ ω).Completion x)
  have hi : C.subtype.comp i = B.subtype := Submodule.subtype_comp_inclusion B C hBC
  have hiω := DFunLike.congr_fun
    (congrArg (fun g ↦ g.baseChange (S.ϕ ω).Completion) hi) x
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at hiω
  simpa only [NormFamily.restrict_norm, LinearMap.baseChange_comp,
    LinearMap.comp_apply, hiω] using h

/-- The maximal-slope payoff is already fixed by the game's `max` operation. -/
theorem max_maximalSlopePayoff (I : StrictIntvl (Submodule K V)) :
    (V.maximalSlopePayoff).max I = V.maximalSlopePayoff I := by
  apply le_antisymm _ PayoffFunction.apply_le_max
  apply PayoffFunction.max_le
  intro U hU
  exact V.maximalSlope_subquotient_mono I.left U I.right hU.2

/-- The game's first-player value is an infimum over actual intermediate quotients. -/
theorem A_maximalSlopePayoff (I : StrictIntvl (Submodule K V)) :
    (V.maximalSlopePayoff).A I =
      ⨅ (U : Submodule K V) (_ : I.left ≤ U ∧ U < I.right),
        ((V.restrictOfMeasurableBase I.right).quotientOfMeasurableBase
          (U.comap I.right.subtype)).maximalSlope := by
  simp only [PayoffFunction.A_apply, V.max_maximalSlopePayoff]
  rfl

/-- Player A's value is the minimal slope of the actual normed subquotient. -/
theorem A_maximalSlopePayoff_eq_minimalSlope (I : StrictIntvl (Submodule K V)) :
    (V.maximalSlopePayoff).A I =
      ((V.restrictOfMeasurableBase I.right).quotientOfMeasurableBase
        (I.left.comap I.right.subtype)).minimalSlope := by
  rw [V.A_maximalSlopePayoff]
  let W := V.restrictOfMeasurableBase I.right
  let T := I.left.comap I.right.subtype
  let Q := W.quotientOfMeasurableBase T
  apply le_antisymm
  · apply Q.le_minimalSlope
    intro Z hZ
    rw [W.maximalSlope_quotient_quotient_eq_quotient_ker T Z]
    let R : Submodule K I.right := (Z.mkQ.comp T.mkQ).ker
    let U : Submodule K V := R.map I.right.subtype
    have hTR : T ≤ R := by
      simpa only [R, LinearMap.ker_comp, Submodule.ker_mkQ] using T.le_comap_mkQ Z
    have hleft : I.left ≤ U := by
      have h := Submodule.map_mono (f := I.right.subtype) hTR
      simpa only [T, Submodule.map_comap_subtype, inf_eq_right.mpr I.lt.le] using h
    have hRpos : 0 < Module.finrank K (I.right ⧸ R) := by
      rw [((Z.mkQ.comp T.mkQ).quotKerEquivOfSurjective
        (Z.mkQ_surjective.comp T.mkQ_surjective)).finrank_eq]
      exact hZ
    have hRtop : R ≠ ⊤ := by
      intro he
      have hdim := R.finrank_quotient_add_finrank
      rw [he, finrank_top] at hdim
      rw [he] at hRpos
      omega
    have hright : U < I.right := by
      have h := I.right.mapIic.strictMono (lt_top_iff_ne_top.mpr hRtop)
      change (I.right.mapIic R : Submodule K V) < I.right.mapIic ⊤ at h
      simpa only [Submodule.coe_mapIic_apply, Submodule.map_subtype_top] using h
    have hcomap : U.comap I.right.subtype = R :=
      Submodule.comap_map_eq_of_injective I.right.subtype_injective R
    exact iInf_le_of_le U (iInf_le_of_le ⟨hleft, hright⟩ (by rw [hcomap]))
  · apply le_iInf
    intro U
    apply le_iInf
    intro hU
    let R := U.comap I.right.subtype
    let Z := R.map T.mkQ
    have hTR : T ≤ R := Submodule.comap_mono hU.1
    have hker : (Z.mkQ.comp T.mkQ).ker = R := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]
      exact Submodule.comap_map_eq_self (by simpa only [Submodule.ker_mkQ] using hTR)
    have hZtop : Z ≠ ⊤ := by
      intro he
      have hRtop : R = ⊤ := by
        rw [← hker, LinearMap.ker_comp, Submodule.ker_mkQ, he, Submodule.comap_top]
      exact hU.2.not_ge (Submodule.comap_subtype_eq_top.mp hRtop)
    have hZpos : 0 < Module.finrank K ((I.right ⧸ T) ⧸ Z) := by
      have hdim := Z.finrank_quotient_add_finrank
      have hlt := Submodule.finrank_lt hZtop
      omega
    have h := Q.minimalSlope_le_maximalSlope_quotient Z hZpos
    rw [W.maximalSlope_quotient_quotient_eq_quotient_ker T Z, hker] at h
    exact h

/-- On an initial interval, player A's value is exactly the existing minimal slope. -/
theorem A_maximalSlopePayoff_bot (B : Submodule K V) (hB : ⊥ < B) :
    (V.maximalSlopePayoff).A ⟨⊥, B, hB⟩ =
      (V.restrictOfMeasurableBase B).minimalSlope := by
  rw [V.A_maximalSlopePayoff_eq_minimalSlope, Submodule.comap_bot, Submodule.ker_subtype]
  exact minimalSlope_quotient_bot _

/-- The game's descending-chain condition comes from finite dimensionality. -/
instance maximalSlopePayoff_adcc : (V.maximalSlopePayoff).ADCC where
  dcc _ f _ hf := (not_strictAnti_of_wellFoundedLT f hf).elim


end

end ArakelovGeometry.AdelicVectorBundle
