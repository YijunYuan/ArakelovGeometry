/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.ParameterSpace
public import ArakelovGeometry.AdelicStructure.RationalPlaceClasses
public import ArakelovGeometry.Analysis.NonarchimedeanPowerCompletion
public import ArakelovGeometry.ExternalResults.Ostrowski
public import ArakelovGeometry.ExternalResults.Place
public import ArakelovGeometry.NumberTheory.InfinitePlaceLocalDegree

/-!
# Actual normalized extension parameters for number-field places

Canonical rational restrictions select a unique representative of every
nontrivial number-field place, independently of local-degree normalization.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.AdelicStructure.NormalizedNumberFieldPlaces

variable {K : Type*} [Field K] [NumberField K]

/-- Nontrivial values on a genuine number field have nontrivial rational restrictions. -/
theorem isNontrivial_restriction_rat (v : AbsoluteValue K ℝ) (hv : v.IsNontrivial) :
    (v.under ℚ).IsNontrivial := by
  by_contra h
  exact (AbsoluteValue.not_isNontrivial_of_finite v ℚ h) hv

/-- An actual normalized parameter can never induce the trivial value. -/
theorem parameter_isNontrivial (x : ParameterSpaceExtension rationalAdelicStructure K) :
    x.abv.IsNontrivial := by
  obtain ⟨q, hq0, hq⟩ := rationalAdelicStructure_phi_isNontrivial x.base
  refine ⟨algebraMap ℚ K q, (map_ne_zero_iff _ (algebraMap ℚ K).injective).mpr hq0, ?_⟩
  change (x.abv.under ℚ) q ≠ 1
  rwa [x.restrict_eq]

/-- Actual normalized parameters are equal when their absolute values are equivalent. -/
theorem parameter_eq_of_isEquiv {x y : ParameterSpaceExtension rationalAdelicStructure K}
    (h : x.abv.IsEquiv y.abv) : x = y := by
  have hr : (x.abv.under ℚ).IsEquiv (y.abv.under ℚ) :=
    fun a b => h (algebraMap ℚ K a) (algebraMap ℚ K b)
  have hb : x.base = y.base := by
    rw [x.restrict_eq, y.restrict_eq] at hr
    exact rationalAdelicStructure_phi_isEquiv_iff.mp hr
  have he : x.abv.under ℚ = y.abv.under ℚ := by
    rw [x.restrict_eq, y.restrict_eq, hb]
  have hn : (x.abv.under ℚ).IsNontrivial := by
    rw [x.restrict_eq]
    exact rationalAdelicStructure_phi_isNontrivial x.base
  exact ParameterSpaceExtension.ext rationalAdelicStructure K hb
    (AbsoluteValue.eq_of_isEquiv_of_nontrivial_rat_restriction h he hn)

/-- Every genuinely nontrivial number-field value has an actual normalized parameter. -/
theorem exists_parameter_isEquiv (v : AbsoluteValue K ℝ) (hv : v.IsNontrivial) :
    ∃ x : ParameterSpaceExtension rationalAdelicStructure K, v.IsEquiv x.abv := by
  by_cases hna : IsNonarchimedean v
  · have hqn : IsNonarchimedean (v.under ℚ) := by
      intro a b
      change v (algebraMap ℚ K (a + b)) ≤
        max (v (algebraMap ℚ K a)) (v (algebraMap ℚ K b))
      rw [map_add]
      exact hna _ _
    rcases Rat.AbsoluteValue.equiv_real_or_padic _ (isNontrivial_restriction_rat v hv)
      with hr | ⟨p, ⟨hp, hq⟩, _⟩
    · have hh := (NumberField.isNonarchimedean_congr hr).mp hqn
      exact False.elim (rationalAdelicStructure_infinite_mem_inf hh)
    · obtain ⟨c, hc, hpow⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hq
      let x : ParameterSpaceExtension rationalAdelicStructure K := {
        base := Sum.inl ⟨p, hp.out⟩
        abv := AbsoluteValue.nonarchimedeanRpow v hna c hc
        restrict_eq := by
          ext a
          exact congrFun hpow a }
      exact ⟨x, AbsoluteValue.isEquiv_nonarchimedeanRpow v hna c hc⟩
  · obtain ⟨w, hw⟩ := NumberField.exists_infinitePlace_of_not_isNonarchimedean hna
    exact ⟨⟨Sum.inr (), w.val, w.restriction_rat⟩, hw⟩

/-- Every nontrivial actual place class has a unique normalized extension parameter. -/
theorem existsUnique_parameter_class (ω : AbsoluteValue.Place K)
    (hω : ω ≠ AbsoluteValue.trivialPlace K) :
    ∃! x : ParameterSpaceExtension rationalAdelicStructure K,
      (Quotient.mk' x.abv : AbsoluteValue.Place K) = ω := by
  classical
  have hn : ω.out.IsNontrivial := by
    rw [AbsoluteValue.isNontrivial_iff_ne_trivial]
    intro h
    apply hω
    rw [← Quotient.out_eq ω, h]
    rfl
  obtain ⟨x, hx⟩ := exists_parameter_isEquiv ω.out hn
  have hc : (Quotient.mk' x.abv : AbsoluteValue.Place K) = ω :=
    (Quotient.sound' hx.symm).trans (Quotient.out_eq ω)
  refine ⟨x, hc, fun y hy => ?_⟩
  apply parameter_eq_of_isEquiv
  exact Quotient.eq'.mp (hy.trans hc.symm)

/-- The actual parameter set is canonically the set of nontrivial number-field places. -/
def parameterEquivNontrivialPlace :
    ParameterSpaceExtension rationalAdelicStructure K ≃
      {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K} := by
  classical
  exact Equiv.ofBijective (fun x => ⟨Quotient.mk' x.abv, by
    intro h
    have he : x.abv = AbsoluteValue.trivial :=
      AbsoluteValue.isEquiv_trivial_iff_eq_trivial.mp (Quotient.eq'.mp h)
    exact (AbsoluteValue.isNontrivial_iff_ne_trivial x.abv).mp
      (parameter_isNontrivial x) he⟩) (by
        constructor
        · intro x y h
          apply parameter_eq_of_isEquiv
          exact Quotient.eq'.mp (congrArg Subtype.val h)
        · intro ω
          obtain ⟨x, hx, _⟩ := existsUnique_parameter_class ω.val ω.property
          exact ⟨x, Subtype.ext hx⟩)

end ArakelovGeometry.AdelicStructure.NormalizedNumberFieldPlaces
