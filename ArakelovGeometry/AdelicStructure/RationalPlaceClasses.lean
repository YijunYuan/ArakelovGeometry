/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicStructure.RationalNormalization
public import Mathlib.Analysis.AbsoluteValue.Equivalence

/-!
# Actual rational parameters and absolute-value classes

The canonical rational prime and real values distinguish equivalence
classes and exhaust all nontrivial rational absolute values.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.AdelicStructure

open AdelicCurve.RationalFunction

/-- All source rational parameters have genuinely nontrivial absolute values. -/
theorem rationalAdelicStructure_phi_isNontrivial (ω : rationalAdelicStructure.Ω) :
    (rationalAdelicStructure.ϕ ω).IsNontrivial := by
  cases ω with
  | inl p =>
      refine ⟨(p.val : ℚ), Nat.cast_ne_zero.mpr p.property.ne_zero, ?_⟩
      rw [rationalAdelicStructure_prime_apply_prime]
      exact ne_of_lt (inv_lt_one_of_one_lt₀ (by exact_mod_cast p.property.one_lt))
  | inr u =>
      cases u
      refine ⟨(2 : ℚ), by norm_num, ?_⟩
      norm_num [Rat.AbsoluteValue.real_eq_abs]

/-- Equivalent canonical rational values have exactly the same actual parameter. -/
theorem rationalAdelicStructure_phi_isEquiv_iff
    {ω η : rationalAdelicStructure.Ω} :
    (rationalAdelicStructure.ϕ ω).IsEquiv (rationalAdelicStructure.ϕ η) ↔ ω = η := by
  constructor
  · intro h
    cases ω with
    | inl p =>
        let : Fact p.val.Prime := ⟨p.property⟩
        cases η with
        | inl q =>
            let : Fact q.val.Prime := ⟨q.property⟩
            change (Rat.AbsoluteValue.padic p.val).IsEquiv
              (Rat.AbsoluteValue.padic q.val) at h
            have hnt := rationalAdelicStructure_phi_isNontrivial (Sum.inl p)
            change (Rat.AbsoluteValue.padic p.val).IsNontrivial at hnt
            rcases Rat.AbsoluteValue.equiv_real_or_padic _ hnt with hr | ⟨r, hr, hu⟩
            · exact False.elim ((Rat.AbsoluteValue.not_real_isEquiv_padic p.val) hr.symm)
            · have hp : p.val = r := hu p.val ⟨inferInstance, .refl _⟩
              have hq : q.val = r := hu q.val ⟨inferInstance, h⟩
              exact congrArg Sum.inl (Subtype.ext (hp.trans hq.symm))
        | inr u =>
            cases u
            exact False.elim ((Rat.AbsoluteValue.not_real_isEquiv_padic p.val) h.symm)
    | inr u =>
        cases u
        cases η with
        | inl p =>
            let : Fact p.val.Prime := ⟨p.property⟩
            exact False.elim ((Rat.AbsoluteValue.not_real_isEquiv_padic p.val) h)
        | inr u =>
            cases u
            rfl
  · rintro rfl
    exact .refl _

/-- Every nontrivial rational absolute-value class has an actual source parameter. -/
theorem exists_rationalAdelicStructure_phi_isEquiv (v : AbsoluteValue ℚ ℝ)
    (hv : v.IsNontrivial) : ∃ ω : rationalAdelicStructure.Ω,
      v.IsEquiv (rationalAdelicStructure.ϕ ω) := by
  rcases Rat.AbsoluteValue.equiv_real_or_padic v hv with h | ⟨p, ⟨hp, h⟩, _⟩
  · exact ⟨Sum.inr (), h⟩
  · exact ⟨Sum.inl ⟨p, hp.out⟩, h⟩

end ArakelovGeometry.AdelicStructure

namespace AbsoluteValue

/-- A genuinely nontrivial fixed rational restriction forces equivalent values equal. -/
theorem eq_of_isEquiv_of_nontrivial_rat_restriction {K : Type*} [Field K]
    [Algebra ℚ K] {v w : AbsoluteValue K ℝ} (h : v.IsEquiv w)
    (hr : v.under ℚ = w.under ℚ)
    (hnt : (v.under ℚ).IsNontrivial) : v = w := by
  obtain ⟨c, hc, hpow⟩ := isEquiv_iff_exists_rpow_eq.mp h
  obtain ⟨q, hq⟩ := hnt.exists_abv_gt_one
  have hqr : v (algebraMap ℚ K q) = w (algebraMap ℚ K q) :=
    congrArg (fun z : AbsoluteValue ℚ ℝ => z q) hr
  have he : v (algebraMap ℚ K q) ^ c = v (algebraMap ℚ K q) ^ (1 : ℝ) := by
    calc
      _ = w (algebraMap ℚ K q) := congrFun hpow (algebraMap ℚ K q)
      _ = _ := by rw [← hqr, Real.rpow_one]
  have hc₁ : c = 1 := (Real.rpow_right_inj (zero_lt_one.trans hq) hq.ne').mp he
  ext a
  simpa [hc₁] using congrFun hpow a

end AbsoluteValue
