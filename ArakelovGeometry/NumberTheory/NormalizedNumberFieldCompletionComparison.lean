/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.EquivalentCompletion
public import ArakelovGeometry.NumberTheory.NormalizedNumberFieldLocalDegree

/-!
# The actual finite completed-field normalization map

The old ideal-norm completion and the actual source-normalized completion are
canonically isomorphic as algebras over the original number field. Their actual
completed norms satisfy the inverse-degree power relation, including at zero.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ArakelovGeometry.AdelicStructure

variable {K : Type*} [Field K] [NumberField K]

/-- The canonical actual old-to-normalized finite completed-field algebra map. -/
def normalizedFiniteCompletionEquiv (v : FinitePlace K) :
    v.val.Completion ≃ₐ[K]
      (normalizedPlaceValue ⟨Quotient.mk' v.val, mk_finitePlace_ne_trivialPlace v⟩).Completion :=
  AbsoluteValue.completionAlgEquivOfIsEquiv v.val _
    (Quotient.eq'.mp (normalizedPlaceValue_class
      ⟨Quotient.mk' v.val, mk_finitePlace_ne_trivialPlace v⟩)).symm

/-- The actual normalization map fixes the original number field. -/
theorem normalizedFiniteCompletionEquiv_coe (v : FinitePlace K) (a : K) :
    normalizedFiniteCompletionEquiv v (a : v.val.Completion) =
      (a : (normalizedPlaceValue
        ⟨Quotient.mk' v.val, mk_finitePlace_ne_trivialPlace v⟩).Completion) :=
  AbsoluteValue.completionAlgEquivOfIsEquiv_coe _ _ _ a

/-- The actual finite normalization map is continuous. -/
theorem continuous_normalizedFiniteCompletionEquiv (v : FinitePlace K) :
    Continuous (normalizedFiniteCompletionEquiv v) :=
  AbsoluteValue.continuous_completionAlgEquivOfIsEquiv _ _ _

/-- Its actual completed inverse is continuous. -/
theorem continuous_normalizedFiniteCompletionEquiv_symm (v : FinitePlace K) :
    Continuous (normalizedFiniteCompletionEquiv v).symm :=
  AbsoluteValue.continuous_completionAlgEquivOfIsEquiv_symm _ _ _

/-- The actual inverse local-degree power identity holds on every completed finite scalar. -/
theorem norm_normalizedFiniteCompletionEquiv (v : FinitePlace K) (z : v.val.Completion) :
    ‖normalizedFiniteCompletionEquiv v z‖ =
      ‖z‖ ^ (((normalizedPlaceValue
        ⟨Quotient.mk' v.val, mk_finitePlace_ne_trivialPlace v⟩).localDegree ℚ : ℝ)⁻¹) := by
  apply AbsoluteValue.norm_completionAlgEquivOfIsEquiv
  · apply inv_pos.mpr
    exact_mod_cast normalizedPlaceValue_finitePlace_localDegree_pos v
  · exact normalizedPlaceValue_eq_finitePlace_rpow v

/-- The actual completed valuation-ring unit ball is preserved and reflected. -/
theorem norm_normalizedFiniteCompletionEquiv_le_one_iff (v : FinitePlace K)
    (z : v.val.Completion) : ‖normalizedFiniteCompletionEquiv v z‖ ≤ 1 ↔ ‖z‖ ≤ 1 := by
  rw [norm_normalizedFiniteCompletionEquiv]
  have hd : (0 : ℝ) < ((normalizedPlaceValue
      ⟨Quotient.mk' v.val, mk_finitePlace_ne_trivialPlace v⟩).localDegree ℚ : ℝ) := by
    exact_mod_cast normalizedPlaceValue_finitePlace_localDegree_pos v
  simpa only [Real.one_rpow] using
    (Real.rpow_le_rpow_iff (norm_nonneg z) zero_le_one (inv_pos.mpr hd))

/-- Degree-weighted actual completed logarithms equal the old completed logarithm, also at zero. -/
theorem localDegree_mul_log_norm_normalizedFiniteCompletionEquiv
    (v : FinitePlace K) (z : v.val.Completion) :
    ((normalizedPlaceValue
      ⟨Quotient.mk' v.val, mk_finitePlace_ne_trivialPlace v⟩).localDegree ℚ : ℝ) *
      Real.log ‖normalizedFiniteCompletionEquiv v z‖ = Real.log ‖z‖ := by
  have hd : (0 : ℝ) < ((normalizedPlaceValue
      ⟨Quotient.mk' v.val, mk_finitePlace_ne_trivialPlace v⟩).localDegree ℚ : ℝ) := by
    exact_mod_cast normalizedPlaceValue_finitePlace_localDegree_pos v
  by_cases hz : z = 0
  · subst z
    simp
  · rw [norm_normalizedFiniteCompletionEquiv, Real.log_rpow (norm_pos_iff.mpr hz),
      ← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul]

/-- The true completed normalization exponent is the inverse canonical arithmetic degree. -/
theorem norm_normalizedFiniteCompletionEquiv_eq_rpow_inverse_ef
    (P : HeightOneSpectrum (𝓞 K)) (z : (FinitePlace.mk P).val.Completion) :
    ‖normalizedFiniteCompletionEquiv (FinitePlace.mk P) z‖ =
      ‖z‖ ^ (((P.asIdeal.ramificationIdx ℤ * P.asIdeal.inertiaDeg ℤ : ℕ) : ℝ)⁻¹) :=
  (norm_normalizedFiniteCompletionEquiv (FinitePlace.mk P) z).trans
    (congrArg (fun d : ℕ => ‖z‖ ^ ((d : ℝ)⁻¹))
      (ActualPrimeIndexing.normalizedPrime_localDegree_eq_ramificationIdx_mul_inertiaDeg P))

end ArakelovGeometry.AdelicStructure
