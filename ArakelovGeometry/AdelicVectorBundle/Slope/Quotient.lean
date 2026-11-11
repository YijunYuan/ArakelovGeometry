/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic
import ArakelovGeometry.AdelicVectorBundle.Degree.ExactSequence.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Source minimal slope as the infimum of actual quotient mean slopes

Actual quotient norms compose on completed fibres. Rank induction then finds
a nonzero quotient with maximal slope below any real upper bound for the
ambient mean slope. Degree superadditivity is the load-bearing step; no
maximal-slope finiteness or Harder--Narasimhan theorem is assumed.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u v w w' w''

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  {G : Type w''} [AddCommGroup G] [Module K G] [FiniteDimensional K G]

namespace NormFamily

omit [FiniteDimensional K G] in
/-- Actual quotient norms compose on the completed fibres. Common lower
bounds for lift norms are applied twice, so no optimal lift is assumed. -/
theorem pushforward_comp_norm (ξ : NormFamily S E)
    (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (ρ : F →ₗ[K] G) (hρ : Function.Surjective ρ)
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] G) :
    ((ξ.pushforward π hπ).pushforward ρ hρ).norm ω z =
      (ξ.pushforward (ρ.comp π) (hρ.comp hπ)).norm ω z := by
  apply le_antisymm
  · apply (ξ.le_quotientSeminorm_iff (ρ.comp π) (hρ.comp hπ) ω z _).mpr
    intro x hx
    rw [← hx, LinearMap.baseChange_comp, LinearMap.comp_apply]
    exact ((ξ.pushforward π hπ).pushforward_norm_le ρ hρ ω
      (π.baseChange (S.ϕ ω).Completion x)).trans (ξ.pushforward_norm_le π hπ ω x)
  · apply ((ξ.pushforward π hπ).le_quotientSeminorm_iff ρ hρ ω z _).mpr
    intro y hy
    apply (ξ.le_quotientSeminorm_iff π hπ ω y _).mpr
    intro x hx
    have hz : (ρ.comp π).baseChange (S.ϕ ω).Completion x = z := by
      rw [LinearMap.baseChange_comp, LinearMap.comp_apply, hx, hy]
    rw [← hz]
    exact ξ.pushforward_norm_le (ρ.comp π) (hρ.comp hπ) ω x

omit [FiniteDimensional K G] in
/-- Successive actual surjective quotient norm families are exactly the
actual quotient family of the composite rational map. -/
theorem pushforward_comp (ξ : NormFamily S E)
    (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (ρ : F →ₗ[K] G) (hρ : Function.Surjective ρ) :
    (ξ.pushforward π hπ).pushforward ρ hρ =
      ξ.pushforward (ρ.comp π) (hρ.comp hπ) := by
  ext ω z
  exact ξ.pushforward_comp_norm π hπ ρ hρ ω z

end NormFamily

namespace AdelicVectorBundle

variable [S.IsProper]

/-- Every iterated actual quotient has the maximal slope of the ambient
quotient by the kernel of the composite quotient map. -/
theorem maximalSlope_quotient_quotient_eq_quotient_ker (V : AdelicVectorBundle S E)
    (U : Submodule K E) (T : Submodule K (E ⧸ U))
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ((V.quotientOfMeasurableBase U hS).quotientOfMeasurableBase T hS).maximalSlope hS hN =
      (V.quotientOfMeasurableBase (T.mkQ.comp U.mkQ).ker hS).maximalSlope hS hN := by
  let π := T.mkQ.comp U.mkQ
  have hπ : Function.Surjective π := T.mkQ_surjective.comp U.mkQ_surjective
  symm
  apply maximalSlope_eq_of_completed_isometry _ _ (π.quotKerEquivOfSurjective hπ) hS hN
  intro ω z
  simp only [quotientOfMeasurableBase_toNormFamily]
  change ((V.toNormFamily.pushforward U.mkQ U.mkQ_surjective).pushforward
      T.mkQ T.mkQ_surjective).norm ω _ = (V.toNormFamily.quotient π.ker).norm ω z
  rw [V.toNormFamily.pushforward_comp_norm]
  exact V.toNormFamily.quotient_ker_equiv_norm_eq π hπ ω z

/-- All nonzero iterated actual quotients occur among the ambient source
quotients defining the minimal slope. -/
theorem minimalSlope_le_maximalSlope_quotient_quotient (V : AdelicVectorBundle S E)
    (U : Submodule K E) (T : Submodule K (E ⧸ U))
    (hT : 0 < Module.finrank K ((E ⧸ U) ⧸ T))
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.minimalSlope hS hN ≤
      ((V.quotientOfMeasurableBase U hS).quotientOfMeasurableBase T hS).maximalSlope hS hN := by
  rw [V.maximalSlope_quotient_quotient_eq_quotient_ker U T hS hN]
  apply V.minimalSlope_le_maximalSlope_quotient (T.mkQ.comp U.mkQ).ker _ hS hN
  rwa [((T.mkQ.comp U.mkQ).quotKerEquivOfSurjective
    (T.mkQ_surjective.comp U.mkQ_surjective)).finrank_eq]

/-- Passing to any actual quotient increases the source minimal slope.
This follows from the actual quotient composition, including zero quotients. -/
theorem minimalSlope_le_minimalSlope_quotient (V : AdelicVectorBundle S E)
    (U : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.minimalSlope hS hN ≤ (V.quotientOfMeasurableBase U hS).minimalSlope hS hN := by
  apply (V.quotientOfMeasurableBase U hS).le_minimalSlope hS hN
  intro T hT
  exact V.minimalSlope_le_maximalSlope_quotient_quotient U T hT hS hN

/-- If the mean slope is at most `c` and a nonzero subspace has mean
slope greater than `c`, its actual quotient is nonzero of smaller rank
and has mean slope strictly less than `c`. -/
theorem quotient_rank_and_slope_lt_of_lt_restrict (V : AdelicVectorBundle S E)
    (U : Submodule K E) (hU : 0 < Module.finrank K U)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (c : ℝ) (hmean : V.slope hS hN ≤ c)
    (hR : c < (V.restrictOfMeasurableBase U hS).slope hS hN) :
    0 < Module.finrank K (E ⧸ U) ∧
      Module.finrank K (E ⧸ U) < Module.finrank K E ∧
      (V.quotientOfMeasurableBase U hS).slope hS hN < c := by
  have hproper : U ≠ ⊤ := by
    intro htop
    rw [htop, V.slope_restrict_top hS hN] at hR
    exact (not_lt_of_ge hmean) hR
  have hdim := U.finrank_quotient_add_finrank
  have hRdim := Submodule.finrank_lt hproper
  have hQpos : 0 < Module.finrank K (E ⧸ U) := by omega
  have hQlt : Module.finrank K (E ⧸ U) < Module.finrank K E := by omega
  refine ⟨hQpos, hQlt, ?_⟩
  have hd := V.degree_restrict_add_degree_quotient_le U hS hN
  rw [(V.restrictOfMeasurableBase U hS).degree_eq_rank_mul_slope hS hN,
    (V.quotientOfMeasurableBase U hS).degree_eq_rank_mul_slope hS hN,
    V.degree_eq_rank_mul_slope hS hN] at hd
  have hUreal : (0 : ℝ) < Module.finrank K U := Nat.cast_pos.mpr hU
  have hQreal : (0 : ℝ) < Module.finrank K (E ⧸ U) := Nat.cast_pos.mpr hQpos
  have hdimreal : (Module.finrank K (E ⧸ U) : ℝ) + Module.finrank K U =
      Module.finrank K E := by exact_mod_cast hdim
  have hdimc := congrArg (fun r : ℝ => r * c) hdimreal
  rw [add_mul] at hdimc
  have hRc := mul_lt_mul_of_pos_left hR hUreal
  have hEc := mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg (Module.finrank K E))
  apply (mul_lt_mul_iff_right₀ hQreal).mp
  nlinarith

private theorem exists_quotient_maximalSlope_le_of_slope_le_aux (r : ℕ) :
    ∀ (E : Type w) [AddCommGroup E] [Module K E] [FiniteDimensional K E],
      Module.finrank K E = r →
      ∀ (V : AdelicVectorBundle S E)
        (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
        (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion),
        0 < Module.finrank K E → ∀ c : ℝ, V.slope hS hN ≤ c →
        ∃ U : Submodule K E, 0 < Module.finrank K (E ⧸ U) ∧
          (V.quotientOfMeasurableBase U hS).maximalSlope hS hN ≤ (c : EReal) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro E _ _ _ hdim V hS hN hr c hmean
    by_cases hmax : V.maximalSlope hS hN ≤ (c : EReal)
    · refine ⟨⊥, ?_, ?_⟩
      · have h := (⊥ : Submodule K E).finrank_quotient_add_finrank
        rw [finrank_bot, add_zero] at h
        rwa [h]
      · rwa [V.maximalSlope_quotient_bot hS hN]
    · have hhigh : (c : EReal) < V.maximalSlope hS hN := lt_of_not_ge hmax
      change (c : EReal) < ⨆ U : {U : Submodule K E // 0 < Module.finrank K U},
        ((V.restrictOfMeasurableBase U.val hS).slope hS hN : EReal) at hhigh
      obtain ⟨U, hUs⟩ := lt_iSup_iff.mp hhigh
      have hUsreal : c < (V.restrictOfMeasurableBase U.val hS).slope hS hN :=
        EReal.coe_lt_coe_iff.mp hUs
      have hQ := V.quotient_rank_and_slope_lt_of_lt_restrict U.val U.property
        hS hN c hmean hUsreal
      obtain ⟨T, hTpos, hTmax⟩ := ih (Module.finrank K (E ⧸ U.val))
        (by rw [← hdim]; exact hQ.2.1) (E ⧸ U.val) rfl
        (V.quotientOfMeasurableBase U.val hS) hS hN hQ.1 c hQ.2.2.le
      refine ⟨(T.mkQ.comp U.val.mkQ).ker, ?_, ?_⟩
      · rwa [((T.mkQ.comp U.val.mkQ).quotKerEquivOfSurjective
          (T.mkQ_surjective.comp U.val.mkQ_surjective)).finrank_eq]
      · rwa [← V.maximalSlope_quotient_quotient_eq_quotient_ker U.val T hS hN]

/-- A positive-rank bundle with mean at most a real `c` has an actual
nonzero quotient with maximal slope at most `c`. Rank induction uses
degree superadditivity and the actual quotient composition theorem. -/
theorem exists_quotient_maximalSlope_le_of_slope_le (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : 0 < Module.finrank K E) (c : ℝ) (hmean : V.slope hS hN ≤ c) :
    ∃ U : Submodule K E, 0 < Module.finrank K (E ⧸ U) ∧
      (V.quotientOfMeasurableBase U hS).maximalSlope hS hN ≤ (c : EReal) := by
  exact exists_quotient_maximalSlope_le_of_slope_le_aux (Module.finrank K E)
    E rfl V hS hN hr c hmean

/-- Source Proposition 4.3.26: minimal slope is at most mean slope in
positive rank. Neither extremum is assumed finite. -/
theorem minimalSlope_le_slope (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : 0 < Module.finrank K E) :
    V.minimalSlope hS hN ≤ (V.slope hS hN : EReal) := by
  obtain ⟨U, hU, hmax⟩ :=
    V.exists_quotient_maximalSlope_le_of_slope_le hS hN hr (V.slope hS hN) le_rfl
  exact (V.minimalSlope_le_maximalSlope_quotient U hU hS hN).trans hmax

/-- The source minimal slope is at most the mean of every nonzero
actual quotient. Iterated quotient norm composition is used through
minimal slope monotonicity. -/
theorem minimalSlope_le_slope_quotient (V : AdelicVectorBundle S E)
    (U : Submodule K E) (hU : 0 < Module.finrank K (E ⧸ U))
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.minimalSlope hS hN ≤ ((V.quotientOfMeasurableBase U hS).slope hS hN : EReal) := by
  exact (V.minimalSlope_le_minimalSlope_quotient U hS hN).trans
    ((V.quotientOfMeasurableBase U hS).minimalSlope_le_slope hS hN hU)

/-- Source Proposition 4.3.26 as an equality in the extended real line.
The original infimum of quotient maximal slopes equals the infimum
of actual quotient means. The formula also includes the zero bundle:
both infima are empty and equal to `⊤`. -/
theorem minimalSlope_eq_iInf_slope_quotient (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.minimalSlope hS hN =
      ⨅ U : {U : Submodule K E // 0 < Module.finrank K (E ⧸ U)},
        ((V.quotientOfMeasurableBase U.val hS).slope hS hN : EReal) := by
  apply le_antisymm
  · exact le_iInf fun U => V.minimalSlope_le_slope_quotient U.val U.property hS hN
  · apply V.le_minimalSlope hS hN
    intro U hU
    have hi : (⨅ W : {W : Submodule K E // 0 < Module.finrank K (E ⧸ W)},
        ((V.quotientOfMeasurableBase W.val hS).slope hS hN : EReal)) ≤
        ((V.quotientOfMeasurableBase U hS).slope hS hN : EReal) :=
      iInf_le (fun W : {W : Submodule K E // 0 < Module.finrank K (E ⧸ W)} =>
        ((V.quotientOfMeasurableBase W.val hS).slope hS hN : EReal)) ⟨U, hU⟩
    exact hi.trans ((V.quotientOfMeasurableBase U hS).slope_le_maximalSlope hS hN hU)

/-- The quotient mean bound also applies to arbitrary actual surjective
rational quotient presentations through their completed kernel normal form. -/
theorem minimalSlope_le_slope_pushforward (V : AdelicVectorBundle S E)
    (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (hm : (V.toNormFamily.pushforward π hπ).IsMeasurable)
    (hr : 0 < Module.finrank K F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.minimalSlope hS hN ≤ ((V.pushforward π hπ hm).slope hS hN : EReal) := by
  rw [V.slope_pushforward_eq_quotient_ker π hπ hm hS hN]
  apply V.minimalSlope_le_slope_quotient π.ker _ hS hN
  rwa [(π.quotKerEquivOfSurjective hπ).finrank_eq]

/-- Source minimal slope has a finite real upper bound in positive
rank; this conclusion does not assert a finite lower bound. -/
theorem minimalSlope_lt_top (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : 0 < Module.finrank K E) : V.minimalSlope hS hN < ⊤ :=
  (V.minimalSlope_le_slope hS hN hr).trans_lt (EReal.coe_lt_top _)

end AdelicVectorBundle

end

end ArakelovGeometry
