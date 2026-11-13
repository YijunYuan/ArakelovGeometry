/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DirectSum.Basic
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Strong

import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Subquotient
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Hermitian.Basis
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Domination of direct sums

Proposition 4.1.19(4) permits arbitrary convex profiles equal to the maximum
outside a measurable set of finite measure. No measurability of the profiles
is imposed. The Archimedean correction in the dual bound is retained.
-/

@[expose] public section

open MeasureTheory Filter
open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u w w'

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E]
  {F : Type w'} [AddCommGroup F] [Module K F]
  (ξ : NormFamily S E) (η : NormFamily S F)

/-- The maximum direct sum in the canonical completed-product coordinates. -/
theorem maxDirectSum_norm (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] (E × F)) :
    (ξ.maxDirectSum η).norm ω z =
      max (ξ.norm ω ((TensorProduct.prodRight K (S.ϕ ω).Completion
        (S.ϕ ω).Completion E F z).1))
        (η.norm ω ((TensorProduct.prodRight K (S.ϕ ω).Completion
          (S.ϕ ω).Completion E F z).2)) :=
  NormShape.maxShape_perspective (apply_nonneg _ _) (apply_nonneg _ _)

/-- Every admissible profile dominates the coordinate maximum. -/
theorem maxDirectSum_le_directSum (ψ : S.Ω → NormShape) :
    ξ.maxDirectSum η ≤ ξ.directSum η ψ := by
  intro ω z
  rw [maxDirectSum_norm, directSum_norm]
  exact (ψ ω).max_le_perspective (apply_nonneg _ _) (apply_nonneg _ _)

/-- A profile supported away from the maximum on `U` costs at most a factor
two on `U` and no factor outside it. -/
theorem directSum_norm_le_exp_indicator_mul_max (ψ : S.Ω → NormShape) (U : Set S.Ω)
    (hψ : ∀ ω ∉ U, Set.EqOn (ψ ω).toFun NormShape.maxShape.toFun (Set.Icc (0 : ℝ) 1))
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] (E × F)) :
    (ξ.directSum η ψ).norm ω z ≤
      Real.exp (U.indicator (fun _ => Real.log 2) ω) * (ξ.maxDirectSum η).norm ω z := by
  classical
  rw [directSum_norm, maxDirectSum_norm]
  by_cases hω : ω ∈ U
  · rw [Set.indicator_of_mem hω, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    apply ((ψ ω).perspective_le_add (apply_nonneg _ _) (apply_nonneg _ _)).trans
    nlinarith [le_max_left
      (ξ.norm ω ((TensorProduct.prodRight K (S.ϕ ω).Completion
        (S.ϕ ω).Completion E F z).1))
      (η.norm ω ((TensorProduct.prodRight K (S.ϕ ω).Completion
        (S.ϕ ω).Completion E F z).2)),
      le_max_right
      (ξ.norm ω ((TensorProduct.prodRight K (S.ϕ ω).Completion
        (S.ϕ ω).Completion E F z).1))
      (η.norm ω ((TensorProduct.prodRight K (S.ϕ ω).Completion
        (S.ϕ ω).Completion E F z).2))]
  · rw [Set.indicator_of_notMem hω, Real.exp_zero, one_mul]
    exact le_of_eq (((ψ ω).perspective_congr NormShape.maxShape (hψ ω hω)
      (apply_nonneg _ _) (apply_nonneg _ _)).trans
        (NormShape.maxShape_perspective (apply_nonneg _ _) (apply_nonneg _ _)))

/-- One upper-dominated rational vector has a nonnegative integrable
exponential bound. This formulation includes the zero vector. -/
theorem IsUpperDominated.exists_norm_exp_bound {ξ : NormFamily S E}
    (hξ : ξ.IsUpperDominated) (x : E) :
    ∃ A : S.Ω → ℝ, Integrable A S.v ∧ (∀ ω, 0 ≤ A ω) ∧
      ∀ᵐ ω ∂S.v, ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) ≤ Real.exp (A ω) := by
  by_cases hx : x = 0
  · refine ⟨0, integrable_zero _ _ _, fun _ => le_rfl, Eventually.of_forall ?_⟩
    intro ω
    simp only [hx, TensorProduct.tmul_zero, norm_zero, Pi.zero_apply, Real.exp_zero, zero_le_one]
  · obtain ⟨A, hA, hbound⟩ := hξ x hx
    refine ⟨fun ω => |A ω|, hA.abs, fun ω => abs_nonneg _, ?_⟩
    filter_upwards [hbound] with ω hω
    exact (Real.log_le_iff_le_exp (ξ.norm_rational_pos ω hx)).mp
      (hω.trans (le_abs_self _))

/-- The maximum sum of two upper-dominated norm families is upper dominated. -/
theorem IsUpperDominated.maxDirectSum {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsUpperDominated) (hη : η.IsUpperDominated) :
    (ξ.maxDirectSum η).IsUpperDominated := by
  constructor
  rintro ⟨x, y⟩ hxy
  obtain ⟨A, hA, hA0, hx⟩ := hξ.exists_norm_exp_bound x
  obtain ⟨B, hB, hB0, hy⟩ := hη.exists_norm_exp_bound y
  refine ⟨A + B, hA.add hB, ?_⟩
  filter_upwards [hx, hy] with ω hxω hyω
  apply (Real.log_le_iff_le_exp ((ξ.maxDirectSum η).norm_rational_pos ω hxy)).mpr
  rw [maxDirectSum_norm, TensorProduct.prodRight_tmul]
  exact max_le (hxω.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_right (hB0 ω))))
    (hyω.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left (hA0 ω))))

variable [FiniteDimensional K E] [FiniteDimensional K F]

/-- A completed rational functional on a product splits along the two
actual completed projections. -/
theorem dualBaseChange_one_prod_apply (ℓ : Module.Dual K (E × F)) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (E × F)) :
    dualBaseChangeEquiv K (S.ϕ ω).Completion (E × F)
        ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ) z =
      dualBaseChangeEquiv K (S.ϕ ω).Completion E
          ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ.comp (LinearMap.inl K E F))
          ((LinearMap.fst K E F).baseChange (S.ϕ ω).Completion z) +
        dualBaseChangeEquiv K (S.ϕ ω).Completion F
          ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ.comp (LinearMap.inr K E F))
          ((LinearMap.snd K E F).baseChange (S.ϕ ω).Completion z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a p =>
      have hp : ℓ p = ℓ (p.1, 0) + ℓ (0, p.2) := by
        rw [← map_add]
        simp
      simp only [LinearMap.baseChange_tmul, LinearMap.fst_apply, LinearMap.snd_apply,
        dualBaseChangeEquiv_tmul_apply_tmul, one_mul, LinearMap.comp_apply,
        LinearMap.inl_apply, LinearMap.inr_apply, hp, map_add, mul_add]
  | add x y hx hy =>
      simp only [map_add, hx, hy]
      ring

/-- The dual of any profile sum is bounded by the maximum of the two
restricted dual norms, with a factor two only at infinite places. -/
theorem directSum_dual_norm_rational_le (ψ : S.Ω → NormShape) (ω : S.Ω)
    (ℓ : Module.Dual K (E × F)) :
    (ξ.directSum η ψ).dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ) ≤
      Real.exp (S.Ωinf.indicator (fun _ => Real.log 2) ω) *
        max (ξ.dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ.comp (LinearMap.inl K E F)))
          (η.dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ.comp (LinearMap.inr K E F))) := by
  classical
  let A := ξ.dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ.comp (LinearMap.inl K E F))
  let B := η.dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ.comp (LinearMap.inr K E F))
  have hAB : 0 ≤ max A B := (ξ.dual.norm_nonneg ω _).trans (le_max_left _ _)
  apply (ξ.directSum η ψ).dual_norm_le ω _ (mul_nonneg (Real.exp_pos _).le hAB)
  intro z
  rw [dualBaseChange_one_prod_apply]
  have h₁ := (ξ.norm_dual_apply_le ω
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ.comp (LinearMap.inl K E F))
      ((LinearMap.fst K E F).baseChange (S.ϕ ω).Completion z)).trans
    (mul_le_mul (le_max_left A B) (ξ.directSum_norm_fst_le η ψ ω z)
      (ξ.norm_nonneg ω _) hAB)
  have h₂ := (η.norm_dual_apply_le ω
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ.comp (LinearMap.inr K E F))
      ((LinearMap.snd K E F).baseChange (S.ϕ ω).Completion z)).trans
    (mul_le_mul (le_max_right A B) (ξ.directSum_norm_snd_le η ψ ω z)
      (η.norm_nonneg ω _) hAB)
  by_cases hω : ω ∈ S.Ωinf
  · rw [Set.indicator_of_mem hω, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact (_root_.norm_add_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by dsimp [A, B]; ring))
  · rw [Set.indicator_of_notMem hω, Real.exp_zero, one_mul]
    exact (S.norm_add_le_max_of_finite ω (not_not.mp hω) _ _).trans (max_le h₁ h₂)

/-- The profile correction is supported exactly on its exceptional set. -/
theorem localDist_maxDirectSum_directSum_le (ψ : S.Ω → NormShape) (U : Set S.Ω)
    (hψ : ∀ ω ∉ U, Set.EqOn (ψ ω).toFun NormShape.maxShape.toFun (Set.Icc (0 : ℝ) 1))
    (ω : S.Ω) :
    (ξ.maxDirectSum η).localDist (ξ.directSum η ψ) ω ≤
      U.indicator (fun _ => Real.log 2) ω := by
  have hn : 0 ≤ U.indicator (fun _ => Real.log 2) ω :=
    Set.indicator_nonneg (fun _ _ => Real.log_nonneg (by norm_num)) ω
  apply ((ξ.maxDirectSum η).localDist_le_iff_norm_le (ξ.directSum η ψ) ω hn).mpr
  intro z
  exact ⟨(ξ.maxDirectSum_le_directSum η ψ ω z).trans
    (le_mul_of_one_le_left ((ξ.directSum η ψ).norm_nonneg ω z) (Real.one_le_exp_iff.mpr hn)),
    ξ.directSum_norm_le_exp_indicator_mul_max η ψ U hψ ω z⟩

/-- Finite measurable support makes the arbitrary profile correction dominated. -/
theorem localDist_maxDirectSum_directSum_hasIntegrableBounds (ψ : S.Ω → NormShape)
    (U : Set S.Ω) (hU : MeasurableSet U) (hfin : S.v U < ⊤)
    (hψ : ∀ ω ∉ U, Set.EqOn (ψ ω).toFun NormShape.maxShape.toFun (Set.Icc (0 : ℝ) 1)) :
    HasIntegrableBounds ((ξ.maxDirectSum η).localDist (ξ.directSum η ψ)) S.v := by
  refine ⟨⟨U.indicator (fun _ => Real.log 2), ?_,
    Eventually.of_forall (ξ.localDist_maxDirectSum_directSum_le η ψ U hψ)⟩,
    ⟨0, integrable_zero _ _ _, Eventually.of_forall ((ξ.maxDirectSum η).localDist_nonneg _)⟩⟩
  exact (integrable_indicator_iff hU).mpr (integrableOn_const hfin.ne)

/-- The dual upper-domination bound is independent of the profile. Its
only measure correction is the finite measure of the infinite places. -/
theorem directSum_dual_isUpperDominated (ψ : S.Ω → NormShape)
    [hξ : ξ.dual.IsUpperDominated] [hη : η.dual.IsUpperDominated]
    (hfin : S.v S.Ωinf < ⊤) : (ξ.directSum η ψ).dual.IsUpperDominated := by
  constructor
  intro ℓ hℓ
  obtain ⟨A, hA, hA0, hℓ₁⟩ := hξ.exists_norm_exp_bound (ℓ.comp (LinearMap.inl K E F))
  obtain ⟨B, hB, hB0, hℓ₂⟩ := hη.exists_norm_exp_bound (ℓ.comp (LinearMap.inr K E F))
  let R : S.Ω → ℝ := S.Ωinf.indicator (fun _ => Real.log 2)
  have hR : Integrable R S.v :=
    (integrable_indicator_iff S.measurableSet_Ωinf).mpr (integrableOn_const hfin.ne)
  refine ⟨fun ω => R ω + (A ω + B ω), hR.add (hA.add hB), ?_⟩
  filter_upwards [hℓ₁, hℓ₂] with ω h₁ h₂
  apply (Real.log_le_iff_le_exp ((ξ.directSum η ψ).dual.norm_rational_pos ω hℓ)).mpr
  calc
    (ξ.directSum η ψ).dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ) ≤
        Real.exp (R ω) *
          max (ξ.dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ.comp (LinearMap.inl K E F)))
            (η.dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ.comp (LinearMap.inr K E F))) :=
      ξ.directSum_dual_norm_rational_le η ψ ω ℓ
    _ ≤ Real.exp (R ω) * Real.exp (A ω + B ω) :=
      mul_le_mul_of_nonneg_left
        (max_le (h₁.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_right (hB0 ω))))
          (h₂.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left (hA0 ω)))))
        (Real.exp_pos _).le
    _ = Real.exp (R ω + (A ω + B ω)) := (Real.exp_add _ _).symm

/-- The maximum direct sum of dominated families is dominated whenever
the infinite places have finite measure. -/
theorem IsDominated.maxDirectSum {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsDominated) (hη : η.IsDominated) (hfin : S.v S.Ωinf < ⊤) :
    (ξ.maxDirectSum η).IsDominated :=
  ⟨hξ.1.maxDirectSum hη.1,
    ξ.directSum_dual_isUpperDominated η (fun _ ↦ NormShape.maxShape) (hξ := hξ.2)
        (hη := hη.2) hfin⟩

/-- Domination for arbitrary profiles with finite exceptional support.
The infinite-place and profile corrections are separate integrable terms. -/
theorem IsDominated.directSum_of_measure_lt_top {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsDominated) (hη : η.IsDominated) (ψ : S.Ω → NormShape)
    (U : Set S.Ω) (hU : MeasurableSet U) (hfinU : S.v U < ⊤)
    (hψ : ∀ ω ∉ U, Set.EqOn (ψ ω).toFun NormShape.maxShape.toFun (Set.Icc (0 : ℝ) 1))
    (hfin : S.v S.Ωinf < ⊤) : (ξ.directSum η ψ).IsDominated :=
  (hξ.maxDirectSum hη hfin).of_localDist
    (ξ.localDist_maxDirectSum_directSum_hasIntegrableBounds η ψ U hU hfinU hψ).1

/-- The domination clause of Proposition 4.1.19(4), retaining the usual
Archimedean normalization that supplies finite measure of the infinite places. -/
theorem IsDominated.directSum {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsDominated) (hη : η.IsDominated) (ψ : S.Ω → NormShape)
    (U : Set S.Ω) (hU : MeasurableSet U) (hfinU : S.v U < ⊤)
    (hψ : ∀ ω ∉ U, Set.EqOn (ψ ω).toFun NormShape.maxShape.toFun (Set.Icc (0 : ℝ) 1))
    [hS : S.IsArchimedeanNormalized] :
    (ξ.directSum η ψ).IsDominated :=
  hξ.directSum_of_measure_lt_top hη ψ U hU hfinU hψ (S.v_Ωinf_lt_top_of_isRCLike)

/-- Componentwise norm comparison controls the actual maximum sum. -/
theorem maxDirectSum_norm_le_exp_localDist_mul (ξ' : NormFamily S E) (η' : NormFamily S F)
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] (E × F)) :
    (ξ'.maxDirectSum η').norm ω z ≤
      Real.exp (ξ.localDist ξ' ω + η.localDist η' ω) * (ξ.maxDirectSum η).norm ω z := by
  rw [maxDirectSum_norm, maxDirectSum_norm, mul_max_of_nonneg _ _ (Real.exp_pos _).le]
  apply max_le_max
  · exact (ξ.norm_le_exp_localDist_mul ξ' ω _).trans
      (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (le_add_of_nonneg_right (η.localDist_nonneg η' ω)))
        (ξ.norm_nonneg ω _))
  · exact (η.norm_le_exp_localDist_mul η' ω _).trans
      (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (le_add_of_nonneg_left (ξ.localDist_nonneg ξ' ω)))
        (η.norm_nonneg ω _))

/-- Maximum direct sums have distance bounded by the sum of the component
distances, including zero-dimensional factors. -/
theorem localDist_maxDirectSum_le (ξ' : NormFamily S E) (η' : NormFamily S F) (ω : S.Ω) :
    (ξ.maxDirectSum η).localDist (ξ'.maxDirectSum η') ω ≤
      ξ.localDist ξ' ω + η.localDist η' ω := by
  apply ((ξ.maxDirectSum η).localDist_le_iff_norm_le (ξ'.maxDirectSum η') ω
    (add_nonneg (ξ.localDist_nonneg ξ' ω) (η.localDist_nonneg η' ω))).mpr
  intro z
  refine ⟨?_, ξ.maxDirectSum_norm_le_exp_localDist_mul η ξ' η' ω z⟩
  simpa only [localDist_comm] using ξ'.maxDirectSum_norm_le_exp_localDist_mul η' ξ η ω z

/-- Strong domination of the maximum sum follows by comparison with
actual dominated ultrametric-at-finite-place Hermitian basis norms. -/
theorem IsStronglyDominated.maxDirectSum {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsStronglyDominated) (hη : η.IsStronglyDominated)
    [hS : S.IsArchimedeanNormalized] :
    (ξ.maxDirectSum η).IsStronglyDominated := by
  let b := Module.finBasis K E
  let c := Module.finBasis K F
  let ξ₀ := ofBasisHermitian S E b
  let η₀ := ofBasisHermitian S F c
  have hfin := S.v_Ωinf_lt_top_of_isRCLike
  have hξ₀ : ξ₀.IsStronglyDominated :=
    ofBasisHermitian_isStronglyDominated_of_measure_lt_top b hfin
  have hη₀ : η₀.IsStronglyDominated :=
    ofBasisHermitian_isStronglyDominated_of_measure_lt_top c hfin
  have hmax : (ξ₀.maxDirectSum η₀).IsStronglyDominated :=
    ((ξ₀.maxDirectSum η₀).isStronglyDominated_iff_isDominated_of_ultrametric
      (hξ := ((ofBasisHermitian_isUltrametric b).maxDirectSum (ofBasisHermitian_isUltrametric c)))
).mpr (hξ₀.isDominated.maxDirectSum hη₀.isDominated hfin)
  have hdistξ := hξ₀.localDist hξ hfin
  have hdistη := hη₀.localDist hη hfin
  apply hmax.of_localDist
  exact (hdistξ.1.add hdistη.1).mono
    (Eventually.of_forall fun ω => ξ₀.localDist_maxDirectSum_le η₀ ξ η ω)

/-- The strong-domination clause of Proposition 4.1.19(4), for every
admissible profile supported away from the maximum on a set of finite measure. -/
theorem IsStronglyDominated.directSum {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsStronglyDominated) (hη : η.IsStronglyDominated) (ψ : S.Ω → NormShape)
    (U : Set S.Ω) (hU : MeasurableSet U) (hfinU : S.v U < ⊤)
    (hψ : ∀ ω ∉ U, Set.EqOn (ψ ω).toFun NormShape.maxShape.toFun (Set.Icc (0 : ℝ) 1))
    [hS : S.IsArchimedeanNormalized] :
    (ξ.directSum η ψ).IsStronglyDominated :=
  (hξ.maxDirectSum hη).of_localDist
    (ξ.localDist_maxDirectSum_directSum_hasIntegrableBounds η ψ U hU hfinU hψ).1

end ArakelovGeometry.NormFamily
