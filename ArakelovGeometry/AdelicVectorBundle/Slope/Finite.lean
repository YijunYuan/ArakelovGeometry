/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Determinant.Basic
public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic

import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Determinant.Bound
import ArakelovGeometry.AdelicVectorBundle.Dual.Map
import ArakelovGeometry.AdelicVectorBundle.NormFamily.BasisComparison
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Rational
import ArakelovGeometry.AdelicVectorBundle.Slope.Dual
import ArakelovGeometry.AdelicVectorBundle.Slope.Quotient
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Finiteness of the source extremal slopes

One integrable envelope for the actual rational dual basis bounds determinant
coordinates of every subspace. The intrinsic determinant discrepancy supplies
the Archimedean rank loss, and the proper product formula removes the nonzero
rational coefficient. No uniform subspace degree bound is assumed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace NormFamily

/-- For arbitrary norms, the completed determinant pairing equals the
product of the two actual determinant norms times their intrinsic discrepancy.
This includes the two scalar determinant lines in rank zero. -/
theorem norm_completedDeterminantPairing_eq_discrepancy_mul (ξ : NormFamily S E)
    (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E)))
    (t : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    ‖completedDeterminantPairing K (S.ϕ ω).Completion E z t‖ =
      ξ.determinantDiscrepancy ω *
        (ξ.determinant.norm ω t * ξ.dual.determinant.norm ω z) := by
  let t₀ := (1 : (S.ϕ ω).Completion) ⊗ₜ[K] determinantGenerator (K := K) (E := E)
  let z₀ := (1 : (S.ϕ ω).Completion) ⊗ₜ[K] dualDeterminantGenerator (K := K) (E := E)
  have ht₀ : t₀ ≠ 0 := by
    intro h
    have hp := completedDeterminantGenerator_pairing (S := S) (E := E) ω
    change completedDeterminantPairing K (S.ϕ ω).Completion E z₀ t₀ = 1 at hp
    rw [h, map_zero] at hp
    exact zero_ne_one hp
  have hz₀ : z₀ ≠ 0 := by
    intro h
    have hp := completedDeterminantGenerator_pairing (S := S) (E := E) ω
    change completedDeterminantPairing K (S.ϕ ω).Completion E z₀ t₀ = 1 at hp
    rw [h, map_zero, LinearMap.zero_apply] at hp
    exact zero_ne_one hp
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one
    (show Module.finrank (S.ϕ ω).Completion
        ((S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) = 1 by
      rw [Module.finrank_baseChange]; exact determinant_finrank) ht₀ t
  obtain ⟨b, hb⟩ := exists_smul_eq_of_finrank_eq_one
    (show Module.finrank (S.ϕ ω).Completion
        ((S.ϕ ω).Completion ⊗[K]
          (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E))) = 1 by
      rw [Module.finrank_baseChange]; exact determinant_finrank) hz₀ z
  have hp : completedDeterminantPairing K (S.ϕ ω).Completion E z t = b * a := by
    rw [← ha, ← hb]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, t₀, z₀,
      completedDeterminantGenerator_pairing, mul_one, mul_comm]
  rw [hp, norm_mul, ← ha, ← hb, ξ.determinant.norm_smul, ξ.dual.determinant.norm_smul]
  have hnonzero : ξ.determinant.norm ω t₀ * ξ.dual.determinant.norm ω z₀ ≠ 0 :=
    (mul_pos (ξ.determinant.norm_pos ω ht₀) (ξ.dual.determinant.norm_pos ω hz₀)).ne'
  change ‖b‖ * ‖a‖ = (ξ.determinant.norm ω t₀ * ξ.dual.determinant.norm ω z₀)⁻¹ * _
  symm
  calc
    _ = (‖a‖ * ‖b‖) * ((ξ.determinant.norm ω t₀ * ξ.dual.determinant.norm ω z₀)⁻¹ *
        (ξ.determinant.norm ω t₀ * ξ.dual.determinant.norm ω z₀)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hnonzero, mul_one, mul_comm]

/-- The sharp local discrepancy bound controls an actual dual-coordinate
wedge on every completed determinant vector. The finite-place factor is one,
even when the original vector norm is not ultrametric. -/
theorem norm_completedDeterminantPairing_dual_wedge_le (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized] (ω : S.Ω)
    (f : Fin (Module.finrank K (Module.Dual K E)) →
      (S.ϕ ω).Completion ⊗[K] Module.Dual K E)
    (t : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    ‖completedDeterminantPairing K (S.ϕ ω).Completion E
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion (Module.Dual K E) _).symm
          (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ f)) t‖ ≤
      Real.exp (S.Ωinf.indicator (fun _ ↦
        (Module.finrank K E : ℝ) / 2 * Real.log (Module.finrank K E)) ω) *
        ξ.determinant.norm ω t * ∏ i, ξ.dual.norm ω (f i) := by
  have hδ : ξ.determinantDiscrepancy ω ≤
      Real.exp (S.Ωinf.indicator (fun _ ↦
        (Module.finrank K E : ℝ) / 2 * Real.log (Module.finrank K E)) ω) := by
    rw [← Real.exp_log (ξ.determinantDiscrepancy_pos ω)]
    exact Real.exp_le_exp.mpr (ξ.log_determinantDiscrepancy_le_indicator ω)
  rw [ξ.norm_completedDeterminantPairing_eq_discrepancy_mul]
  calc
    _ ≤ Real.exp (S.Ωinf.indicator (fun _ ↦
        (Module.finrank K E : ℝ) / 2 * Real.log (Module.finrank K E)) ω) *
        (ξ.determinant.norm ω t * ∏ i, ξ.dual.norm ω (f i)) :=
      mul_le_mul hδ
        (mul_le_mul_of_nonneg_left (ξ.dual.determinant_norm_ιMulti_le ω f)
          (ξ.determinant.norm_nonneg ω t))
        (mul_nonneg (ξ.determinant.norm_nonneg ω t) (ξ.dual.determinant.norm_nonneg ω _))
        (Real.exp_pos _).le
    _ = _ := by ring

/-- One integrable envelope for a fixed ambient dual basis bounds all its
restrictions to all rational subspaces. This is obtained from domination,
not assumed as a uniform subspace degree estimate. -/
theorem IsDominated.exists_restricted_dual_basis_norm_bound (ξ : NormFamily S E)
    (b : Module.Basis (Fin (Module.finrank K E)) K E) (hd : ξ.IsDominated) :
    ∃ A : S.Ω → ℝ, Integrable A S.v ∧ (∀ ω, 0 ≤ A ω) ∧
      ∀ᵐ ω ∂S.v, ∀ (U : Submodule K E) (i : Fin (Module.finrank K E)),
        (ξ.restrict U).dual.norm ω
          ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] U.subtype.dualMap (b.coord i)) ≤
            Real.exp (A ω) := by
  obtain ⟨A, hA, hA0, hb⟩ :=
    IsUpperDominated.exists_basis_norm_bound ξ.dual b.dualBasis hd.2
  refine ⟨A, hA, hA0, ?_⟩
  filter_upwards [hb] with ω hω
  intro U i
  have h := ξ.pullback_dual_norm_le U.subtype U.subtype_injective ω
    ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] b.coord i)
  rw [LinearMap.baseChange_tmul] at h
  have hbi : b.dualBasis i = b.coord i := by
    ext x
    simp only [Module.Basis.dualBasis_apply, Module.Basis.coord_apply]
  exact h.trans (by simpa only [Module.Basis.baseChange_apply, hbi] using hω i)

end NormFamily

/-- The actual wedge of the ambient coordinate functionals restricted to
a subspace, with only the canonical equality of primal and dual ranks. -/
def restrictedCoordinateDualWedge
    (b : Module.Basis (Fin (Module.finrank K E)) K E) (U : Submodule K E)
    (s : Set.powersetCard (Fin (Module.finrank K E)) (Module.finrank K U)) :
    ⋀[K]^(Module.finrank K (Module.Dual K U)) (Module.Dual K U) :=
  _root_.exteriorPower.ιMulti K _ (fun i => U.subtype.dualMap
    (b.coord (Set.powersetCard.ofFinEmbEquiv.symm s
      (finCongr (Subspace.dual_finrank_eq (K := K) (V := U)) i))))

/-- Pairing a restricted coordinate wedge with a subspace determinant is
exactly the corresponding coordinate of its embedded ambient exterior vector. -/
theorem restrictedCoordinateDualWedge_pairing
    (b : Module.Basis (Fin (Module.finrank K E)) K E) (U : Submodule K E)
    (s : Set.powersetCard (Fin (Module.finrank K E)) (Module.finrank K U))
    (t : ⋀[K]^(Module.finrank K U) U) :
    determinantDualEquiv K U (restrictedCoordinateDualWedge b U s) t =
      (b.exteriorPower (Module.finrank K U)).coord s
        (_root_.exteriorPower.map (Module.finrank K U) U.subtype t) := by
  have h : determinantDualEquiv K U (restrictedCoordinateDualWedge b U s) =
      ((b.exteriorPower (Module.finrank K U)).coord s).comp
        (_root_.exteriorPower.map (Module.finrank K U) U.subtype) := by
    apply _root_.exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro x
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      determinantDualEquiv, LinearEquiv.trans_apply, restrictedCoordinateDualWedge,
      exteriorPowerDegreeEquiv_ιMulti, exteriorDualEquiv_apply,
      Equiv.apply_symm_apply, _root_.exteriorPower.pairingDual_ιMulti_ιMulti,
      _root_.exteriorPower.basis_coord, _root_.exteriorPower.map_apply_ιMulti,
      _root_.exteriorPower.ιMultiDual_apply_ιMulti, Function.comp_def,
      LinearMap.dualMap_apply]
  exact LinearMap.congr_fun h t

/-- A nonzero subspace determinant has a nonzero rational coordinate in
the exterior basis of any fixed ambient basis. The corresponding actual
restricted dual wedge has a nonzero pairing with it. -/
theorem exists_restrictedCoordinateDualWedge_pairing_ne_zero
    (b : Module.Basis (Fin (Module.finrank K E)) K E) (U : Submodule K E)
    (t : ⋀[K]^(Module.finrank K U) U) (ht : t ≠ 0) :
    ∃ s : Set.powersetCard (Fin (Module.finrank K E)) (Module.finrank K U),
      determinantDualEquiv K U (restrictedCoordinateDualWedge b U s) t ≠ 0 := by
  have hem : _root_.exteriorPower.map (Module.finrank K U) U.subtype t ≠ 0 := by
    intro h
    exact ht ((_root_.exteriorPower.map_injective_field U.subtype_injective)
      (h.trans (map_zero _).symm))
  have hre : (b.exteriorPower (Module.finrank K U)).repr
      (_root_.exteriorPower.map (Module.finrank K U) U.subtype t) ≠ 0 := by
    intro h
    exact hem ((b.exteriorPower (Module.finrank K U)).repr.injective
      (h.trans (map_zero _).symm))
  obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hre
  refine ⟨s, ?_⟩
  rw [restrictedCoordinateDualWedge_pairing]
  simpa only [Module.Basis.coord_apply, Finsupp.zero_apply] using hs

namespace NormFamily

/-- A common bound on actual restricted coordinate functionals gives the
rank power bound on their genuine dual determinant wedge. -/
theorem restrictedCoordinateDualWedge_norm_le (ξ : NormFamily S E)
    (b : Module.Basis (Fin (Module.finrank K E)) K E) (U : Submodule K E)
    (s : Set.powersetCard (Fin (Module.finrank K E)) (Module.finrank K U))
    (ω : S.Ω) (A : ℝ)
    (hb : ∀ i, (ξ.restrict U).dual.norm ω
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] U.subtype.dualMap (b.coord i)) ≤ Real.exp A) :
    (ξ.restrict U).dual.determinant.norm ω
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] restrictedCoordinateDualWedge b U s) ≤
        Real.exp ((Module.finrank K U : ℝ) * A) := by
  let f (i : Fin (Module.finrank K (Module.Dual K U))) := U.subtype.dualMap
    (b.coord (Set.powersetCard.ofFinEmbEquiv.symm s
      (finCongr (Subspace.dual_finrank_eq (K := K) (V := U)) i)))
  have he := exteriorBaseChangeEquiv_symm_ιMulti_tmul K (S.ϕ ω).Completion
    (Module.Dual K U) (Module.finrank K (Module.Dual K U)) (fun _ ↦ 1) f
  simp only [Finset.prod_const_one] at he
  have h := (ξ.restrict U).dual.determinant_norm_ιMulti_le ω
    (fun i ↦ (1 : (S.ϕ ω).Completion) ⊗ₜ[K] f i)
  rw [he] at h
  change (ξ.restrict U).dual.determinant.norm ω
    ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] restrictedCoordinateDualWedge b U s) ≤ _ at h
  refine h.trans ?_
  calc
    (∏ i, (ξ.restrict U).dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] f i)) ≤
        ∏ _ : Fin (Module.finrank K (Module.Dual K U)), Real.exp A :=
      Finset.prod_le_prod₀ (fun _ _ ↦ (ξ.restrict U).dual.norm_nonneg ω _)
        (fun i _ ↦ hb _)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_nat_mul, Subspace.dual_finrank_eq]

/-- A nonzero rational determinant coordinate gives the local logarithmic
lower bound on the actual restricted determinant norm. Its rank loss is
supported on infinity and uses the intrinsic determinant discrepancy. -/
theorem log_absValue_coordinate_le_logNorm_restrict_determinant (ξ : NormFamily S E)
    (b : Module.Basis (Fin (Module.finrank K E)) K E) (U : Submodule K E)
    (s : Set.powersetCard (Fin (Module.finrank K E)) (Module.finrank K U))
    (t : ⋀[K]^(Module.finrank K U) U) (ht : t ≠ 0)
    (hα : determinantDualEquiv K U (restrictedCoordinateDualWedge b U s) t ≠ 0)
    [hN : S.IsArchimedeanNormalized]
    (ω : S.Ω) (A : ℝ)
    (hb : ∀ i, (ξ.restrict U).dual.norm ω
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] U.subtype.dualMap (b.coord i)) ≤ Real.exp A) :
    Real.log (S.ϕ ω (determinantDualEquiv K U (restrictedCoordinateDualWedge b U s) t)) ≤
      (ξ.restrict U).determinant.logNorm t ω + (Module.finrank K U : ℝ) * A +
        S.Ωinf.indicator (fun _ ↦
          (Module.finrank K U : ℝ) / 2 * Real.log (Module.finrank K U)) ω := by
  let η := ξ.restrict U
  let α := determinantDualEquiv K U (restrictedCoordinateDualWedge b U s) t
  let R := S.Ωinf.indicator (fun _ ↦
    (Module.finrank K U : ℝ) / 2 * Real.log (Module.finrank K U)) ω
  have hpair : ‖completedDeterminantPairing K (S.ϕ ω).Completion U
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] restrictedCoordinateDualWedge b U s)
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] t)‖ = S.ϕ ω α := by
    change ‖dualBaseChangeEquiv K (S.ϕ ω).Completion _
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K]
        determinantDualEquiv K U (restrictedCoordinateDualWedge b U s))
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] t)‖ = S.ϕ ω α
    simp only [dualBaseChangeEquiv_tmul_apply_tmul, one_mul,
      S.norm_algebraMap_eq_absValue, α]
  have hδ : η.determinantDiscrepancy ω ≤ Real.exp R := by
    rw [← Real.exp_log (η.determinantDiscrepancy_pos ω)]
    exact Real.exp_le_exp.mpr (η.log_determinantDiscrepancy_le_indicator ω)
  have hprod := mul_le_mul hδ (ξ.restrictedCoordinateDualWedge_norm_le b U s ω A hb)
    (η.dual.determinant.norm_nonneg ω _) (Real.exp_pos R).le
  have hnorm : S.ϕ ω α ≤ Real.exp (R + (Module.finrank K U : ℝ) * A) *
      η.determinant.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] t) := by
    rw [← hpair, η.norm_completedDeterminantPairing_eq_discrepancy_mul]
    have h := mul_le_mul_of_nonneg_right hprod
      (η.determinant.norm_nonneg ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] t))
    rw [Real.exp_add]
    nlinarith
  have hl := Real.log_le_log ((S.ϕ ω).pos hα) hnorm
  rw [Real.log_mul (Real.exp_ne_zero _) (η.determinant.norm_rational_pos ω ht).ne',
    Real.log_exp] at hl
  change Real.log (S.ϕ ω α) ≤ η.determinant.logNorm t ω + _ + R
  dsimp only [logNorm] at hl ⊢
  linarith

end NormFamily

namespace AdelicVectorBundle

variable [S.IsProper]

/-- Integrating the actual determinant coordinate bound removes its
nonzero rational coefficient by properness. The only error is the accepted
sharp Archimedean determinant discrepancy, in every subspace rank. -/
theorem degree_restrict_le_of_dual_basis_norm_bound (V : AdelicVectorBundle S)
    (b : Module.Basis (Fin (Module.finrank K V)) K V) (A : S.Ω → ℝ)
    (hA : Integrable A S.v)
    (hb : ∀ᵐ ω ∂S.v, ∀ (U : Submodule K V) (i : Fin (Module.finrank K V)),
      (V.toNormFamily.restrict U).dual.norm ω
        ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] U.subtype.dualMap (b.coord i)) ≤ Real.exp (A ω))
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (U : Submodule K V) :
    (V.restrictOfNormMeasurability U).degree ≤
      (Module.finrank K U : ℝ) * (∫ ω, A ω ∂S.v) +
        (Module.finrank K U : ℝ) / 2 * Real.log (Module.finrank K U) *
          (S.v S.Ωinf).toReal := by
  let W := V.restrictOfNormMeasurability U
  let t := determinantGenerator (K := K) (E := U)
  have ht : t ≠ 0 := determinantGenerator_ne_zero
  obtain ⟨s, hs⟩ := exists_restrictedCoordinateDualWedge_pairing_ne_zero b U t ht
  let α := determinantDualEquiv K U (restrictedCoordinateDualWedge b U s) t
  have hα : α ≠ 0 := hs
  let R := S.Ωinf.indicator (fun _ ↦
    (Module.finrank K U : ℝ) / 2 * Real.log (Module.finrank K U))
  have hR : Integrable R S.v :=
    (integrable_indicator_iff S.measurableSet_Ωinf).mpr
      (integrableOn_const (S.v_Ωinf_lt_top_of_isRCLike).ne)
  have hf : Integrable (W.toNormFamily.determinant.logNorm t) S.v :=
    (W.determinantOfNormMeasurability).integrable_logNorm t
  have hlocal : ∀ᵐ ω ∂S.v, Real.log (S.ϕ ω α) ≤
      W.toNormFamily.determinant.logNorm t ω + (Module.finrank K U : ℝ) * A ω + R ω := by
    filter_upwards [hb] with ω hω
    exact V.toNormFamily.log_absValue_coordinate_le_logNorm_restrict_determinant
      b U s t ht hs ω (A ω) (hω U)
  have hi := integral_mono_ae (S.integrable_log α hα)
    ((hf.add (hA.const_mul (Module.finrank K U : ℝ))).add hR) hlocal
  simp only [Pi.add_apply] at hi
  have hsum := integral_add (hf.add (hA.const_mul (Module.finrank K U : ℝ))) hR
  simp only [Pi.add_apply] at hsum
  rw [hsum, integral_add hf (hA.const_mul (Module.finrank K U : ℝ)), integral_const_mul,
    AdelicStructure.IsProper.product_formula α hα] at hi
  rw [W.degree_eq_neg_integral ⟨t, ht⟩]
  dsimp only [R] at hi
  rw [integral_indicator_const _ S.measurableSet_Ωinf] at hi
  change 0 ≤ (∫ ω, W.toNormFamily.determinant.logNorm t ω ∂S.v) +
    (Module.finrank K U : ℝ) * (∫ ω, A ω ∂S.v) +
      (S.v S.Ωinf).toReal * ((Module.finrank K U : ℝ) / 2 *
        Real.log (Module.finrank K U)) at hi
  linarith

/-- Actual dual-basis domination and the proper product formula give a
single real upper bound for all restricted mean slopes. Equivalently the
restricted degrees are bounded by rank times one real constant. -/
theorem exists_degree_restrict_le_rank_mul (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    ∃ C : ℝ, ∀ U : Submodule K V,
      (V.restrictOfNormMeasurability U).degree ≤ (Module.finrank K U : ℝ) * C := by
  let b := Module.finBasis K V
  obtain ⟨A, hA, _, hb⟩ :=
    NormFamily.IsDominated.exists_restricted_dual_basis_norm_bound V.toNormFamily b V.isDominated
  let C := (∫ ω, A ω ∂S.v) + (1 / 2 : ℝ) * Real.log (Module.finrank K V) *
    (S.v S.Ωinf).toReal
  refine ⟨C, fun U ↦ ?_⟩
  have hdeg := V.degree_restrict_le_of_dual_basis_norm_bound b A hA hb U
  by_cases hn : Module.finrank K U = 0
  · simpa only [hn, Nat.cast_zero, zero_mul, zero_div, add_zero] using hdeg
  · have hlog : Real.log (Module.finrank K U : ℝ) ≤ Real.log (Module.finrank K V) :=
      Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
        (Nat.cast_le.mpr U.finrank_le)
    have hl := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog (div_nonneg (Nat.cast_nonneg (Module.finrank K U))
        (by norm_num : (0 : ℝ) ≤ 2)))
      (ENNReal.toReal_nonneg : 0 ≤ (S.v S.Ωinf).toReal)
    refine hdeg.trans ?_
    dsimp only [C]
    nlinarith

/-- Source Proposition 4.3.30: the maximal slope is strictly below `⊤`.
This also includes rank zero, where the maximal slope is `⊥`. -/
theorem maximalSlope_lt_top (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    V.maximalSlope < ⊤ := by
  obtain ⟨C, hC⟩ := V.exists_degree_restrict_le_rank_mul
  have hmax : V.maximalSlope ≤ (C : EReal) := by
    apply V.maximalSlope_le
    intro U hU
    apply EReal.coe_le_coe_iff.mpr
    have hd := hC U
    rw [(V.restrictOfNormMeasurability U).degree_eq_rank_mul_slope] at hd
    exact (mul_le_mul_iff_right₀ (Nat.cast_pos.mpr hU : (0 : ℝ) < Module.finrank K U)).mp hd
  exact hmax.trans_lt (EReal.coe_lt_top C)

/-- Source Proposition 4.3.30: the source minimal slope is strictly above
`⊥` in positive rank. Maximal-slope finiteness of the actual dual is now
proved, discharging the explicit premise of Proposition 4.3.25. -/
theorem bot_lt_minimalSlope (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (hr : 0 < Module.finrank K V) : ⊥ < V.minimalSlope :=
  V.bot_lt_minimalSlope_of_maximalSlope_dual_lt_top hr
    ((V.dualOfNormMeasurability).maximalSlope_lt_top)

/-- The positive-rank maximal slope is a finite real number, after both
extended endpoints have been excluded by proved bounds. -/
theorem exists_maximalSlope_eq_coe (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (hr : 0 < Module.finrank K V) :
    ∃ c : ℝ, V.maximalSlope = (c : EReal) := by
  lift V.maximalSlope to ℝ using
    ⟨(V.maximalSlope_lt_top).ne, (V.bot_lt_maximalSlope hr).ne'⟩ with c
  exact ⟨c, rfl⟩

/-- The positive-rank minimal slope is a finite real number. Its upper
endpoint is excluded by the proved actual quotient-mean formula. -/
theorem exists_minimalSlope_eq_coe (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (hr : 0 < Module.finrank K V) :
    ∃ c : ℝ, V.minimalSlope = (c : EReal) := by
  lift V.minimalSlope to ℝ using
    ⟨(V.minimalSlope_lt_top hr).ne, (V.bot_lt_minimalSlope hr).ne'⟩ with c
  exact ⟨c, rfl⟩

/-- The finiteness producer discharges the source's explicit premise in
Proposition 4.3.25 for every actual positive-rank adelic bundle. -/
theorem minimalSlope_add_maximalSlope_dual_nonneg (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (hr : 0 < Module.finrank K V) :
    0 ≤ V.minimalSlope + (V.dualOfNormMeasurability).maximalSlope :=
  V.minimalSlope_add_maximalSlope_dual_nonneg_of_lt_top hr
    ((V.dualOfNormMeasurability).maximalSlope_lt_top)

end AdelicVectorBundle

end

end ArakelovGeometry
