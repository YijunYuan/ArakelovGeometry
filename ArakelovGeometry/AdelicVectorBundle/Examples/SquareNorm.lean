/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicStructure.RationalNormalization
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Ordered
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
public import ArakelovGeometry.Analysis.Determinant.ExactSequence

import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicVectorBundle.Degree.Height
import ArakelovGeometry.AdelicVectorBundle.Dual.Map
import ArakelovGeometry.AdelicVectorBundle.NormFamily.BasisComparison
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Line
import ArakelovGeometry.AdelicVectorBundle.Slope.Quotient
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# The square norm over the source-normalized rational curve

The bundle uses the existing completed coordinate-maximum norm on `ℚ²`.
Both measurability clauses, domination and strong adelicity are produced
on the actual prime-counting and single-real curve.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle.Examples

noncomputable section

open AdelicStructure

/-- The standard rational coordinate plane. -/
abbrev RationalPlane := Fin 2 → ℚ

/-- Its actual standard coordinate basis. -/
def squareBasis : Module.Basis (Fin 2) ℚ RationalPlane := Pi.basisFun ℚ (Fin 2)

/-- The archimedean locus of the rational adelic curve has finite measure. -/
theorem squareFiniteInfiniteMeasure :
    rationalAdelicStructure.v rationalAdelicStructure.Ωinf < ⊤ := by
  rw [rationalAdelicStructure_v_Ωinf]
  exact ENNReal.one_lt_top

/-- The actual coordinate-maximum adelic bundle at every rational place. -/
abbrev squareNorm : AdelicVectorBundle rationalAdelicStructure where
  carrier := RationalPlane
  toNormFamily := NormFamily.ofBasis rationalAdelicStructure RationalPlane squareBasis
  toIsAdelic := {
    isMeasurable := NormFamily.ofBasis_isMeasurable squareBasis
    dual_isMeasurable :=
      (NormFamily.ofBasis rationalAdelicStructure RationalPlane
        squareBasis).dual.isMeasurable_of_discrete
    isDominated := by
      exact NormFamily.ofBasis_isDominated_of_measure_lt_top squareBasis squareFiniteInfiniteMeasure
  }

@[simp]
theorem squareNorm_toNormFamily : squareNorm.toNormFamily =
    NormFamily.ofBasis rationalAdelicStructure RationalPlane squareBasis := rfl

/-- The norm is the maximum norm of the actual completed coordinates. -/
theorem squareNorm_norm_coordinates (ω : rationalAdelicStructure.Ω)
    (x : (rationalAdelicStructure.ϕ ω).Completion ⊗[ℚ] RationalPlane) :
    squareNorm.norm ω x =
      ‖(squareBasis.baseChange (rationalAdelicStructure.ϕ ω).Completion).equivFun x‖ :=
  NormFamily.ofBasis_norm rationalAdelicStructure RationalPlane squareBasis ω x

/-- Rational evaluations use precisely the original absolute values. -/
theorem squareNorm_norm_rational (ω : rationalAdelicStructure.Ω) (x : RationalPlane) :
    squareNorm.norm ω ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ] x) =
      ‖fun i : Fin 2 ↦ rationalAdelicStructure.ϕ ω (x i)‖ := by
  change (NormFamily.ofBasis rationalAdelicStructure RationalPlane squareBasis).norm ω _ = _
  rw [NormFamily.ofBasis_norm_rational]
  rfl

/-- The true completed maximum family has integrably bounded distance
to the canonical mixed family. -/
theorem squareNorm_localDist_mixed_hasIntegrableBounds :
    HasIntegrableBounds (squareNorm.toNormFamily.localDist
      (NormFamily.ofBasisMixed rationalAdelicStructure RationalPlane squareBasis))
      rationalAdelicStructure.v := by
  classical
  constructor
  · refine ⟨rationalAdelicStructure.Ωinf.indicator
      (fun _ ↦ Real.log (Fintype.card (Fin 2) : ℝ)), ?_, ?_⟩
    · exact (integrable_indicator_iff rationalAdelicStructure.measurableSet_Ωinf).mpr
        (integrableOn_const squareFiniteInfiniteMeasure.ne)
    · exact Filter.Eventually.of_forall
        (NormFamily.ofBasis_localDist_ofBasisMixed_le squareBasis)
  · exact ⟨0, integrable_zero _ _ _, Filter.Eventually.of_forall
      (squareNorm.toNormFamily.localDist_nonneg _)⟩

/-- Strong adelicity belongs to the actual square bundle, including its bidual. -/
theorem squareNorm_isStronglyAdelic : squareNorm.IsStronglyAdelic :=
  (NormFamily.isStronglyDominated_iff_localDist_ofBasisMixed_of_measure_lt_top
    squareBasis squareNorm.toNormFamily squareFiniteInfiniteMeasure).mpr
      squareNorm_localDist_mixed_hasIntegrableBounds

@[simp]
theorem squareNorm_finrank : Module.finrank ℚ RationalPlane = 2 := by
  simp only [RationalPlane, Module.finrank_pi, Fintype.card_fin]

private theorem squareCoordinateNorm {k : Type*} [SeminormedAddCommGroup k]
    (x : Fin 2 → k) : ‖x‖ = max ‖x 0‖ ‖x 1‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).mpr
    intro i
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (norm_le_pi_norm x 0) (norm_le_pi_norm x 1)

/-- The completed norm is literally the maximum of its two completed coordinates. -/
theorem squareNorm_norm_max (ω : rationalAdelicStructure.Ω)
    (x : (rationalAdelicStructure.ϕ ω).Completion ⊗[ℚ] RationalPlane) :
    squareNorm.norm ω x = max
      ‖(squareBasis.baseChange (rationalAdelicStructure.ϕ ω).Completion).equivFun x 0‖
      ‖(squareBasis.baseChange (rationalAdelicStructure.ϕ ω).Completion).equivFun x 1‖ := by
  rw [squareNorm_norm_coordinates, squareCoordinateNorm]

/-- The source coordinate maximum on every rational vector and every place. -/
theorem squareNorm_norm_max_rational (ω : rationalAdelicStructure.Ω) (x : RationalPlane) :
    squareNorm.norm ω ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ] x) =
      max (rationalAdelicStructure.ϕ ω (x 0)) (rationalAdelicStructure.ϕ ω (x 1)) := by
  rw [squareNorm_norm_rational, squareCoordinateNorm]
  simp only [Real.norm_eq_abs, abs_of_nonneg (rationalAdelicStructure.ϕ ω |>.nonneg _)]

/-- At the unique real place this is the original square norm. -/
theorem squareNorm_norm_infinite_rational (x : RationalPlane) :
    squareNorm.norm (Sum.inr ())
      ((1 : (rationalAdelicStructure.ϕ (Sum.inr ())).Completion) ⊗ₜ[ℚ] x) =
        max |(x 0 : ℝ)| |(x 1 : ℝ)| := by
  rw [squareNorm_norm_max_rational]
  change max (Rat.AbsoluteValue.real (x 0)) (Rat.AbsoluteValue.real (x 1)) = _
  rw [Rat.AbsoluteValue.real_eq_abs, Rat.AbsoluteValue.real_eq_abs]
  simp only [Rat.cast_abs]

/-- Every finite completed fibre retains the actual normalized rational prime norm. -/
theorem squareNorm_norm_prime_rational (p : Nat.Primes) (x : RationalPlane) :
    squareNorm.norm (Sum.inl p)
      ((1 : (rationalAdelicStructure.ϕ (Sum.inl p)).Completion) ⊗ₜ[ℚ] x) =
        max (AdelicCurve.RationalFunction.rationalPadicAbv p (x 0))
          (AdelicCurve.RationalFunction.rationalPadicAbv p (x 1)) :=
  squareNorm_norm_max_rational _ x

/-- The standard basis with the actual determinant's rank index. -/
def squareDetBasis : Module.Basis (Fin (Module.finrank ℚ RationalPlane)) ℚ RationalPlane :=
  squareBasis.reindex (finCongr squareNorm_finrank.symm)

/-- The standard generator of the actual rational determinant line. -/
def squareDetGenerator : ⋀[ℚ]^(Module.finrank ℚ RationalPlane) RationalPlane :=
  _root_.exteriorPower.ιMulti ℚ (Module.finrank ℚ RationalPlane) squareDetBasis

private theorem squareDetBasis_baseChange (ω : rationalAdelicStructure.Ω) :
    squareDetBasis.baseChange (rationalAdelicStructure.ϕ ω).Completion =
      (squareBasis.baseChange (rationalAdelicStructure.ϕ ω).Completion).reindex
        (finCongr squareNorm_finrank.symm) := by
  ext i
  simp only [Module.Basis.baseChange_apply, Module.Basis.reindex_apply, squareDetBasis]

/-- The canonical scalar coordinate of the actual completed determinant line. -/
def squareCompletedDetCoordinate (ω : rationalAdelicStructure.Ω) :
    ((rationalAdelicStructure.ϕ ω).Completion ⊗[ℚ]
      (⋀[ℚ]^(Module.finrank ℚ RationalPlane) RationalPlane)) ≃ₗ[
        (rationalAdelicStructure.ϕ ω).Completion] (rationalAdelicStructure.ϕ ω).Completion :=
  (exteriorBaseChangeEquiv ℚ (rationalAdelicStructure.ϕ ω).Completion RationalPlane _).trans
    (determinantCoordinateEquiv
      (squareDetBasis.baseChange (rationalAdelicStructure.ϕ ω).Completion))

@[simp]
theorem squareCompletedDetCoordinate_generator (ω : rationalAdelicStructure.Ω) :
    squareCompletedDetCoordinate ω
      ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ] squareDetGenerator) = 1 := by
  change determinantCoordinateEquiv
    (squareDetBasis.baseChange (rationalAdelicStructure.ϕ ω).Completion)
      (exteriorBaseChangeEquiv ℚ (rationalAdelicStructure.ϕ ω).Completion RationalPlane _
        (1 ⊗ₜ[ℚ] squareDetGenerator)) = 1
  rw [squareDetGenerator, exteriorBaseChangeEquiv_tmul_ιMulti, one_smul]
  have he : (fun i ↦ (1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ]
      squareDetBasis i) = squareDetBasis.baseChange
        (rationalAdelicStructure.ϕ ω).Completion := by
    funext i
    exact (Module.Basis.baseChange_apply _ _ _).symm
  rw [he, determinantCoordinateEquiv_ιMulti, Module.Basis.det_self]

private theorem squareCompletedDetFormula (ω : rationalAdelicStructure.Ω)
    (x : Fin (Module.finrank ℚ RationalPlane) →
      (rationalAdelicStructure.ϕ ω).Completion ⊗[ℚ] RationalPlane) :
    (squareDetBasis.baseChange (rationalAdelicStructure.ϕ ω).Completion).det x =
      let e := finCongr squareNorm_finrank.symm
      let c := (squareBasis.baseChange (rationalAdelicStructure.ϕ ω).Completion).equivFun
      c (x (e 0)) 0 * c (x (e 1)) 1 - c (x (e 1)) 0 * c (x (e 0)) 1 := by
  rw [squareDetBasis_baseChange, Module.Basis.det_reindex, Module.Basis.det_apply,
    Matrix.det_fin_two]
  simp only [Module.Basis.toMatrix_apply, Module.Basis.equivFun_apply, Function.comp_apply]

/-- Every actual completed pair satisfies the real determinant bound with constant two. -/
theorem squareCompletedDet_norm_le_two (ω : rationalAdelicStructure.Ω)
    (x : Fin (Module.finrank ℚ RationalPlane) →
      (rationalAdelicStructure.ϕ ω).Completion ⊗[ℚ] RationalPlane) :
    ‖(squareDetBasis.baseChange (rationalAdelicStructure.ϕ ω).Completion).det x‖ ≤
      2 * ∏ i, squareNorm.norm ω (x i) := by
  let e := finCongr squareNorm_finrank.symm
  let c := (squareBasis.baseChange (rationalAdelicStructure.ϕ ω).Completion).equivFun
  have hc (i : Fin 2) (j : Fin 2) : ‖c (x (e i)) j‖ ≤ squareNorm.norm ω (x (e i)) := by
    rw [squareNorm_norm_coordinates]
    exact norm_le_pi_norm _ _
  have h01 := mul_le_mul (hc 0 0) (hc 1 1) (norm_nonneg _)
    (squareNorm.toNormFamily.norm_nonneg ω _)
  have h10 := mul_le_mul (hc 1 0) (hc 0 1) (norm_nonneg _)
    (squareNorm.toNormFamily.norm_nonneg ω _)
  rw [squareCompletedDetFormula]
  have hn := norm_sub_le (c (x (e 0)) 0 * c (x (e 1)) 1)
    (c (x (e 1)) 0 * c (x (e 0)) 1)
  simp only [norm_mul] at hn
  have hp : (∏ i, squareNorm.norm ω (x i)) =
      squareNorm.norm ω (x (e 0)) * squareNorm.norm ω (x (e 1)) := by
    rw [← e.prod_comp (fun i ↦ squareNorm.norm ω (x i)), Fin.prod_univ_two]
  rw [hp]
  dsimp only at hn ⊢
  nlinarith

/-- At every actual finite place the determinant constant is one. -/
theorem squareCompletedDet_norm_le_finite (ω : rationalAdelicStructure.Ω)
    (hω : ω ∈ rationalAdelicStructure.Ωfin)
    (x : Fin (Module.finrank ℚ RationalPlane) →
      (rationalAdelicStructure.ϕ ω).Completion ⊗[ℚ] RationalPlane) :
    ‖(squareDetBasis.baseChange (rationalAdelicStructure.ϕ ω).Completion).det x‖ ≤
      ∏ i, squareNorm.norm ω (x i) := by
  let e := finCongr squareNorm_finrank.symm
  let c := (squareBasis.baseChange (rationalAdelicStructure.ϕ ω).Completion).equivFun
  have hc (i : Fin 2) (j : Fin 2) : ‖c (x (e i)) j‖ ≤ squareNorm.norm ω (x (e i)) := by
    rw [squareNorm_norm_coordinates]
    exact norm_le_pi_norm _ _
  have h01 := mul_le_mul (hc 0 0) (hc 1 1) (norm_nonneg _)
    (squareNorm.toNormFamily.norm_nonneg ω _)
  have h10 := mul_le_mul (hc 1 0) (hc 0 1) (norm_nonneg _)
    (squareNorm.toNormFamily.norm_nonneg ω _)
  rw [squareCompletedDetFormula]
  have hn := rationalAdelicStructure.norm_add_le_max_of_finite ω hω
    (c (x (e 0)) 0 * c (x (e 1)) 1) (-(c (x (e 1)) 0 * c (x (e 0)) 1))
  simp only [norm_neg, norm_mul, ← sub_eq_add_neg] at hn
  have hp : (∏ i, squareNorm.norm ω (x i)) =
      squareNorm.norm ω (x (e 0)) * squareNorm.norm ω (x (e 1)) := by
    rw [← e.prod_comp (fun i ↦ squareNorm.norm ω (x i)), Fin.prod_univ_two]
  rw [hp]
  exact hn.trans (max_le h01 (by simpa only [mul_comm] using h10))

private theorem squareCompletedDetCoordinate_norm_le_of_bound
    (ω : rationalAdelicStructure.Ω) (C : ℝ) (hC : 0 < C)
    (hdet : ∀ x : Fin (Module.finrank ℚ RationalPlane) →
      (rationalAdelicStructure.ϕ ω).Completion ⊗[ℚ] RationalPlane,
      ‖(squareDetBasis.baseChange (rationalAdelicStructure.ϕ ω).Completion).det x‖ ≤
        C * ∏ i, squareNorm.norm ω (x i))
    (z : (rationalAdelicStructure.ϕ ω).Completion ⊗[ℚ]
      (⋀[ℚ]^(Module.finrank ℚ RationalPlane) RationalPlane)) :
    ‖squareCompletedDetCoordinate ω z‖ ≤ C * squareNorm.toNormFamily.determinant.norm ω z := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨x, hx, hn⟩ := squareNorm.toNormFamily.exists_determinant_ιMulti_norm_lt
    (by rw [squareNorm_finrank]; norm_num) ω z (div_pos hε hC)
  have he : squareCompletedDetCoordinate ω
      ((exteriorBaseChangeEquiv ℚ (rationalAdelicStructure.ϕ ω).Completion RationalPlane _).symm
        (_root_.exteriorPower.ιMulti (rationalAdelicStructure.ϕ ω).Completion _ x)) =
      (squareDetBasis.baseChange (rationalAdelicStructure.ϕ ω).Completion).det x := by
    change determinantCoordinateEquiv
      (squareDetBasis.baseChange (rationalAdelicStructure.ϕ ω).Completion)
        (exteriorBaseChangeEquiv ℚ (rationalAdelicStructure.ϕ ω).Completion RationalPlane _
          ((exteriorBaseChangeEquiv ℚ (rationalAdelicStructure.ϕ ω).Completion
            RationalPlane _).symm _)) = _
    rw [LinearEquiv.apply_symm_apply, determinantCoordinateEquiv_ιMulti]
  have hb := hdet x
  rw [← he, hx] at hb
  have hn' := mul_lt_mul_of_pos_left hn hC
  rw [mul_add, mul_div_cancel₀ _ hC.ne'] at hn'
  exact hb.trans hn'.le

/-- The factor-two bound applies to every vector of the actual determinant line. -/
theorem squareCompletedDetCoordinate_norm_le_two (ω : rationalAdelicStructure.Ω)
    (z : (rationalAdelicStructure.ϕ ω).Completion ⊗[ℚ]
      (⋀[ℚ]^(Module.finrank ℚ RationalPlane) RationalPlane)) :
    ‖squareCompletedDetCoordinate ω z‖ ≤ 2 * squareNorm.toNormFamily.determinant.norm ω z :=
  squareCompletedDetCoordinate_norm_le_of_bound ω 2 (by norm_num)
    (squareCompletedDet_norm_le_two ω) z

/-- The actual finite determinant coordinate is contractive on all completed vectors. -/
theorem squareCompletedDetCoordinate_norm_le_finite (ω : rationalAdelicStructure.Ω)
    (hω : ω ∈ rationalAdelicStructure.Ωfin)
    (z : (rationalAdelicStructure.ϕ ω).Completion ⊗[ℚ]
      (⋀[ℚ]^(Module.finrank ℚ RationalPlane) RationalPlane)) :
    ‖squareCompletedDetCoordinate ω z‖ ≤ squareNorm.toNormFamily.determinant.norm ω z := by
  simpa only [one_mul] using squareCompletedDetCoordinate_norm_le_of_bound ω 1 zero_lt_one
    (fun x ↦ by simpa only [one_mul] using squareCompletedDet_norm_le_finite ω hω x) z

/-- The standard completed basis wedge is the canonical rational determinant generator. -/
theorem squareDetBasis_completed_wedge (ω : rationalAdelicStructure.Ω) :
    (exteriorBaseChangeEquiv ℚ (rationalAdelicStructure.ϕ ω).Completion RationalPlane _).symm
      (_root_.exteriorPower.ιMulti (rationalAdelicStructure.ϕ ω).Completion _
        (squareDetBasis.baseChange (rationalAdelicStructure.ϕ ω).Completion)) =
      (1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ] squareDetGenerator := by
  apply (exteriorBaseChangeEquiv ℚ (rationalAdelicStructure.ϕ ω).Completion
    RationalPlane _).injective
  rw [LinearEquiv.apply_symm_apply, squareDetGenerator,
    exteriorBaseChangeEquiv_tmul_ιMulti, one_smul]
  congr 1
  funext i
  exact Module.Basis.baseChange_apply _ _ _

/-- The actual finite determinant generator has norm one. -/
theorem squareNorm_determinant_norm_generator_finite (ω : rationalAdelicStructure.Ω)
    (hω : ω ∈ rationalAdelicStructure.Ωfin) :
    squareNorm.toNormFamily.determinant.norm ω
      ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ] squareDetGenerator) = 1 := by
  apply le_antisymm
  · have h := squareNorm.toNormFamily.determinant_norm_ιMulti_le ω
      (squareDetBasis.baseChange (rationalAdelicStructure.ϕ ω).Completion)
    rw [squareDetBasis_completed_wedge] at h
    have hn (i : Fin (Module.finrank ℚ RationalPlane)) :
        squareNorm.norm ω
          (squareDetBasis.baseChange (rationalAdelicStructure.ϕ ω).Completion i) = 1 := by
      rw [squareDetBasis_baseChange, Module.Basis.reindex_apply,
        Module.Basis.baseChange_apply]
      change (NormFamily.ofBasis rationalAdelicStructure RationalPlane squareBasis).norm ω _ = 1
      simpa only [norm_one] using NormFamily.ofBasis_norm_tmul_basis
        rationalAdelicStructure RationalPlane squareBasis ω 1 _
    simpa only [hn, Finset.prod_const_one] using h
  · have h := squareCompletedDetCoordinate_norm_le_finite ω hω
      ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ] squareDetGenerator)
    have he := congrArg (fun a : (rationalAdelicStructure.ϕ ω).Completion ↦ ‖a‖)
      (squareCompletedDetCoordinate_generator ω)
    calc
      1 = ‖squareCompletedDetCoordinate ω (1 ⊗ₜ[ℚ] squareDetGenerator)‖ := by
        exact (he.trans (norm_one : ‖(1 :
          (rationalAdelicStructure.ϕ ω).Completion)‖ = 1)).symm
      _ ≤ _ := h

/-- The actual completed pair with coordinates `(1,1)` and `(1,-1)`
has unit norms and determinant minus twice the standard generator. -/
theorem exists_squareCompletedDet_witness (ω : rationalAdelicStructure.Ω) :
    ∃ x : Fin (Module.finrank ℚ RationalPlane) →
      (rationalAdelicStructure.ϕ ω).Completion ⊗[ℚ] RationalPlane,
      (∀ i, squareNorm.norm ω (x i) = 1) ∧
      (exteriorBaseChangeEquiv ℚ (rationalAdelicStructure.ϕ ω).Completion RationalPlane _).symm
        (_root_.exteriorPower.ιMulti (rationalAdelicStructure.ϕ ω).Completion _ x) =
          (-2 : (rationalAdelicStructure.ϕ ω).Completion) •
            ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ] squareDetGenerator) := by
  let k := (rationalAdelicStructure.ϕ ω).Completion
  let e := finCongr squareNorm_finrank.symm
  let c := (squareBasis.baseChange k).equivFun
  let x : Fin (Module.finrank ℚ RationalPlane) → k ⊗[ℚ] RationalPlane := fun i ↦
    c.symm (if e.symm i = 0 then (![1, 1] : Fin 2 → k) else ![1, -1])
  let w := (exteriorBaseChangeEquiv ℚ k RationalPlane _).symm
    (_root_.exteriorPower.ιMulti k _ x)
  let g := (1 : k) ⊗ₜ[ℚ] squareDetGenerator
  have hx (i : Fin (Module.finrank ℚ RationalPlane)) : squareNorm.norm ω (x i) = 1 := by
    rw [squareNorm_norm_coordinates]
    change ‖c (c.symm _)‖ = 1
    rw [LinearEquiv.apply_symm_apply, squareCoordinateNorm]
    split_ifs <;> simp
  have hd : (squareDetBasis.baseChange k).det x = (-2 : k) := by
    rw [squareCompletedDetFormula]
    change c (x (e 0)) 0 * c (x (e 1)) 1 - c (x (e 1)) 0 * c (x (e 0)) 1 = _
    simp [x]
    ring
  have hw : w = (-2 : k) • g := by
    apply (squareCompletedDetCoordinate ω).injective
    have hew : squareCompletedDetCoordinate ω w = (squareDetBasis.baseChange k).det x := by
      change determinantCoordinateEquiv (squareDetBasis.baseChange k)
        (exteriorBaseChangeEquiv ℚ k RationalPlane _
          ((exteriorBaseChangeEquiv ℚ k RationalPlane _).symm _)) = _
      rw [LinearEquiv.apply_symm_apply, determinantCoordinateEquiv_ιMulti]
    have heg : squareCompletedDetCoordinate ω g = 1 := squareCompletedDetCoordinate_generator ω
    calc
      squareCompletedDetCoordinate ω w = (-2 : k) := hew.trans hd
      _ = (-2 : k) • squareCompletedDetCoordinate ω g := by
        calc
          (-2 : k) = (-2 : k) • (1 : k) := by simp only [smul_eq_mul, mul_one]
          _ = (-2 : k) • squareCompletedDetCoordinate ω g :=
            congrArg (fun a : k ↦ (-2 : k) • a) heg.symm
      _ = squareCompletedDetCoordinate ω ((-2 : k) • g) :=
        ((squareCompletedDetCoordinate ω).map_smul (-2 : k) g).symm
  exact ⟨x, hx, hw⟩

private theorem squareRealCompletion_norm_two :
    ‖(2 : (rationalAdelicStructure.ϕ (Sum.inr ())).Completion)‖ = 2 := by
  have hn : ‖algebraMap ℚ (rationalAdelicStructure.ϕ (Sum.inr ())).Completion (2 : ℚ)‖ =
      (2 : ℝ) := by
    change ‖(WithAbs.toAbs (rationalAdelicStructure.ϕ (Sum.inr ())) (2 : ℚ) :
      (rationalAdelicStructure.ϕ (Sum.inr ())).Completion)‖ = 2
    rw [UniformSpace.Completion.norm_coe]
    change Rat.AbsoluteValue.real (2 : ℚ) = 2
    norm_num [Rat.AbsoluteValue.real_eq_abs]
  simpa only [map_ofNat] using hn

/-- The actual determinant generator has real square volume `1/2`. -/
theorem squareNorm_determinant_norm_generator_infinite :
    squareNorm.toNormFamily.determinant.norm (Sum.inr ())
      ((1 : (rationalAdelicStructure.ϕ (Sum.inr ())).Completion) ⊗ₜ[ℚ] squareDetGenerator) =
        (1 : ℝ) / 2 := by
  let ω : rationalAdelicStructure.Ω := Sum.inr ()
  let k := (rationalAdelicStructure.ϕ ω).Completion
  obtain ⟨x, hx, hw⟩ := exists_squareCompletedDet_witness ω
  let w := (exteriorBaseChangeEquiv ℚ k RationalPlane _).symm
    (_root_.exteriorPower.ιMulti k _ x)
  let g := (1 : k) ⊗ₜ[ℚ] squareDetGenerator
  have hu := squareNorm.toNormFamily.determinant_norm_ιMulti_le ω x
  change squareNorm.toNormFamily.determinant.norm ω w ≤ _ at hu
  have hnu : squareNorm.toNormFamily.determinant.norm ω w =
      2 * squareNorm.toNormFamily.determinant.norm ω g := by
    calc
      _ = squareNorm.toNormFamily.determinant.norm ω ((-2 : k) • g) :=
        congrArg (squareNorm.toNormFamily.determinant.norm ω) hw
      _ = ‖(-2 : k)‖ * squareNorm.toNormFamily.determinant.norm ω g :=
        squareNorm.toNormFamily.determinant.norm_smul ω (-2 : k) g
      _ = _ := congrArg (fun r : ℝ ↦ r * squareNorm.toNormFamily.determinant.norm ω g)
        ((_root_.norm_neg (2 : k)).trans squareRealCompletion_norm_two)
  rw [hnu] at hu
  simp only [hx, Finset.prod_const_one] at hu
  have hl := squareCompletedDetCoordinate_norm_le_two ω g
  have heg := congrArg (fun a : k ↦ ‖a‖) (squareCompletedDetCoordinate_generator ω)
  have hgn : ‖squareCompletedDetCoordinate ω g‖ = 1 := heg.trans norm_one
  have hl' : 1 ≤ 2 * squareNorm.toNormFamily.determinant.norm ω g := hgn.symm.le.trans hl
  change squareNorm.toNormFamily.determinant.norm ω g = _
  linarith

/-- The standard generator is nonzero on the actual rational determinant line. -/
theorem squareDetGenerator_ne_zero : squareDetGenerator ≠ 0 := by
  intro hz
  have he : determinantCoordinateEquiv squareDetBasis squareDetGenerator = 1 := by
    rw [squareDetGenerator, determinantCoordinateEquiv_ιMulti, Module.Basis.det_self]
  rw [hz, map_zero] at he
  exact zero_ne_one he

/-- The actual logarithmic determinant norm is supported on the single real place. -/
theorem squareNorm_determinant_logNorm_generator :
    squareNorm.toNormFamily.determinant.logNorm squareDetGenerator =
      rationalAdelicStructure.Ωinf.indicator (fun _ ↦ -Real.log 2) := by
  classical
  funext ω
  cases ω with
  | inl p =>
      have hn := squareNorm_determinant_norm_generator_finite (Sum.inl p)
        (rationalAdelicStructure_prime_mem_fin p)
      have he := congrArg Real.log hn
      change Real.log (squareNorm.toNormFamily.determinant.norm (Sum.inl p)
        (1 ⊗ₜ[ℚ] squareDetGenerator)) = _
      have hi : (Sum.inl p : rationalAdelicStructure.Ω) ∉ rationalAdelicStructure.Ωinf :=
        fun h ↦ h (rationalAdelicStructure_prime_mem_fin p)
      calc
        _ = 0 := he.trans Real.log_one
        _ = _ := (Set.indicator_of_notMem hi
          (fun _ : rationalAdelicStructure.Ω ↦ -Real.log 2)).symm
  | inr u =>
      cases u
      have he := congrArg Real.log squareNorm_determinant_norm_generator_infinite
      change Real.log (squareNorm.toNormFamily.determinant.norm (Sum.inr ())
        (1 ⊗ₜ[ℚ] squareDetGenerator)) = _
      calc
        _ = -Real.log 2 := he.trans (by rw [one_div, Real.log_inv])
        _ = _ := (Set.indicator_of_mem rationalAdelicStructure_infinite_mem_inf
          (fun _ : rationalAdelicStructure.Ω ↦ -Real.log 2)).symm

/-- The genuine Arakelov degree of the actual square bundle is `log 2`. -/
theorem squareNorm_degree :
    squareNorm.degree (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)
      (hN := ⟨rationalAdelicStructure_isRCLike⟩) = Real.log 2 := by
  rw [AdelicVectorBundle.degree_eq_neg_integral _
    ⟨squareDetGenerator, squareDetGenerator_ne_zero⟩, squareNorm_determinant_logNorm_generator,
    integral_indicator_const _ rationalAdelicStructure.measurableSet_Ωinf]
  have hm : rationalAdelicStructure.v.real rationalAdelicStructure.Ωinf = 1 := by
    rw [Measure.real, rationalAdelicStructure_v_Ωinf, ENNReal.toReal_one]
  rw [hm, one_smul, neg_neg]

private theorem squareOneWedge_injective {k F : Type*} [Field k]
    [AddCommGroup F] [Module k F] {n : ℕ} (hn : n = 1)
    {x y : Fin n → F} (h : _root_.exteriorPower.ιMulti k n x =
      _root_.exteriorPower.ιMulti k n y) : x = y := by
  subst n
  have he := congrArg (_root_.exteriorPower.oneEquiv k F) h
  rw [_root_.exteriorPower.oneEquiv_ιMulti, _root_.exteriorPower.oneEquiv_ιMulti] at he
  funext i
  fin_cases i
  exact he

private theorem squareLineDeterminant_norm {F : Type*} [AddCommGroup F] [Module ℚ F]
    [FiniteDimensional ℚ F] (ξ : NormFamily rationalAdelicStructure F)
    (hr : Module.finrank ℚ F = 1) (ω : rationalAdelicStructure.Ω)
    (x : Fin (Module.finrank ℚ F) → (rationalAdelicStructure.ϕ ω).Completion ⊗[ℚ] F) :
    ξ.determinant.norm ω
      ((exteriorBaseChangeEquiv ℚ (rationalAdelicStructure.ϕ ω).Completion F _).symm
        (_root_.exteriorPower.ιMulti (rationalAdelicStructure.ϕ ω).Completion _ x)) =
          ∏ i, ξ.norm ω (x i) := by
  apply le_antisymm (ξ.determinant_norm_ιMulti_le ω x)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨y, hy, hc⟩ := ξ.exists_determinant_ιMulti_norm_lt
    (by rw [hr]; exact zero_lt_one) ω
    ((exteriorBaseChangeEquiv ℚ (rationalAdelicStructure.ϕ ω).Completion F _).symm
      (_root_.exteriorPower.ιMulti (rationalAdelicStructure.ϕ ω).Completion _ x)) hε
  have hw := (exteriorBaseChangeEquiv ℚ
    (rationalAdelicStructure.ϕ ω).Completion F _).symm.injective hy
  have he : y = x := squareOneWedge_injective hr hw
  rw [he] at hc
  exact hc.le

private theorem squareLineDegreeFormula
     (V : AdelicVectorBundle rationalAdelicStructure)
    (hr : Module.finrank ℚ V = 1) (x : V) (hx : x ≠ 0) :
    V.degree (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)
        (hN := ⟨rationalAdelicStructure_isRCLike⟩) =
      -(∫ ω, V.toNormFamily.logNorm x ω ∂rationalAdelicStructure.v) := by
  let b : Module.Basis (Fin (Module.finrank ℚ V)) ℚ V :=
    (FiniteDimensional.basisSingleton (Fin 1) hr x hx).reindex (finCongr hr.symm)
  have hb (i : Fin (Module.finrank ℚ V)) : b i = x := by
    simp only [b, Module.Basis.reindex_apply, FiniteDimensional.basisSingleton_apply]
  let t := _root_.exteriorPower.ιMulti ℚ (Module.finrank ℚ V) b
  have ht : t ≠ 0 := by
    intro hz
    have he : determinantCoordinateEquiv b t = 1 := by
      change determinantCoordinateEquiv b (_root_.exteriorPower.ιMulti ℚ _ b) = 1
      rw [determinantCoordinateEquiv_ιMulti, Module.Basis.det_self]
    rw [hz, map_zero] at he
    exact zero_ne_one he
  rw [V.degree_eq_neg_integral ⟨t, ht⟩]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  have he : (exteriorBaseChangeEquiv ℚ (rationalAdelicStructure.ϕ ω).Completion V _).symm
      (_root_.exteriorPower.ιMulti (rationalAdelicStructure.ϕ ω).Completion _
        (fun i ↦ (1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ] b i)) =
      (1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ] t := by
    rw [exteriorBaseChangeEquiv_symm_ιMulti_tmul, Finset.prod_const_one]
  have hn := squareLineDeterminant_norm V.toNormFamily hr ω
    (fun i ↦ (1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ] b i)
  rw [he] at hn
  have hp : (∏ i : Fin (Module.finrank ℚ V),
      V.norm ω ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ] b i)) =
      V.norm ω ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ] x) := by
    simp only [hb, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hr, pow_one]
  exact congrArg Real.log (hn.trans hp)

/-- Every nonzero actual square vector has nonpositive vector degree. -/
theorem squareNorm_vectorDegree_le_zero (x : {x : RationalPlane // x ≠ 0}) :
    squareNorm.toNormFamily.vectorDegree
      (hd := squareNorm.isDominated) (hm := squareNorm.isMeasurable) x ≤ 0 := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, x.val i ≠ 0 := by
    by_contra h
    apply x.property
    ext i
    exact not_ne_iff.mp (not_exists.mp h i)
  have hn : ∀ ω : rationalAdelicStructure.Ω,
      Real.log (rationalAdelicStructure.ϕ ω (x.val i)) ≤
        squareNorm.toNormFamily.logNorm x.val ω := by
    intro ω
    apply Real.log_le_log (rationalAdelicStructure.ϕ ω |>.pos hi)
    rw [squareNorm_norm_max_rational]
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hm := integral_mono (rationalAdelicStructure.integrable_log _ hi)
    (squareNorm.integrable_logNorm x.val) hn
  rw [AdelicStructure.IsProper.product_formula _ hi] at hm
  rw [NormFamily.vectorDegree_eq_neg_integral]
  linarith

/-- All actual rational square lines have nonpositive Arakelov degree. -/
theorem squareNorm_degree_restrict_le_zero (U : Submodule ℚ RationalPlane)
    (hr : Module.finrank ℚ U = 1) :
    (squareNorm.restrictOfNormMeasurability U
        (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)).degree
      (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)
          (hN := ⟨rationalAdelicStructure_isRCLike⟩) ≤ 0 := by
  let V :=
    squareNorm.restrictOfNormMeasurability U (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)
  let x := V.lineGenerator (hV := ⟨hr⟩)
  have hx : (x.val : RationalPlane) ≠ 0 := by
    intro h
    exact x.property (Subtype.ext h)
  rw [squareLineDegreeFormula V hr x.val x.property]
  have he : V.toNormFamily.logNorm x.val =
      squareNorm.toNormFamily.logNorm (x.val : RationalPlane) := by
    funext ω
    unfold NormFamily.logNorm
    change Real.log ((squareNorm.toNormFamily.restrict U).norm ω (1 ⊗ₜ[ℚ] x.val)) = _
    rw [NormFamily.restrict_norm, LinearMap.baseChange_tmul]
    rfl
  rw [he]
  simpa only [NormFamily.vectorDegree_eq_neg_integral] using
    squareNorm_vectorDegree_le_zero ⟨x.val, hx⟩

private theorem squareCompletedScalar_norm (ω : rationalAdelicStructure.Ω) (a : ℚ) :
    ‖algebraMap ℚ (rationalAdelicStructure.ϕ ω).Completion a‖ =
      rationalAdelicStructure.ϕ ω a := by
  change ‖(WithAbs.toAbs (rationalAdelicStructure.ϕ ω) a :
    (rationalAdelicStructure.ϕ ω).Completion)‖ = _
  rw [UniformSpace.Completion.norm_coe]
  rfl

private theorem squareQuotient_dual_coord_le (U : Submodule ℚ RationalPlane)
    (ℓ : Module.Dual ℚ (RationalPlane ⧸ U)) (i : Fin 2)
    (ω : rationalAdelicStructure.Ω) :
    rationalAdelicStructure.ϕ ω (ℓ (U.mkQ (squareBasis i))) ≤
      (squareNorm.toNormFamily.quotient U).dual.norm ω
        ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ] ℓ) := by
  let ξ := squareNorm.toNormFamily.quotient U
  have hn : ξ.norm ω ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ]
      U.mkQ (squareBasis i)) ≤ 1 := by
    have h := squareNorm.toNormFamily.quotient_norm_mk_le U ω
      ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ] squareBasis i)
    rw [LinearMap.baseChange_tmul, squareNorm_toNormFamily,
      NormFamily.ofBasis_norm_tmul_basis, norm_one] at h
    exact h
  have he := ξ.norm_dual_apply_le ω
    ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ] ℓ)
    ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ] U.mkQ (squareBasis i))
  rw [dualBaseChangeEquiv_tmul_apply_tmul, one_mul, one_mul,
    squareCompletedScalar_norm] at he
  exact he.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hn (ξ.dual.norm_nonneg ω _))

/-- Every actual rational quotient line of the square has nonnegative degree. -/
theorem squareNorm_degree_quotient_nonneg (U : Submodule ℚ RationalPlane)
    (hr : Module.finrank ℚ (RationalPlane ⧸ U) = 1) :
    0 ≤ (squareNorm.quotientOfNormMeasurability U
      (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)).degree
        (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)
            (hN := ⟨rationalAdelicStructure_isRCLike⟩) := by
  let Q :=
    squareNorm.quotientOfNormMeasurability U (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)
  let z := Q.lineGenerator (hV := ⟨hr⟩)
  obtain ⟨ℓ, he⟩ := Module.Projective.exists_dual_eq_one ℚ z.property
  let f := ℓ.comp U.mkQ
  have hf : f ≠ 0 := by
    intro h
    obtain ⟨x, hx⟩ := U.mkQ_surjective z.val
    have hzero : ℓ z.val = 0 := by
      rw [← hx]
      exact congrArg (fun g : RationalPlane →ₗ[ℚ] ℚ ↦ g x) h
    rw [he] at hzero
    exact one_ne_zero hzero
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, f (squareBasis i) ≠ 0 := by
    by_contra h
    apply hf
    apply squareBasis.ext
    intro i
    exact not_ne_iff.mp (not_exists.mp h i)
  have hb : ∀ ω : rationalAdelicStructure.Ω,
      Real.log (rationalAdelicStructure.ϕ ω (f (squareBasis i))) ≤
        Q.toNormFamily.dual.logNorm ℓ ω := by
    intro ω
    exact Real.log_le_log (rationalAdelicStructure.ϕ ω |>.pos hi)
      (squareQuotient_dual_coord_le U ℓ i ω)
  have hm := integral_mono (rationalAdelicStructure.integrable_log _ hi)
    ((Q.dualOfNormMeasurability (hS := ⟨(Or.inl
        rationalAdelicStructure_discrete)⟩)).integrable_logNorm ℓ)
    hb
  rw [AdelicStructure.IsProper.product_formula _ hi] at hm
  change 0 ≤ ∫ ω, Q.toNormFamily.dual.logNorm ℓ ω ∂rationalAdelicStructure.v at hm
  rw [squareLineDegreeFormula Q hr z.val z.property]
  have heq : Q.toNormFamily.dual.logNorm ℓ = fun ω ↦ -Q.toNormFamily.logNorm z.val ω := by
    funext ω
    exact Q.toNormFamily.dual_logNorm_eq_neg hr he ω
  rw [heq, integral_neg] at hm
  exact hm

/-- The actual rational coordinate line. -/
def squareCoordinateLine (i : Fin 2) : Submodule ℚ RationalPlane := ℚ ∙ squareBasis i

/-- Each actual coordinate line has rank one. -/
theorem squareCoordinateLine_finrank (i : Fin 2) :
    Module.finrank ℚ (squareCoordinateLine i) = 1 :=
  finrank_span_singleton (squareBasis.ne_zero i)

/-- The actual restricted degree of either coordinate line is zero. -/
theorem squareNorm_degree_coordinateLine (i : Fin 2) :
    (squareNorm.restrictOfNormMeasurability (squareCoordinateLine i)
      (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)).degree
        (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)
            (hN := ⟨rationalAdelicStructure_isRCLike⟩) = 0 := by
  let U := squareCoordinateLine i
  let x : U := ⟨squareBasis i, Submodule.mem_span_singleton_self _⟩
  have hx : x ≠ 0 := by
    intro h
    exact squareBasis.ne_zero i (congrArg Subtype.val h)
  let V :=
    squareNorm.restrictOfNormMeasurability U (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)
  rw [squareLineDegreeFormula V (squareCoordinateLine_finrank i) x hx]
  have he : V.toNormFamily.logNorm x = 0 := by
    funext ω
    unfold NormFamily.logNorm
    change Real.log ((squareNorm.toNormFamily.restrict U).norm ω (1 ⊗ₜ[ℚ] x)) = 0
    rw [NormFamily.restrict_norm, LinearMap.baseChange_tmul, squareNorm_toNormFamily]
    change Real.log ((NormFamily.ofBasis rationalAdelicStructure RationalPlane squareBasis).norm
      ω (1 ⊗ₜ[ℚ] squareBasis i)) = 0
    rw [NormFamily.ofBasis_norm_tmul_basis, norm_one, Real.log_one]
  simp only [he, Pi.zero_apply, integral_zero, neg_zero]

/-- The true completed dual coordinate functional has norm one at every place. -/
theorem squareNorm_dual_norm_coordinate (ω : rationalAdelicStructure.Ω) (i : Fin 2) :
    squareNorm.toNormFamily.dual.norm ω
      ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ] squareBasis.coord i) = 1 := by
  let k := (rationalAdelicStructure.ϕ ω).Completion
  let b := squareBasis.baseChange k
  have he : dualBaseChangeEquiv ℚ k RationalPlane
      ((1 : k) ⊗ₜ[ℚ] squareBasis.coord i) = b.coord i := by
    apply b.ext
    intro j
    rw [Module.Basis.baseChange_apply, dualBaseChangeEquiv_tmul_apply_tmul]
    fin_cases i <;> fin_cases j <;>
      simp [b, Module.Basis.coord_apply, Module.Basis.repr_self]
  apply le_antisymm
  · apply squareNorm.toNormFamily.dual_norm_le ω _ (by norm_num : (0 : ℝ) ≤ 1)
    intro z
    rw [he, one_mul, Module.Basis.coord_apply, ← Module.Basis.equivFun_apply,
      squareNorm_norm_max]
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · have h := squareNorm.toNormFamily.norm_dual_apply_le ω
      ((1 : k) ⊗ₜ[ℚ] squareBasis.coord i) ((1 : k) ⊗ₜ[ℚ] squareBasis i)
    rw [dualBaseChangeEquiv_tmul_apply_tmul, one_mul, one_mul,
      squareCompletedScalar_norm, Module.Basis.coord_apply, Module.Basis.repr_self] at h
    simp only [Finsupp.single_eq_same, map_one] at h
    rw [NormFamily.ofBasis_norm_tmul_basis, norm_one, mul_one] at h
    exact h

/-- The kernel of an actual coordinate quotient. -/
def squareCoordinateKernel (i : Fin 2) : Submodule ℚ RationalPlane :=
  (squareBasis.coord i).ker

/-- Each actual coordinate quotient has rank one. -/
theorem squareCoordinateQuotient_finrank (i : Fin 2) :
    Module.finrank ℚ (RationalPlane ⧸ squareCoordinateKernel i) = 1 := by
  have hf : Function.Surjective (squareBasis.coord i) := by
    intro a
    refine ⟨a • squareBasis i, ?_⟩
    simp [Module.Basis.coord_apply, Module.Basis.repr_self]
  exact ((squareBasis.coord i).quotKerEquivOfSurjective hf).finrank_eq.trans
    (Module.finrank_self ℚ)

/-- A coordinate quotient generator has its genuine quotient norm one everywhere. -/
theorem squareNorm_coordinateQuotient_norm_generator (i : Fin 2)
    (ω : rationalAdelicStructure.Ω) :
    (squareNorm.toNormFamily.quotient (squareCoordinateKernel i)).norm ω
      ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ]
        (squareCoordinateKernel i).mkQ (squareBasis i)) = 1 := by
  let U := squareCoordinateKernel i
  have hker : U ≤ (squareBasis.coord i).ker := fun _ hx ↦ hx
  let ℓ := U.liftQ (squareBasis.coord i) hker
  let x := U.mkQ (squareBasis i)
  have he : ℓ x = 1 := by
    change (U.liftQ (squareBasis.coord i) hker)
      (Submodule.Quotient.mk (squareBasis i)) = 1
    rw [Submodule.liftQ_apply]
    simp [Module.Basis.coord_apply, Module.Basis.repr_self]
  have hx : x ≠ 0 := by
    intro h
    rw [h, map_zero] at he
    exact zero_ne_one he
  have hd : (squareNorm.toNormFamily.quotient U).dual.norm ω
      ((1 : (rationalAdelicStructure.ϕ ω).Completion) ⊗ₜ[ℚ] ℓ) = 1 := by
    rw [NormFamily.quotient, NormFamily.pushforward_dual_norm_eq,
      LinearMap.baseChange_tmul]
    have hℓ : U.mkQ.dualMap ℓ = squareBasis.coord i := by
      exact Submodule.liftQ_mkQ U _ hker
    rw [hℓ, squareNorm_dual_norm_coordinate]
  have hn := (squareNorm.toNormFamily.quotient U).dual_norm_rational_eq_div
    (squareCoordinateQuotient_finrank i) hx ℓ ω
  rw [hd, he, map_one, one_div] at hn
  exact inv_eq_one.mp hn.symm

/-- The actual degree of either coordinate quotient is zero. -/
theorem squareNorm_degree_coordinateQuotient (i : Fin 2) :
    (squareNorm.quotientOfNormMeasurability (squareCoordinateKernel i)
      (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)).degree
        (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)
            (hN := ⟨rationalAdelicStructure_isRCLike⟩) = 0 := by
  let U := squareCoordinateKernel i
  let x := U.mkQ (squareBasis i)
  have hker : U ≤ (squareBasis.coord i).ker := fun _ hx ↦ hx
  have hx : x ≠ 0 := by
    intro h
    have he : (U.liftQ (squareBasis.coord i) hker) x = 1 := by
      change (U.liftQ (squareBasis.coord i) hker)
        (Submodule.Quotient.mk (squareBasis i)) = 1
      rw [Submodule.liftQ_apply]
      simp [Module.Basis.coord_apply, Module.Basis.repr_self]
    rw [h, map_zero] at he
    exact zero_ne_one he
  let Q :=
    squareNorm.quotientOfNormMeasurability U (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)
  rw [squareLineDegreeFormula Q (squareCoordinateQuotient_finrank i) x hx]
  have he : Q.toNormFamily.logNorm x = 0 := by
    funext ω
    unfold NormFamily.logNorm
    change Real.log ((squareNorm.toNormFamily.quotient (squareCoordinateKernel i)).norm
      ω (1 ⊗ₜ[ℚ] (squareCoordinateKernel i).mkQ (squareBasis i))) = 0
    rw [squareNorm_coordinateQuotient_norm_generator, Real.log_one]
  simp only [he, Pi.zero_apply, integral_zero, neg_zero]



/-- The actual mean slope of the square is half its produced degree. -/
theorem squareNorm_slope :
    squareNorm.slope (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)
      (hN := ⟨rationalAdelicStructure_isRCLike⟩) = Real.log 2 / 2 := by
  rw [AdelicVectorBundle.slope, squareNorm_degree, squareNorm_finrank]
  norm_num

/-- The actual maximal slope is the positive mean of the entire square. -/
theorem squareNorm_maximalSlope :
    squareNorm.maximalSlope (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)
      (hN := ⟨rationalAdelicStructure_isRCLike⟩) = (Real.log 2 / 2 : ℝ) := by
  let hS : DiscreteMeasurableSpace rationalAdelicStructure.Ω ∨
      rationalAdelicStructure.HasCommonCountableDenseSubfield :=
    Or.inl rationalAdelicStructure_discrete
  have hc : 0 ≤ Real.log 2 / 2 := div_nonneg (Real.log_pos (by norm_num)).le (by norm_num)
  apply le_antisymm
  · apply squareNorm.maximalSlope_le (hS := ⟨hS⟩) (hN := ⟨rationalAdelicStructure_isRCLike⟩)
    intro U hU
    have hle := U.finrank_le
    rw [squareNorm_finrank] at hle
    by_cases hr : Module.finrank ℚ U = 1
    · rw [AdelicVectorBundle.slope_eq_degree_of_finrank_one _ hr]
      exact EReal.coe_le_coe ((squareNorm_degree_restrict_le_zero U hr).trans hc)
    · have htop : U = ⊤ := Submodule.eq_top_of_finrank_eq
        (show Module.finrank ℚ U = Module.finrank ℚ RationalPlane by
          rw [squareNorm_finrank]; omega)
      rw [htop, squareNorm.slope_restrict_top, squareNorm_slope]
  · rw [← squareNorm_slope]
    exact squareNorm.slope_le_maximalSlope (hS := ⟨hS⟩) (hN := ⟨rationalAdelicStructure_isRCLike⟩)
      (by rw [squareNorm_finrank]; norm_num)

/-- The actual minimal slope is zero, using all quotient bounds and an attained witness. -/
theorem squareNorm_minimalSlope :
    squareNorm.minimalSlope (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)
      (hN := ⟨rationalAdelicStructure_isRCLike⟩) = 0 := by
  let hS : DiscreteMeasurableSpace rationalAdelicStructure.Ω ∨
      rationalAdelicStructure.HasCommonCountableDenseSubfield :=
    Or.inl rationalAdelicStructure_discrete
  apply le_antisymm
  · have h := squareNorm.minimalSlope_le_slope_quotient (squareCoordinateKernel 0)
      (by rw [squareCoordinateQuotient_finrank]; exact zero_lt_one)
      (hS := ⟨hS⟩) (hN := ⟨rationalAdelicStructure_isRCLike⟩)
    rw [AdelicVectorBundle.slope_eq_degree_of_finrank_one _
      (squareCoordinateQuotient_finrank 0), squareNorm_degree_coordinateQuotient] at h
    exact h
  · apply squareNorm.le_minimalSlope (hS := ⟨hS⟩) (hN := ⟨rationalAdelicStructure_isRCLike⟩)
    intro U hU
    have hdim := U.finrank_quotient_add_finrank
    rw [squareNorm_finrank] at hdim
    change Module.finrank ℚ (RationalPlane ⧸ U) + Module.finrank ℚ U = 2 at hdim
    change 0 < Module.finrank ℚ (RationalPlane ⧸ U) at hU
    by_cases hr : Module.finrank ℚ (RationalPlane ⧸ U) = 1
    · have hm : 0 ≤ (squareNorm.quotientOfNormMeasurability U (hS := ⟨hS⟩)).slope
          (hS := ⟨hS⟩) (hN := ⟨rationalAdelicStructure_isRCLike⟩) := by
        rw [AdelicVectorBundle.slope_eq_degree_of_finrank_one _ hr]
        exact squareNorm_degree_quotient_nonneg U hr
      exact (EReal.coe_le_coe hm).trans
        ((squareNorm.quotientOfNormMeasurability U (hS := ⟨hS⟩)).slope_le_maximalSlope
          (hS := ⟨hS⟩) (hN := ⟨rationalAdelicStructure_isRCLike⟩) hU)
    · have hz : U = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
      rw [hz, squareNorm.maximalSlope_quotient_bot, squareNorm_maximalSlope]
      exact EReal.coe_le_coe
        (div_nonneg (Real.log_pos (by norm_num)).le (by norm_num))

/-- Every nonzero actual square subspace has minimal slope at most zero. -/
theorem squareNorm_minimalSlope_restrict_le_zero (U : Submodule ℚ RationalPlane)
    (hU : 0 < Module.finrank ℚ U) :
    (squareNorm.restrictOfNormMeasurability U
        (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)).minimalSlope
      (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)
          (hN := ⟨rationalAdelicStructure_isRCLike⟩) ≤ 0 := by
  let hS : DiscreteMeasurableSpace rationalAdelicStructure.Ω ∨
      rationalAdelicStructure.HasCommonCountableDenseSubfield :=
    Or.inl rationalAdelicStructure_discrete
  have hle := U.finrank_le
  rw [squareNorm_finrank] at hle
  by_cases hr : Module.finrank ℚ U = 1
  · have h := (squareNorm.restrictOfNormMeasurability U (hS := ⟨hS⟩)).minimalSlope_le_slope
      (hS := ⟨hS⟩) (hN := ⟨rationalAdelicStructure_isRCLike⟩) hU
    rw [AdelicVectorBundle.slope_eq_degree_of_finrank_one _ hr] at h
    exact h.trans (EReal.coe_le_coe (squareNorm_degree_restrict_le_zero U hr))
  · have htop : U = ⊤ := Submodule.eq_top_of_finrank_eq
      (show Module.finrank ℚ U = Module.finrank ℚ RationalPlane by
        rw [squareNorm_finrank]; omega)
    rw [htop, squareNorm.minimalSlope_restrict_top, squareNorm_minimalSlope]


/-- The genuine general filtration of the square has its sole threshold at zero. -/
theorem squareNorm_hnFiltration (t : ℝ) :
    squareNorm.hnFiltration (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)
      (hN := ⟨rationalAdelicStructure_isRCLike⟩) t = if t ≤ 0 then ⊤ else ⊥ := by
  let hS : DiscreteMeasurableSpace rationalAdelicStructure.Ω ∨
      rationalAdelicStructure.HasCommonCountableDenseSubfield :=
    Or.inl rationalAdelicStructure_discrete
  by_cases ht : t ≤ 0
  · rw [ite_eq_left ht]
    apply squareNorm.hnFiltration_eq_top_of_le_minimalSlope
    rw [squareNorm_minimalSlope]
    exact EReal.coe_le_coe ht
  · rw [ite_eq_right ht]
    by_contra hz
    have hp : 0 < Module.finrank ℚ (squareNorm.hnFiltration
        (hS := ⟨hS⟩) (hN := ⟨rationalAdelicStructure_isRCLike⟩) t) :=
      Nat.pos_of_ne_zero (fun h ↦ hz (Submodule.finrank_eq_zero.mp h))
    have hm := squareNorm.le_minimalSlope_restrict_hnFiltration
      (hS := ⟨hS⟩) (hN := ⟨rationalAdelicStructure_isRCLike⟩) t
    have hb := squareNorm_minimalSlope_restrict_le_zero _ hp
    have he : (t : EReal) ≤ (0 : EReal) := hm.trans hb
    exact ht (EReal.coe_le_coe_iff.mp he)

/-- Every genuine general ordered slope of the square is zero. -/
theorem squareNorm_hnSlope (j : Fin (Module.finrank ℚ RationalPlane)) :
    squareNorm.hnSlope (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)
      (hN := ⟨rationalAdelicStructure_isRCLike⟩) j = 0 := by
  let hS : DiscreteMeasurableSpace rationalAdelicStructure.Ω ∨
      rationalAdelicStructure.HasCommonCountableDenseSubfield :=
    Or.inl rationalAdelicStructure_discrete
  apply le_antisymm
  · by_contra h
    have hp : 0 < squareNorm.hnSlope (hS := ⟨hS⟩)
        (hN := ⟨rationalAdelicStructure_isRCLike⟩) j :=
      lt_of_not_ge h
    have hj := squareNorm.lt_finrank_hnFiltration_orderedSlope
      (hS := ⟨hS⟩) (hN := ⟨rationalAdelicStructure_isRCLike⟩) j
    rw [squareNorm_hnFiltration, ite_eq_right (not_le.mpr hp), finrank_bot] at hj
    exact Nat.not_lt_zero _ hj
  · have h := squareNorm.minimalSlope_le_hnSlope
      (hS := ⟨hS⟩) (hN := ⟨rationalAdelicStructure_isRCLike⟩) j
    rw [squareNorm_minimalSlope] at h
    exact EReal.coe_le_coe_iff.mp h

/-- Source strictness: every square ordered slope is below its positive maximal slope. -/
theorem squareNorm_hnSlope_lt_maximalSlope
    (j : Fin (Module.finrank ℚ RationalPlane)) :
    (squareNorm.hnSlope (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)
      (hN := ⟨rationalAdelicStructure_isRCLike⟩) j : EReal) <
        squareNorm.maximalSlope (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)
          (hN := ⟨rationalAdelicStructure_isRCLike⟩) := by
  rw [squareNorm_hnSlope, squareNorm_maximalSlope]
  exact EReal.coe_lt_coe (div_pos (Real.log_pos (by norm_num)) (by norm_num))

/-- Source distinction: the sum of actual ordered slopes is strictly below actual degree. -/
theorem squareNorm_sum_hnSlope_lt_degree :
    (∑ j : Fin (Module.finrank ℚ RationalPlane),
      squareNorm.hnSlope (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)
        (hN := ⟨rationalAdelicStructure_isRCLike⟩) j) <
          squareNorm.degree (hS := ⟨(Or.inl rationalAdelicStructure_discrete)⟩)
            (hN := ⟨rationalAdelicStructure_isRCLike⟩) := by
  simp only [squareNorm_hnSlope, Finset.sum_const_zero, squareNorm_degree]
  exact Real.log_pos (by norm_num)

end

end ArakelovGeometry.AdelicVectorBundle.Examples
