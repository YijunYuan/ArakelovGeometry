/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Measurability.Basic
public import ArakelovGeometry.AdelicVectorBundle.Measurability.Density.Basic
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Hermitian.Basic
public import ArakelovGeometry.Analysis.Convex.JohnEllipsoid.RationalEllipsoid
public import Mathlib.CategoryTheory.Category.Basic

import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicVectorBundle.Measurability.Archimedean
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
import ArakelovGeometry.Analysis.Convex.JohnEllipsoid.JohnNorm
import ArakelovGeometry.Analysis.Convex.JohnEllipsoid.MeasurableEllipsoid
import ArakelovGeometry.Analysis.Hermitian.Norm
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Measurable Hermitian approximation

Rational matrix factors act on compatible complex coordinates of the actual
completed fibre. A countable measurable selection supplies the required norm
bounds at infinite places. Pasting these candidates with the original norms
at finite places gives the global Hermitian approximation of Theorem 4.1.26.
-/

@[expose] public section

open scoped TensorProduct
open Matrix

noncomputable section

namespace ArakelovGeometry.NormFamily

universe u v w wι

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E]
  {ι : Type wι} [Fintype ι] [DecidableEq ι]

/-- Compatible complex coordinates of the actual completed basis. -/
def completedComplexCoordinates (b : Module.Basis ι K E) (ω : S.Ω)
    (σ : (S.ϕ ω).Completion →+* ℂ) :
    ((S.ϕ ω).Completion ⊗[K] E) →ₛₗ[σ] EuclideanSpace ℂ ι where
  toFun x := WithLp.toLp 2 (fun i =>
    σ ((b.baseChange (S.ϕ ω).Completion).equivFun x i))
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp [smul_eq_mul]

/-- A complex rational factor defines an actual completed-field seminorm.
Separation is proved from the selected lower bound below. -/
def complexEllipsoidSeminorm (b : Module.Basis ι K E) (ω : S.Ω)
    (σ : (S.ϕ ω).Completion →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (Q : Matrix ι ι (ℚ × ℚ)) :
    Seminorm (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E) := by
  let : RingHomIsometric σ := ⟨fun {x} => hσ x⟩
  exact (normSeminorm ℂ (EuclideanSpace ℂ ι)).comp
    (((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι))
      (rationalMatrix ℂ Q)).toLinearMap.comp (completedComplexCoordinates b ω σ))

theorem complexEllipsoidSeminorm_apply (b : Module.Basis ι K E) (ω : S.Ω)
    (σ : (S.ϕ ω).Completion →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (Q : Matrix ι ι (ℚ × ℚ)) (x : (S.ϕ ω).Completion ⊗[K] E) :
    complexEllipsoidSeminorm b ω σ hσ Q x =
      ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) (rationalMatrix ℂ Q)
        (completedComplexCoordinates b ω σ x)‖ := rfl

/-- The candidate norm is an explicit finite formula in the embedded coordinates. -/
theorem complexEllipsoidSeminorm_formula (b : Module.Basis ι K E) (ω : S.Ω)
    (σ : (S.ϕ ω).Completion →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (Q : Matrix ι ι (ℚ × ℚ)) (x : (S.ϕ ω).Completion ⊗[K] E) :
    complexEllipsoidSeminorm b ω σ hσ Q x =
      Real.sqrt (∑ i, ‖∑ j, rationalMatrix ℂ Q i j *
        σ ((b.baseChange (S.ϕ ω).Completion).equivFun x j)‖ ^ 2) := by
  rw [complexEllipsoidSeminorm_apply, PiLp.norm_eq_of_L2]
  rfl

/-- Every candidate has the parallelogram identity on the original completed module. -/
theorem complexEllipsoidSeminorm_parallelogram (b : Module.Basis ι K E) (ω : S.Ω)
    (σ : (S.ϕ ω).Completion →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (Q : Matrix ι ι (ℚ × ℚ)) (x y : (S.ϕ ω).Completion ⊗[K] E) :
    (complexEllipsoidSeminorm b ω σ hσ Q (x + y)) ^ 2 +
      (complexEllipsoidSeminorm b ω σ hσ Q (x - y)) ^ 2 =
        2 * ((complexEllipsoidSeminorm b ω σ hσ Q x) ^ 2 +
          (complexEllipsoidSeminorm b ω σ hσ Q y) ^ 2) := by
  simp only [complexEllipsoidSeminorm_apply, map_add, map_sub]
  exact parallelogram_law_with_norm ℂ _ _

/-- Candidate seminorms are continuous in every original completed-fibre norm. -/
theorem continuous_complexEllipsoidSeminorm (ξ : NormFamily S E)
    (b : Module.Basis ι K E) (ω : S.Ω)
    (σ : (S.ϕ ω).Completion →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (Q : Matrix ι ι (ℚ × ℚ)) :
    letI := ξ.fibreNormedAddCommGroup ω
    Continuous (complexEllipsoidSeminorm b ω σ hσ Q) := by
  let := Module.Finite.of_basis b
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  have hB := (linearMapToNormedAddGroupHom
    (b.baseChange (S.ϕ ω).Completion).equivFun.toLinearMap).continuous
  have hcoord (i : ι) : Continuous (fun x =>
      σ ((b.baseChange (S.ϕ ω).Completion).equivFun x i)) :=
    (isometry_complexEmbedding_of_norm σ hσ).continuous.comp
      ((continuous_apply i).comp hB)
  change Continuous (fun x => complexEllipsoidSeminorm b ω σ hσ Q x)
  simp only [complexEllipsoidSeminorm_formula]
  exact (continuous_finsetSum _ fun i _ =>
    ((continuous_finsetSum _ fun j _ =>
      continuous_const.mul (hcoord j)).norm.pow 2)).sqrt

/-- The finite rational-vector formula is measurable for every fixed candidate. -/
theorem measurable_complexEllipsoidSeminorm_rational
    (b : Module.Basis ι K E)
    (σ : ∀ ω : S.Ωinf, (S.ϕ ω.val).Completion →+* ℂ)
    (hσ : ∀ ω x, ‖σ ω x‖ = ‖x‖)
    (hm : ∀ x : K, Measurable (fun ω : S.Ωinf =>
      σ ω (algebraMap K (S.ϕ ω.val).Completion x)))
    (Q : Matrix ι ι (ℚ × ℚ)) (x : E) :
    Measurable (fun ω : S.Ωinf => complexEllipsoidSeminorm b ω.val (σ ω) (hσ ω) Q
      ((1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] x)) := by
  simp only [complexEllipsoidSeminorm_formula, basis_equivFun_one_tmul]
  exact (Finset.measurable_sum _ fun i _ =>
    ((Finset.measurable_sum _ fun j _ =>
      measurable_const.mul (hm (b.equivFun x j))).norm.pow_const 2)).sqrt

/-- The local John producer supplies a strictly admissible candidate at every
normalized infinite place. No measurability hypothesis is used locally. -/
theorem exists_strict_complexEllipsoidSeminorm (ξ : NormFamily S E)
    (b : Module.Basis ι K E) (ω : S.Ω) [IsRCLikeNormedField (S.ϕ ω).Completion]
    (σ : (S.ϕ ω).Completion →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Q : Matrix ι ι (ℚ × ℚ)) (δ : ℚ), 0 < δ ∧ ∀ x,
      (1 + (δ : ℝ)) * (ξ.norm ω x) ^ 2 ≤
        (complexEllipsoidSeminorm b ω σ hσ Q x) ^ 2 ∧
      (complexEllipsoidSeminorm b ω σ hσ Q x) ^ 2 ≤
        (Fintype.card ι + ε - (δ : ℝ)) * (ξ.norm ω x) ^ 2 := by
  let := Module.Finite.of_basis b
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let e : ((S.ϕ ω).Completion ⊗[K] E) ≃L[(S.ϕ ω).Completion]
      EuclideanSpace (S.ϕ ω).Completion ι :=
    LinearEquiv.toContinuousLinearEquiv ((b.baseChange (S.ϕ ω).Completion).equivFun.trans
      (WithLp.linearEquiv 2 (S.ϕ ω).Completion (ι → (S.ϕ ω).Completion)).symm)
  exact exists_strict_complex_rational_coordinates e σ hσ hε

/-- Strict tests on the actual dense subfield combinations imply the desired
non-strict inequalities on every completed vector. -/
theorem complexEllipsoid_bounds_of_dense_tests (ξ : NormFamily S E)
    (b : Module.Basis ι K E) (ω : S.Ω)
    (σ : (S.ϕ ω).Completion →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (Q : Matrix ι ι (ℚ × ℚ)) (K₀ : Subfield K)
    (hK₀ : S.IsDenseSubfieldAt K₀ ω) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (ht : ∀ a : ι → K₀,
      (1 + δ) * (ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ a)) ^ 2 ≤
        (complexEllipsoidSeminorm b ω σ hσ Q
          ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ a)) ^ 2 ∧
      (complexEllipsoidSeminorm b ω σ hσ Q
        ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ a)) ^ 2 ≤
          (Fintype.card ι + ε - δ) *
            (ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ a)) ^ 2)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    ξ.norm ω x ≤ complexEllipsoidSeminorm b ω σ hσ Q x ∧
      complexEllipsoidSeminorm b ω σ hσ Q x ≤
        Real.sqrt (Fintype.card ι + ε) * ξ.norm ω x := by
  let := ξ.fibreNormedAddCommGroup ω
  have hc := ξ.continuous_complexEllipsoidSeminorm b ω σ hσ Q
  have hall : (1 + δ) * (ξ.norm ω x) ^ 2 ≤
      (complexEllipsoidSeminorm b ω σ hσ Q x) ^ 2 ∧
      (complexEllipsoidSeminorm b ω σ hσ Q x) ^ 2 ≤
        (Fintype.card ι + ε - δ) * (ξ.norm ω x) ^ 2 := by
    refine (ξ.denseRange_basisSubfieldMap b K₀ ω hK₀).induction_on x ?_ ht
    exact (isClosed_le (continuous_const.mul (continuous_norm.pow 2)) (hc.pow 2)).inter
      (isClosed_le (hc.pow 2) (continuous_const.mul (continuous_norm.pow 2)))
  have hp : 0 ≤ ξ.norm ω x := ξ.norm_nonneg _ _
  have hq : 0 ≤ complexEllipsoidSeminorm b ω σ hσ Q x := apply_nonneg _ _
  constructor
  · apply (sq_le_sq₀ hp hq).mp
    have hd : 0 ≤ δ * (ξ.norm ω x) ^ 2 := mul_nonneg hδ.le (sq_nonneg _)
    nlinarith [hall.1]
  · apply (sq_le_sq₀ hq (mul_nonneg (Real.sqrt_nonneg _) hp)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hd : 0 ≤ δ * (ξ.norm ω x) ^ 2 := mul_nonneg hδ.le (sq_nonneg _)
    nlinarith [hall.2]

/-- Countably many measurable rational tests select an actual ellipsoid at
every infinite place. One countable subfield is required only at infinity. -/
theorem IsMeasurable.exists_complexEllipsoid_choice {ξ : NormFamily S E}
    (hξ : ξ.IsMeasurable) (b : Module.Basis ι K E)
    [hS : S.IsArchimedeanNormalized]
    (σ : ∀ ω : S.Ωinf, (S.ϕ ω.val).Completion →+* ℂ)
    (hσ : ∀ ω x, ‖σ ω x‖ = ‖x‖)
    (hm : ∀ x : K, Measurable (fun ω : S.Ωinf =>
      σ ω (algebraMap K (S.ϕ ω.val).Completion x)))
    (K₀ : Subfield K) [Countable K₀]
    (hK₀ : ∀ ω ∈ S.Ωinf, S.IsDenseSubfieldAt K₀ ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : S.Ωinf → Matrix ι ι (ℚ × ℚ), Measurable (fun ω (i j : ι) => Q ω i j) ∧
      (∀ x : E, Measurable (fun ω : S.Ωinf =>
        complexEllipsoidSeminorm b ω.val (σ ω) (hσ ω) (Q ω)
          ((1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] x))) ∧
      ∀ (ω : S.Ωinf) (x : (S.ϕ ω.val).Completion ⊗[K] E),
        ξ.norm ω.val x ≤ complexEllipsoidSeminorm b ω.val (σ ω) (hσ ω) (Q ω) x ∧
        complexEllipsoidSeminorm b ω.val (σ ω) (hσ ω) (Q ω) x ≤
          Real.sqrt (Fintype.card ι + ε) * ξ.norm ω.val x := by
  classical
  let : Countable (Matrix ι ι (ℚ × ℚ)) :=
    show Countable (ι → ι → ℚ × ℚ) from inferInstance
  obtain ⟨a, ha⟩ := exists_surjective_nat (Matrix ι ι (ℚ × ℚ) × ℚ)
  let p : ℕ → S.Ωinf → Prop := fun n ω => 0 < (a n).2 ∧ ∀ c : ι → K₀,
    (1 + ((a n).2 : ℝ)) *
      (ξ.norm ω.val ((1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c)) ^ 2 ≤
        (complexEllipsoidSeminorm b ω.val (σ ω) (hσ ω) (a n).1
          ((1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c)) ^ 2 ∧
    (complexEllipsoidSeminorm b ω.val (σ ω) (hσ ω) (a n).1
      ((1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c)) ^ 2 ≤
      (Fintype.card ι + ε - ((a n).2 : ℝ)) *
        (ξ.norm ω.val ((1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c)) ^ 2
  have hp (n : ℕ) : MeasurableSet {ω | p n ω} := by
    have ht (c : ι → K₀) : Measurable (fun ω : S.Ωinf =>
        ξ.norm ω.val ((1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c)) :=
      (hξ (basisSubfieldMap b K₀ c)).comp measurable_subtype_coe
    have hc (c : ι → K₀) :=
      measurable_complexEllipsoidSeminorm_rational b σ hσ hm (a n).1
        (basisSubfieldMap b K₀ c)
    simp only [p, Set.ofPred_and, Set.ofPred_forall]
    exact (MeasurableSet.const _).inter
      (MeasurableSet.iInter (fun c =>
        (measurableSet_le (measurable_const.mul ((ht c).pow_const 2))
          ((hc c).pow_const 2)).inter
        (measurableSet_le ((hc c).pow_const 2)
          (measurable_const.mul ((ht c).pow_const 2)))))
  have hex (ω : S.Ωinf) : ∃ n, p n ω := by
    let := hS ω.val ω.property
    obtain ⟨Q, δ, hδ, hQ⟩ := ξ.exists_strict_complexEllipsoidSeminorm
      b ω.val (σ ω) (hσ ω) hε
    obtain ⟨n, hn⟩ := ha (Q, δ)
    refine ⟨n, ?_⟩
    simp only [p, hn]
    exact ⟨hδ, fun c => hQ _⟩
  refine ⟨fun ω => (a (Nat.find (hex ω))).1,
    Measurable.find (f := fun n _ (i j : ι) => (a n).1 i j)
      (fun _ => measurable_const) hp hex, fun x => ?_, fun ω x => ?_⟩
  · exact Measurable.find
      (fun n => measurable_complexEllipsoidSeminorm_rational b σ hσ hm (a n).1 x) hp hex
  · have hs := Nat.find_spec (hex ω)
    exact ξ.complexEllipsoid_bounds_of_dense_tests b ω.val (σ ω) (hσ ω)
      (a (Nat.find (hex ω))).1 K₀ (hK₀ ω.val ω.property) hε
      (by exact_mod_cast hs.1) hs.2 x

/-- The exact local John theorem on the actual completed fibre. This pointwise
producer requires no measurability, countable density or ultrametricity, and
includes rank zero. -/
theorem exists_archimedean_john_innerProductCore [FiniteDimensional K E]
    (ξ : NormFamily S E) (ω : S.Ω) [IsRCLikeNormedField (S.ϕ ω).Completion] :
    letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    ∃ c : InnerProductSpace.Core (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E),
      ∀ x, ξ.norm ω x ≤ Real.sqrt (RCLike.re (c.inner x x)) ∧
        Real.sqrt (RCLike.re (c.inner x x)) ≤
          Real.sqrt (Module.finrank K E) * ξ.norm ω x := by
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  have hn (x : (S.ϕ ω).Completion ⊗[K] E) : ‖x‖ = ξ.norm ω x := rfl
  have hdim : Module.finrank (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E) =
      Module.finrank K E := by
    rw [Module.finrank_eq_card_basis ((Module.finBasis K E).baseChange (S.ϕ ω).Completion),
      Fintype.card_fin]
  obtain ⟨c, hc⟩ := @exists_john_innerProductCore
    (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E) inferInstance
    (ξ.fibreNormedAddCommGroup ω) (ξ.fibreNormedSpace ω) inferInstance
  exact ⟨c, fun x => by simpa only [hdim, hn] using hc x⟩

section GlobalFamily

variable (ξ : NormFamily S E) (b : Module.Basis ι K E)
  (σ : ∀ ω : S.Ωinf, (S.ϕ ω.val).Completion →+* ℂ)
  (hσ : ∀ ω x, ‖σ ω x‖ = ‖x‖)
  (Q : S.Ωinf → Matrix ι ι (ℚ × ℚ))
  (hQ : ∀ (ω : S.Ωinf) (x : (S.ϕ ω.val).Completion ⊗[K] E),
    ξ.norm ω.val x ≤ complexEllipsoidSeminorm b ω.val (σ ω) (hσ ω) (Q ω) x)

/-- Paste separated ellipsoid candidates at infinity with the original finite
norms. The lower bound proves separation on the actual completed fibres. -/
def complexEllipsoidFamily : NormFamily S E := by
  classical
  refine {
    norm := fun ω => if hω : ω ∈ S.Ωinf then
      complexEllipsoidSeminorm b ω (σ ⟨ω, hω⟩) (hσ ⟨ω, hω⟩) (Q ⟨ω, hω⟩)
      else ξ.norm ω
    norm_eq_zero_iff := fun ω x => ?_ }
  by_cases hω : ω ∈ S.Ωinf
  · simp only [dite_eq_left hω]
    constructor
    · intro hx
      apply (ξ.norm_eq_zero_iff ω x).mp
      exact le_antisymm (by simpa only [hx] using hQ ⟨ω, hω⟩ x) (ξ.norm_nonneg ω x)
    · rintro rfl
      exact map_zero _
  · simpa only [dite_eq_right hω] using ξ.norm_eq_zero_iff ω x

theorem complexEllipsoidFamily_norm_of_mem (ω : S.Ω) (hω : ω ∈ S.Ωinf)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ξ.complexEllipsoidFamily b σ hσ Q hQ).norm ω x =
      complexEllipsoidSeminorm b ω (σ ⟨ω, hω⟩) (hσ ⟨ω, hω⟩) (Q ⟨ω, hω⟩) x := by
  classical
  simp only [complexEllipsoidFamily, dite_eq_left hω]

theorem complexEllipsoidFamily_norm_of_not_mem (ω : S.Ω) (hω : ω ∉ S.Ωinf)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ξ.complexEllipsoidFamily b σ hσ Q hQ).norm ω x = ξ.norm ω x := by
  classical
  simp only [complexEllipsoidFamily, dite_eq_right hω]

/-- The construction fixes every finite completed-fibre norm. -/
theorem complexEllipsoidFamily_norm_finite (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ξ.complexEllipsoidFamily b σ hσ Q hQ).norm ω x = ξ.norm ω x :=
  ξ.complexEllipsoidFamily_norm_of_not_mem b σ hσ Q hQ ω (fun hi => hi hω) x

/-- Finite-place ultrametricity is preserved and reflected. -/
theorem complexEllipsoidFamily_isUltrametric_iff :
    (ξ.complexEllipsoidFamily b σ hσ Q hQ).IsUltrametric ↔ ξ.IsUltrametric := by
  constructor <;> intro hu <;> constructor <;> intro ω hω x y
  · simpa only [ξ.complexEllipsoidFamily_norm_finite b σ hσ Q hQ ω hω] using
      hu ω hω x y
  · simpa only [ξ.complexEllipsoidFamily_norm_finite b σ hσ Q hQ ω hω] using
      hu ω hω x y

/-- The pasted norm has the parallelogram identity at every infinite place,
independently of the finite-place triangle inequalities. -/
theorem complexEllipsoidFamily_parallelogram (ω : S.Ω) (hω : ω ∈ S.Ωinf)
    (x y : (S.ϕ ω).Completion ⊗[K] E) :
    (ξ.complexEllipsoidFamily b σ hσ Q hQ).norm ω (x + y) *
        (ξ.complexEllipsoidFamily b σ hσ Q hQ).norm ω (x + y) +
      (ξ.complexEllipsoidFamily b σ hσ Q hQ).norm ω (x - y) *
        (ξ.complexEllipsoidFamily b σ hσ Q hQ).norm ω (x - y) =
      2 * ((ξ.complexEllipsoidFamily b σ hσ Q hQ).norm ω x *
        (ξ.complexEllipsoidFamily b σ hσ Q hQ).norm ω x +
        (ξ.complexEllipsoidFamily b σ hσ Q hQ).norm ω y *
          (ξ.complexEllipsoidFamily b σ hσ Q hQ).norm ω y) := by
  simp only [ξ.complexEllipsoidFamily_norm_of_mem b σ hσ Q hQ ω hω, ← pow_two]
  exact complexEllipsoidSeminorm_parallelogram b ω
    (σ ⟨ω, hω⟩) (hσ ⟨ω, hω⟩) (Q ⟨ω, hω⟩) x y

/-- The ellipsoid norm is induced by a positive definite inner product on the
original completed scalar module, without any finite-place hypothesis. -/
theorem complexEllipsoidFamily_exists_innerProduct
    [hS : S.IsArchimedeanNormalized]
    (ω : S.Ω) (hω : ω ∈ S.Ωinf) :
    letI := hS ω hω
    letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    ∃ c : InnerProductSpace.Core (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E),
      ∀ x, ((ξ.complexEllipsoidFamily b σ hσ Q hQ).norm ω x) ^ 2 =
        RCLike.re (c.inner x x) := by
  let := hS ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let := (ξ.complexEllipsoidFamily b σ hσ Q hQ).fibreNormedAddCommGroup ω
  let := (ξ.complexEllipsoidFamily b σ hσ Q hQ).fibreNormedSpace ω
  apply exists_innerProductCore_iff_innerProductSpaceable.mpr
  exact ⟨ξ.complexEllipsoidFamily_parallelogram b σ hσ Q hQ ω hω⟩

/-- The infinite-place inner products and unchanged finite norms give the
source Hermitian condition whenever the original family is ultrametric. -/
theorem complexEllipsoidFamily_isHermitian
    [hS : S.IsArchimedeanNormalized]
    [hu : ξ.IsUltrametric] :
    (ξ.complexEllipsoidFamily b σ hσ Q hQ).IsHermitian :=
  ⟨(ξ.complexEllipsoidFamily_isUltrametric_iff b σ hσ Q hQ).mpr hu,
    ξ.complexEllipsoidFamily_exists_innerProduct b σ hσ Q hQ⟩

/-- Measurable rational evaluations on the infinite subtype paste with the
original measurable norms across the measurable infinite-place locus. -/
theorem complexEllipsoidFamily_isMeasurable [hξ : ξ.IsMeasurable]
    (hm : ∀ x : E, Measurable (fun ω : S.Ωinf =>
      complexEllipsoidSeminorm b ω.val (σ ω) (hσ ω) (Q ω)
        ((1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] x))) :
    (ξ.complexEllipsoidFamily b σ hσ Q hQ).IsMeasurable := by
  constructor
  intro x
  apply measurable_of_restrict_of_restrict_compl S.measurableSet_Ωinf
  · convert hm x using 1
    ext ω
    exact ξ.complexEllipsoidFamily_norm_of_mem b σ hσ Q hQ ω.val ω.property _
  · convert (hξ x).comp measurable_subtype_coe using 1
    ext ω
    exact ξ.complexEllipsoidFamily_norm_of_not_mem b σ hσ Q hQ ω.val ω.property _

/-- The construction fixes the unique family in rank zero. -/
theorem complexEllipsoidFamily_eq_self_of_subsingleton [Subsingleton E] :
    ξ.complexEllipsoidFamily b σ hσ Q hQ = ξ :=
  Subsingleton.elim _ _

/-- With no infinite places the construction is exactly the original family. -/
theorem complexEllipsoidFamily_eq_self_of_empty_infinity (h : S.Ωinf = ∅) :
    ξ.complexEllipsoidFamily b σ hσ Q hQ = ξ := by
  ext ω x
  exact ξ.complexEllipsoidFamily_norm_of_not_mem b σ hσ Q hQ ω (by simp [h]) x

end GlobalFamily

/-- Every measurable norm family admits a measurable approximation induced by
inner products at infinity. Finite norms are unchanged, so ultrametricity is
preserved and reflected rather than imposed as a hypothesis. -/
theorem IsMeasurable.exists_archimedean_innerProduct_approximation
    [FiniteDimensional K E] {ξ : NormFamily S E} (hξ : ξ.IsMeasurable)
    [hS : S.IsArchimedeanNormalized]
    (K₀ : Subfield K) [Countable K₀]
    (hK₀ : ∀ ω ∈ S.Ωinf, S.IsDenseSubfieldAt K₀ ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : NormFamily S E, η.IsMeasurable ∧
      (∀ ω (hω : ω ∈ S.Ωinf),
        letI := hS ω hω
        letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
        ∃ c : InnerProductSpace.Core (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E),
          ∀ x, (η.norm ω x) ^ 2 = RCLike.re (c.inner x x)) ∧
      (η.IsUltrametric ↔ ξ.IsUltrametric) ∧
      (∀ ω ∈ S.Ωfin, ∀ x, η.norm ω x = ξ.norm ω x) ∧
      ∀ ω ∈ S.Ωinf, ∀ x, ξ.norm ω x ≤ η.norm ω x ∧
        η.norm ω x ≤ Real.sqrt (Module.finrank K E + ε) * ξ.norm ω x := by
  classical
  let b := Module.finBasis K E
  obtain ⟨σ, hσ, hm⟩ := S.exists_measurable_archimedeanComplexEmbedding K₀ hK₀
  obtain ⟨Q, _, hmeas, hbounds⟩ :=
    hξ.exists_complexEllipsoid_choice b σ hσ hm K₀ hK₀ hε
  let hQ := fun ω x => (hbounds ω x).1
  refine ⟨ξ.complexEllipsoidFamily b σ hσ Q hQ,
    ξ.complexEllipsoidFamily_isMeasurable b σ hσ Q hQ hmeas,
    ξ.complexEllipsoidFamily_exists_innerProduct b σ hσ Q hQ,
    ξ.complexEllipsoidFamily_isUltrametric_iff b σ hσ Q hQ,
    ξ.complexEllipsoidFamily_norm_finite b σ hσ Q hQ, fun ω hω x => ?_⟩
  rw [ξ.complexEllipsoidFamily_norm_of_mem b σ hσ Q hQ ω hω]
  simpa only [Fintype.card_fin] using hbounds ⟨ω, hω⟩ x

/-- Chen–Moriwaki, Theorem 4.1.26: a measurable ultrametric norm family admits
a measurable Hermitian approximation with the dimension-sharp John bound.
The common countable subfield is required only at infinite places. The
statement includes rank zero and the empty infinite-place locus. -/
theorem IsMeasurable.exists_hermitian_approximation [FiniteDimensional K E]
    {ξ : NormFamily S E} (hξ : ξ.IsMeasurable) (hu : ξ.IsUltrametric)
    [hS : S.IsArchimedeanNormalized]
    (K₀ : Subfield K) [Countable K₀]
    (hK₀ : ∀ ω ∈ S.Ωinf, S.IsDenseSubfieldAt K₀ ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : NormFamily S E, η.IsMeasurable ∧ η.IsHermitian ∧
      (∀ ω ∈ S.Ωfin, ∀ x, η.norm ω x = ξ.norm ω x) ∧
      ∀ ω ∈ S.Ωinf, ∀ x, ξ.norm ω x ≤ η.norm ω x ∧
        η.norm ω x ≤ Real.sqrt (Module.finrank K E + ε) * ξ.norm ω x := by
  obtain ⟨η, hm, hi, hu', hf, hb⟩ :=
    hξ.exists_archimedean_innerProduct_approximation K₀ hK₀ hε
  exact ⟨η, hm, ⟨hu'.mpr hu, hi⟩, hf, hb⟩

end ArakelovGeometry.NormFamily
