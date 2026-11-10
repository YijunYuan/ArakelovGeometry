/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicStructure.RationalNormalization
public import ArakelovGeometry.AdelicVectorBundle.Basic
public import ArakelovGeometry.Analysis.Examples.Interval.Polytope
import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicVectorBundle.Degree.Height

/-!
# Actual interval factors on the rational adelic curve

The given real scalar completion is identified isometrically with the real
field. Real interval norms are transported on every actual completed vector;
finite fibers retain their original completed coordinate maximum norms.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

open AdelicStructure

/-- The rational embedding into the reals, with the standard absolute value on its source. -/
def rationalRealCast : WithAbs Rat.AbsoluteValue.real →+* ℝ :=
  (Rat.castHom ℝ).comp (WithAbs.equiv Rat.AbsoluteValue.real).toRingHom

/-- The rational embedding preserves the standard absolute value. -/
theorem rationalRealCast_isometry : Isometry rationalRealCast := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  change ‖((x - y).ofAbs : ℝ)‖ = Rat.AbsoluteValue.real (x - y).ofAbs
  rw [Rat.AbsoluteValue.real_eq_abs, Rat.cast_abs, Real.norm_eq_abs]

/-- The extension of the rational embedding to its completion. -/
def rationalRealExtension : Rat.AbsoluteValue.real.Completion →+* ℝ :=
  UniformSpace.Completion.extensionHom rationalRealCast rationalRealCast_isometry.continuous

private theorem rationalRealExtension_isometry : Isometry rationalRealExtension :=
  rationalRealCast_isometry.completion_extension

/-- Every real number is in the image of the completed rational embedding. -/
theorem rationalRealExtension_surjective : Function.Surjective rationalRealExtension := by
  rw [← RingHom.fieldRange_eq_top_iff]
  exact Real.subfield_eq_of_closed rationalRealExtension_isometry.isClosedEmbedding.isClosed_range

/-- The actual scalar completion at the rational real place, with its given norm. -/
def rationalRealCompletionEquiv : Rat.AbsoluteValue.real.Completion ≃+* ℝ :=
  RingEquiv.ofBijective rationalRealExtension
    ⟨rationalRealExtension.injective, rationalRealExtension_surjective⟩

/-- The real identification preserves the original completed scalar norm. -/
theorem rationalRealCompletionEquiv_norm (a : Rat.AbsoluteValue.real.Completion) :
    ‖rationalRealCompletionEquiv a‖ = ‖a‖ := by
  change ‖rationalRealExtension a‖ = ‖a‖
  simpa only [dist_eq_norm, map_zero, sub_zero] using
    rationalRealExtension_isometry.dist_eq a 0

/-- The actual scalar identification has the original rational embedding. -/
theorem rationalRealCompletionEquiv_ratCast (a : ℚ) :
    rationalRealCompletionEquiv (algebraMap ℚ Rat.AbsoluteValue.real.Completion a) = (a : ℝ) :=
  UniformSpace.Completion.extensionHom_coe rationalRealCast rationalRealCast_isometry.continuous
    (WithAbs.toAbs Rat.AbsoluteValue.real a)

/-- Real coordinates of the actual completed standard rational vector space. -/
def rationalRealCompletedCoordinates (n : ℕ)
    (z : Rat.AbsoluteValue.real.Completion ⊗[ℚ] (Fin n → ℚ)) : Fin n → ℝ :=
  fun i => rationalRealCompletionEquiv
    (((Pi.basisFun ℚ (Fin n)).baseChange Rat.AbsoluteValue.real.Completion).equivFun z i)

theorem rationalRealCompletedCoordinates_add (n : ℕ)
    (z w : Rat.AbsoluteValue.real.Completion ⊗[ℚ] (Fin n → ℚ)) :
    rationalRealCompletedCoordinates n (z + w) =
      rationalRealCompletedCoordinates n z + rationalRealCompletedCoordinates n w := by
  ext i
  simp only [rationalRealCompletedCoordinates, map_add, Pi.add_apply]

theorem rationalRealCompletedCoordinates_smul (n : ℕ) (a : Rat.AbsoluteValue.real.Completion)
    (z : Rat.AbsoluteValue.real.Completion ⊗[ℚ] (Fin n → ℚ)) :
    rationalRealCompletedCoordinates n (a • z) =
      rationalRealCompletionEquiv a • rationalRealCompletedCoordinates n z := by
  ext i
  simp only [rationalRealCompletedCoordinates, map_smul, Pi.smul_apply, smul_eq_mul, map_mul]

/-- On every original rational vector the real coordinates are the usual rational casts. -/
theorem rationalRealCompletedCoordinates_rational (n : ℕ) (x : Fin n → ℚ) :
    rationalRealCompletedCoordinates n
      ((1 : Rat.AbsoluteValue.real.Completion) ⊗ₜ[ℚ] x) = fun i => (x i : ℝ) := by
  ext i
  change rationalRealCompletionEquiv
    (((Pi.basisFun ℚ (Fin n)).baseChange Rat.AbsoluteValue.real.Completion).repr
      (1 ⊗ₜ[ℚ] x) i) = _
  rw [Module.Basis.baseChange_repr_tmul]
  change rationalRealCompletionEquiv ((x i) • (1 : Rat.AbsoluteValue.real.Completion)) = _
  rw [Algebra.smul_def, mul_one]
  exact rationalRealCompletionEquiv_ratCast (x i)

theorem rationalRealCompletedCoordinates_eq_zero_iff (n : ℕ)
    (z : Rat.AbsoluteValue.real.Completion ⊗[ℚ] (Fin n → ℚ)) :
    rationalRealCompletedCoordinates n z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    apply ((Pi.basisFun ℚ (Fin n)).baseChange Rat.AbsoluteValue.real.Completion).equivFun.injective
    ext i
    apply rationalRealCompletionEquiv.injective
    simpa only [rationalRealCompletedCoordinates, Pi.zero_apply, map_zero] using congrFun hz i
  · rintro rfl
    ext i
    simp only [rationalRealCompletedCoordinates, map_zero, Pi.zero_apply]

theorem rationalRealCompletedCoordinates_norm (n : ℕ)
    (z : Rat.AbsoluteValue.real.Completion ⊗[ℚ] (Fin n → ℚ)) :
    ‖rationalRealCompletedCoordinates n z‖ =
      ‖((Pi.basisFun ℚ (Fin n)).baseChange Rat.AbsoluteValue.real.Completion).equivFun z‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    rw [rationalRealCompletedCoordinates, rationalRealCompletionEquiv_norm]
    exact norm_le_pi_norm _ _
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    rw [← rationalRealCompletionEquiv_norm]
    exact norm_le_pi_norm (rationalRealCompletedCoordinates n z) i

/-- Transport a real seminorm using the actual original completed scalar action. -/
def rationalRealFibreSeminorm (n : ℕ) (p : Seminorm ℝ (Fin n → ℝ)) :
    Seminorm Rat.AbsoluteValue.real.Completion
      (Rat.AbsoluteValue.real.Completion ⊗[ℚ] (Fin n → ℚ)) :=
  Seminorm.of (fun z => p (rationalRealCompletedCoordinates n z))
    (by intro z w; rw [rationalRealCompletedCoordinates_add]; exact map_add_le_add _ _ _)
    (by
      intro a z
      rw [rationalRealCompletedCoordinates_smul, map_smul_eq_mul,
        rationalRealCompletionEquiv_norm])

theorem rationalRealFibreSeminorm_apply (n : ℕ) (p : Seminorm ℝ (Fin n → ℝ))
    (z : Rat.AbsoluteValue.real.Completion ⊗[ℚ] (Fin n → ℚ)) :
    rationalRealFibreSeminorm n p z = p (rationalRealCompletedCoordinates n z) := rfl

/-- An actual norm family with unchanged finite fibers and a prescribed separating real norm. -/
def rationalRealModifiedFamily (n : ℕ) (p : Seminorm ℝ (Fin n → ℝ))
    (hp : ∀ x, p x = 0 ↔ x = 0) : NormFamily rationalAdelicStructure (Fin n → ℚ) where
  norm ω := match ω with
    | .inl q => (NormFamily.ofBasis rationalAdelicStructure (Fin n → ℚ)
        (Pi.basisFun ℚ (Fin n))).norm (.inl q)
    | .inr _ => rationalRealFibreSeminorm n p
  norm_eq_zero_iff ω z := by
    cases ω with
    | inl q => exact NormFamily.norm_eq_zero_iff _ _ _
    | inr u =>
      cases u
      change p (rationalRealCompletedCoordinates n z) = 0 ↔ z = 0
      exact (hp _).trans (rationalRealCompletedCoordinates_eq_zero_iff n z)

theorem rationalRealModifiedFamily_norm_prime (n : ℕ) (p : Seminorm ℝ (Fin n → ℝ))
    (hp : ∀ x, p x = 0 ↔ x = 0) (q : Nat.Primes)
    (z : (rationalAdelicStructure.ϕ (.inl q)).Completion ⊗[ℚ] (Fin n → ℚ)) :
    (rationalRealModifiedFamily n p hp).norm (.inl q) z =
      (NormFamily.ofBasis rationalAdelicStructure (Fin n → ℚ)
        (Pi.basisFun ℚ (Fin n))).norm (.inl q) z := rfl

theorem rationalRealModifiedFamily_norm_infinite (n : ℕ) (p : Seminorm ℝ (Fin n → ℝ))
    (hp : ∀ x, p x = 0 ↔ x = 0)
    (z : Rat.AbsoluteValue.real.Completion ⊗[ℚ] (Fin n → ℚ)) :
    (rationalRealModifiedFamily n p hp).norm (.inr ()) z =
      p (rationalRealCompletedCoordinates n z) := rfl

/-- Every finite completed fiber is the original ultrametric coordinate norm. -/
theorem rationalRealModifiedFamily_isUltrametric (n : ℕ) (p : Seminorm ℝ (Fin n → ℝ))
    (hp : ∀ x, p x = 0 ↔ x = 0) : (rationalRealModifiedFamily n p hp).IsUltrametric := by
  intro ω hω x y
  cases ω with
  | inl q =>
      change (NormFamily.ofBasis rationalAdelicStructure (Fin n → ℚ)
          (Pi.basisFun ℚ (Fin n))).norm (.inl q) (x + y) ≤
        max ((NormFamily.ofBasis rationalAdelicStructure (Fin n → ℚ)
          (Pi.basisFun ℚ (Fin n))).norm (.inl q) x)
          ((NormFamily.ofBasis rationalAdelicStructure (Fin n → ℚ)
            (Pi.basisFun ℚ (Fin n))).norm (.inl q) y)
      have h := NormFamily.ofBasisMixed_isUltrametric
        (S := rationalAdelicStructure) (Pi.basisFun ℚ (Fin n)) (.inl q) hω x y
      simpa only [NormFamily.ofBasisMixed_norm_of_finite _ _ hω] using h
  | inr u =>
      cases u
      exact (rationalAdelicStructure_infinite_mem_inf hω).elim

/-- An explicit real comparison gives domination of the actual family and its actual dual. -/
theorem rationalRealModifiedFamily_isDominated (n : ℕ) (p : Seminorm ℝ (Fin n → ℝ))
    (hp : ∀ x, p x = 0 ↔ x = 0) (C : ℝ) (hC : 1 ≤ C)
    (hlo : ∀ x, ‖x‖ ≤ p x) (hhi : ∀ x, p x ≤ C * ‖x‖) :
    (rationalRealModifiedFamily n p hp).IsDominated := by
  let ξ := rationalRealModifiedFamily n p hp
  let β := NormFamily.ofBasis rationalAdelicStructure (Fin n → ℚ) (Pi.basisFun ℚ (Fin n))
  let D := rationalAdelicStructure.Ωinf.indicator (fun _ => Real.log C)
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hD0 (ω : rationalAdelicStructure.Ω) : 0 ≤ D ω :=
    Set.indicator_nonneg (fun _ _ => Real.log_nonneg hC) ω
  have hDI : Integrable D rationalAdelicStructure.v :=
    (integrable_indicator_iff rationalAdelicStructure.measurableSet_Ωinf).mpr
      (integrableOn_const (by rw [rationalAdelicStructure_v_Ωinf]; exact ENNReal.one_ne_top))
  have hβ : β.IsDominated := NormFamily.ofBasis_isDominated_of_measure_lt_top
    (Pi.basisFun ℚ (Fin n)) (by rw [rationalAdelicStructure_v_Ωinf]; exact ENNReal.one_lt_top)
  apply hβ.of_localDist
  refine ⟨D, hDI, Filter.Eventually.of_forall (fun ω => ?_)⟩
  apply (β.localDist_le_iff_norm_le ξ ω (hD0 ω)).mpr
  intro z
  cases ω with
  | inl q =>
      have hq : Sum.inl q ∉ rationalAdelicStructure.Ωinf :=
        fun h => h (rationalAdelicStructure_prime_mem_fin q)
      simp only [D, Set.indicator_of_notMem hq, Real.exp_zero, one_mul]
      exact ⟨le_rfl, le_rfl⟩
  | inr u =>
      cases u
      rw [show D (.inr ()) = Real.log C from
        Set.indicator_of_mem rationalAdelicStructure_infinite_mem_inf _, Real.exp_log hC0]
      have he : β.norm (.inr ()) z = ‖rationalRealCompletedCoordinates n z‖ := by
        change (NormFamily.ofBasis rationalAdelicStructure (Fin n → ℚ)
          (Pi.basisFun ℚ (Fin n))).norm (.inr ()) z = _
        rw [NormFamily.ofBasis_norm]
        exact (rationalRealCompletedCoordinates_norm n z).symm
      change β.norm (.inr ()) z ≤ C * p (rationalRealCompletedCoordinates n z) ∧
        p (rationalRealCompletedCoordinates n z) ≤ C * β.norm (.inr ()) z
      rw [he]
      exact ⟨(hlo _).trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (apply_nonneg p _)), hhi _⟩

/-- The actual completed interval factor of rational dimension two. -/
def rationalIntervalPlaneFamily : NormFamily rationalAdelicStructure (Fin 2 → ℚ) :=
  rationalRealModifiedFamily 2 intervalSeminorm₂ intervalSeminorm₂_eq_zero_iff

/-- The actual completed interval factor of rational dimension three. -/
def rationalIntervalThreeFamily : NormFamily rationalAdelicStructure (Fin 3 → ℚ) :=
  rationalRealModifiedFamily 3 intervalSeminorm₃ intervalSeminorm₃_eq_zero_iff

theorem rationalIntervalPlaneFamily_norm_prime (q : Nat.Primes)
    (z : (rationalAdelicStructure.ϕ (.inl q)).Completion ⊗[ℚ] (Fin 2 → ℚ)) :
    rationalIntervalPlaneFamily.norm (.inl q) z =
      ‖((Pi.basisFun ℚ (Fin 2)).baseChange
        (rationalAdelicStructure.ϕ (.inl q)).Completion).equivFun z‖ :=
  NormFamily.ofBasis_norm rationalAdelicStructure (Fin 2 → ℚ) (Pi.basisFun ℚ (Fin 2)) _ z

theorem rationalIntervalThreeFamily_norm_prime (q : Nat.Primes)
    (z : (rationalAdelicStructure.ϕ (.inl q)).Completion ⊗[ℚ] (Fin 3 → ℚ)) :
    rationalIntervalThreeFamily.norm (.inl q) z =
      ‖((Pi.basisFun ℚ (Fin 3)).baseChange
        (rationalAdelicStructure.ϕ (.inl q)).Completion).equivFun z‖ :=
  NormFamily.ofBasis_norm rationalAdelicStructure (Fin 3 → ℚ) (Pi.basisFun ℚ (Fin 3)) _ z

theorem rationalIntervalPlaneFamily_norm_infinite
    (z : Rat.AbsoluteValue.real.Completion ⊗[ℚ] (Fin 2 → ℚ)) :
    rationalIntervalPlaneFamily.norm (.inr ()) z =
      intervalSeminorm₂ (rationalRealCompletedCoordinates 2 z) := rfl

theorem rationalIntervalThreeFamily_norm_infinite
    (z : Rat.AbsoluteValue.real.Completion ⊗[ℚ] (Fin 3 → ℚ)) :
    rationalIntervalThreeFamily.norm (.inr ()) z =
      intervalSeminorm₃ (rationalRealCompletedCoordinates 3 z) := rfl

private theorem intervalPlanePiNormBounds (x : Fin 2 → ℝ) :
    ‖x‖ ≤ intervalSeminorm₂ x ∧ intervalSeminorm₂ x ≤ 2 * ‖x‖ := by
  constructor
  · apply (pi_norm_le_iff_of_nonneg (apply_nonneg intervalSeminorm₂ x)).mpr
    intro i
    simpa only [Real.norm_eq_abs] using abs_coordinate_le_intervalSeminorm₂ x i
  · have h0 := norm_le_pi_norm x 0
    have h1 := norm_le_pi_norm x 1
    simp only [Real.norm_eq_abs] at h0 h1
    exact (intervalSeminorm₂_le_sum x).trans (by linarith)

private theorem intervalThreePiNormBounds (x : Fin 3 → ℝ) :
    ‖x‖ ≤ intervalSeminorm₃ x ∧ intervalSeminorm₃ x ≤ 3 * ‖x‖ := by
  constructor
  · apply (pi_norm_le_iff_of_nonneg (apply_nonneg intervalSeminorm₃ x)).mpr
    intro i
    simpa only [Real.norm_eq_abs] using abs_coordinate_le_intervalSeminorm₃ x i
  · have h0 := norm_le_pi_norm x 0
    have h1 := norm_le_pi_norm x 1
    have h2 := norm_le_pi_norm x 2
    simp only [Real.norm_eq_abs] at h0 h1 h2
    exact (intervalSeminorm₃_le_sum x).trans (by linarith)

theorem rationalIntervalPlaneFamily_isDominated : rationalIntervalPlaneFamily.IsDominated :=
  rationalRealModifiedFamily_isDominated 2 intervalSeminorm₂ intervalSeminorm₂_eq_zero_iff
    2 (by norm_num) (fun x => (intervalPlanePiNormBounds x).1)
    (fun x => (intervalPlanePiNormBounds x).2)

theorem rationalIntervalThreeFamily_isDominated : rationalIntervalThreeFamily.IsDominated :=
  rationalRealModifiedFamily_isDominated 3 intervalSeminorm₃ intervalSeminorm₃_eq_zero_iff
    3 (by norm_num) (fun x => (intervalThreePiNormBounds x).1)
    (fun x => (intervalThreePiNormBounds x).2)

/-- Both measurability clauses and actual dual domination belong to this rational plane bundle. -/
def rationalIntervalPlaneBundle : AdelicVectorBundle rationalAdelicStructure (Fin 2 → ℚ) where
  toNormFamily := rationalIntervalPlaneFamily
  isMeasurable := rationalIntervalPlaneFamily.isMeasurable_of_discrete
  dual_isMeasurable := rationalIntervalPlaneFamily.dual.isMeasurable_of_discrete
  isDominated := rationalIntervalPlaneFamily_isDominated

/-- The rational rank-three interval bundle on the actual normalized adelic curve. -/
def rationalIntervalThreeBundle : AdelicVectorBundle rationalAdelicStructure (Fin 3 → ℚ) where
  toNormFamily := rationalIntervalThreeFamily
  isMeasurable := rationalIntervalThreeFamily.isMeasurable_of_discrete
  dual_isMeasurable := rationalIntervalThreeFamily.dual.isMeasurable_of_discrete
  isDominated := rationalIntervalThreeFamily_isDominated

theorem rationalIntervalPlaneBundle_toNormFamily :
    rationalIntervalPlaneBundle.toNormFamily = rationalIntervalPlaneFamily := rfl

theorem rationalIntervalThreeBundle_toNormFamily :
    rationalIntervalThreeBundle.toNormFamily = rationalIntervalThreeFamily := rfl

end

end ArakelovGeometry
