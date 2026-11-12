/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicStructure.TrivialPlace
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Basic
public import Mathlib.NumberTheory.NumberField.Basic

import Mathlib.CategoryTheory.Category.Init

/-!
# Upper and lower domination do not imply domination

The source's infinite counting-place example (Remark 4.1.4) is specialized
to `ℚ`. Norms use the genuine trivial completed tensor fibres and their
canonical operator duals.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.CountingDominationCounterexample

noncomputable section

open AdelicStructure

-- Use the same zero-decidability datum as the existing canonical
-- trivial-completion equivalences, rather than a second rational instance.
local instance : DecidablePred (fun x : ℚ ↦ x = 0) :=
  fun _ ↦ Classical.propDecidable _

open Classical in
/-- The actual proper trivial adelic structure on the infinite rational
counting space. -/
abbrev countingCurve : AdelicStructure ℚ where
  Ω := ℚ
  A := inferInstance
  v := Measure.count
  ϕ := fun _ ↦ AbsoluteValue.trivial
  measurable_log := (trivialAdelicStructure ℚ ℚ Measure.count).measurable_log
  integrable_log := (trivialAdelicStructure ℚ ℚ Measure.count).integrable_log

/-- The transparent counting curve is exactly the existing canonical
trivial adelic structure, including its original measure. -/
theorem countingCurve_eq_trivialAdelicStructure :
    countingCurve = trivialAdelicStructure ℚ ℚ Measure.count := rfl

instance countingCurve_isProper : countingCurve.IsProper := by
  change (trivialAdelicStructure ℚ ℚ Measure.count).IsProper
  infer_instance

instance countingCurve_discreteMeasurableSpace :
    DiscreteMeasurableSpace countingCurve.Ω := by
  change DiscreteMeasurableSpace ℚ
  infer_instance

/-- The rational plane underlying the source example. -/
abbrev Plane := ℚ × ℚ

/-- The source's varying cheap-line norm before canonical completion transport. -/
def rawNorm (a : ℚ) (x : Plane) : ℝ :=
  if x = 0 then 0 else if x.2 = a * x.1 then 1 / 2 else 1

@[simp]
theorem rawNorm_zero (a : ℚ) : rawNorm a 0 = 0 := by
  simp [rawNorm]

theorem rawNorm_le_one (a : ℚ) (x : Plane) : rawNorm a x ≤ 1 := by
  simp only [rawNorm]
  split_ifs <;> norm_num

theorem half_le_rawNorm (a : ℚ) {x : Plane} (hx : x ≠ 0) :
    (1 / 2 : ℝ) ≤ rawNorm a x := by
  simp only [rawNorm, ite_eq_right hx]
  split_ifs <;> norm_num

theorem rawNorm_eq_zero_iff (a : ℚ) (x : Plane) :
    rawNorm a x = 0 ↔ x = 0 := by
  by_cases hx : x = 0
  · simp [hx]
  · simp only [rawNorm, ite_eq_right hx]
    split_ifs <;> norm_num [hx]

/-- The weighted coordinate norm satisfies the triangle inequality. -/
theorem rawNorm_add_le (a : ℚ) (x y : Plane) :
    rawNorm a (x + y) ≤ rawNorm a x + rawNorm a y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  have hsum := rawNorm_le_one a (x + y)
  have hleft := half_le_rawNorm a hx
  have hright := half_le_rawNorm a hy
  linarith

open Classical in
private theorem rawNorm_smul (a c : ℚ) (x : Plane) :
    rawNorm a (c • x) = (AbsoluteValue.trivial : AbsoluteValue ℚ ℝ) c * rawNorm a x := by
  by_cases hc : c = 0
  · simp [hc]
  rw [AbsoluteValue.trivial_apply hc, one_mul]
  by_cases hx : x = 0
  · simp [hx]
  have hcx : c • x ≠ 0 := (smul_eq_zero_iff_right hc).not.mpr hx
  have hline : c * x.2 = a * (c * x.1) ↔ x.2 = a * x.1 := by
    rw [mul_left_comm a c x.1]
    exact ⟨mul_left_cancel₀ hc, fun h ↦ congrArg (c * ·) h⟩
  simp only [rawNorm, ite_eq_right hcx, ite_eq_right hx, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, hline]

open Classical in
/-- The source norm is a genuine scalar-compatible separating seminorm
over the original trivially normed rational field. -/
def localSeminorm (a : ℚ) :
    Seminorm (WithAbs (AbsoluteValue.trivial : AbsoluteValue ℚ ℝ)) Plane :=
  Seminorm.of (rawNorm a) (rawNorm_add_le a) (by
    intro c x
    change rawNorm a (c.ofAbs • x) = ‖c‖ * rawNorm a x
    rw [WithAbs.norm_eq_apply_ofAbs]
    exact rawNorm_smul a c.ofAbs x)

open Classical in
@[simp]
theorem localSeminorm_apply (a : ℚ) (x : Plane) :
    localSeminorm a x = rawNorm a x := rfl

open Classical in
/-- The actual completed norm family, transported through the existing
canonical trivial-completion tensor equivalence at every counting place. -/
def normFamily : NormFamily countingCurve Plane where
  norm a := by
    change Seminorm (AbsoluteValue.trivial : AbsoluteValue ℚ ℝ).Completion
      ((AbsoluteValue.trivial : AbsoluteValue ℚ ℝ).Completion ⊗[ℚ] Plane)
    exact Seminorm.of (fun z ↦ localSeminorm a (trivialCompletedTensorEquiv ℚ Plane z))
      (by
        intro x y
        rw [map_add]
        exact map_add_le_add (localSeminorm a) _ _)
      (by
        intro c z
        rw [trivialCompletedTensorEquiv_smul]
        change localSeminorm a
          (WithAbs.toAbs (AbsoluteValue.trivial : AbsoluteValue ℚ ℝ)
            (trivialCompletionAlgEquiv ℚ c) • trivialCompletedTensorEquiv ℚ Plane z) = _
        rw [map_smul_eq_mul, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_toAbs,
          ← norm_trivialCompletion ℚ c])
  norm_eq_zero_iff a z := by
    change rawNorm a (trivialCompletedTensorEquiv ℚ Plane z) = 0 ↔ z = 0
    rw [rawNorm_eq_zero_iff, LinearEquiv.map_eq_zero_iff]

open Classical in
/-- The norm formula on every actual completed vector, without a
rational-pure-tensor restriction. -/
theorem normFamily_norm (a : countingCurve.Ω)
    (z : (countingCurve.ϕ a).Completion ⊗[ℚ] Plane) :
    normFamily.norm a z = rawNorm a (trivialCompletedTensorEquiv ℚ Plane z) := rfl

open Classical in
@[simp]
theorem normFamily_norm_rational (a : countingCurve.Ω) (x : Plane) :
    normFamily.norm a ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] x) =
      rawNorm a x := by
  rw [normFamily_norm, trivialCompletedTensorEquiv_one_tmul]

open Classical in
/-- At a nonzero rational vector, the genuine logarithmic norm is the
indicator of its unique possible cheap-line place. -/
theorem logNorm_eq (a : countingCurve.Ω) {x : Plane} (hx : x ≠ 0) :
    normFamily.logNorm x a =
      if x.2 = a * x.1 then -Real.log 2 else 0 := by
  have hn : normFamily.logNorm x a = Real.log (rawNorm a x) :=
    congrArg Real.log (normFamily_norm_rational a x)
  rw [hn]
  simp only [rawNorm, ite_eq_right hx]
  split_ifs
  · rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  · exact Real.log_one

/-- Every rational logarithmic norm is genuinely integrable against
infinite counting measure: its support is contained in one singleton. -/
theorem integrable_logNorm {x : Plane} (hx : x ≠ 0) :
    Integrable (normFamily.logNorm x) countingCurve.v := by
  apply integrable_count_iff.mpr
  apply summable_of_ne_finset_zero (s := {x.2 / x.1})
  intro a ha
  have hline : x.2 ≠ a * x.1 := by
    intro h
    by_cases hx1 : x.1 = 0
    · have hx2 : x.2 = 0 := by simpa only [hx1, mul_zero] using h
      exact hx (Prod.ext hx1 hx2)
    · have hae : x.2 / x.1 = a := (div_eq_iff hx1).mpr h
      exact ha (by simpa only [Finset.mem_singleton] using hae.symm)
  rw [logNorm_eq a hx, ite_eq_right hline]
  exact _root_.norm_zero

/-- The primal norm family is upper dominated by its actual logarithmic
norm itself, whose integrability is produced for every nonzero vector. -/
theorem isUpperDominated : normFamily.IsUpperDominated := by
  constructor
  intro x hx
  exact ⟨normFamily.logNorm x, integrable_logNorm hx,
    Filter.Eventually.of_forall fun _ ↦ le_rfl⟩

/-- The same produced logarithmic norm gives lower domination. -/
theorem isLowerDominated : normFamily.IsLowerDominated := by
  constructor
  intro x hx
  exact ⟨normFamily.logNorm x, integrable_logNorm hx,
    Filter.Eventually.of_forall fun _ ↦ le_rfl⟩

open Classical in
/-- Every vector of every actual trivial completed tensor fibre is a
rational pure tensor, through the existing canonical equivalence. -/
theorem completed_eq_one_tmul {F : Type*} [AddCommGroup F] [Module ℚ F]
    (a : countingCurve.Ω) (z : (countingCurve.ϕ a).Completion ⊗[ℚ] F) :
    z = (1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ]
      trivialCompletedTensorEquiv ℚ F z := by
  apply (trivialCompletedTensorEquiv ℚ F).injective
  rw [trivialCompletedTensorEquiv_one_tmul]

private theorem trivial_apply_le_one (b : ℚ) :
    (AbsoluteValue.trivial : AbsoluteValue ℚ ℝ) b ≤ 1 := by
  by_cases hb : b = 0
  · simp [hb]
  · rw [AbsoluteValue.trivial_apply hb]

private theorem eval_le_rawNorm_of_annihilates (a : ℚ) (ℓ : Module.Dual ℚ Plane)
    (hcheap : ℓ ((1, a) : Plane) = 0) (x : Plane) :
    (AbsoluteValue.trivial : AbsoluteValue ℚ ℝ) (ℓ x) ≤ rawNorm a x := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hline : x.2 = a * x.1
  · have he : x = x.1 • ((1, a) : Plane) := by
      ext <;> simp [smul_eq_mul, hline, mul_comm]
    have hval : ℓ x = 0 := by rw [he, map_smul, hcheap, smul_zero]
    rw [hval, map_zero]
    exact apply_nonneg (localSeminorm a) x
  · rw [rawNorm, ite_eq_right hx, ite_eq_right hline]
    exact trivial_apply_le_one (ℓ x)

open Classical in
private theorem dual_norm_le_of_rational_bound (a : countingCurve.Ω)
    (ℓ : Module.Dual ℚ Plane) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : Plane, (AbsoluteValue.trivial : AbsoluteValue ℚ ℝ) (ℓ x) ≤ C * rawNorm a x) :
    normFamily.dual.norm a ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] ℓ) ≤ C := by
  apply normFamily.dual_norm_le a _ hC
  intro z
  have hz := completed_eq_one_tmul a z
  have heval :
      ‖dualBaseChangeEquiv ℚ (countingCurve.ϕ a).Completion Plane
        ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] ℓ) z‖ =
      (AbsoluteValue.trivial : AbsoluteValue ℚ ℝ)
        (ℓ (trivialCompletedTensorEquiv ℚ Plane z)) := by
    rw [hz, dualBaseChangeEquiv_tmul_apply_tmul, one_mul, one_mul,
      norm_trivialCompletion ℚ, trivialCompletionAlgEquiv_algebraMap,
      trivialCompletedTensorEquiv_one_tmul]
  calc
    _ = (AbsoluteValue.trivial : AbsoluteValue ℚ ℝ)
        (ℓ (trivialCompletedTensorEquiv ℚ Plane z)) := heval
    _ ≤ C * rawNorm a (trivialCompletedTensorEquiv ℚ Plane z) := h _
    _ = C * normFamily.norm a z := congrArg (C * ·) (normFamily_norm a z).symm

open Classical in
private theorem one_le_dual_norm_of_ne_zero (a : countingCurve.Ω)
    (ℓ : Module.Dual ℚ Plane) (hℓ : ℓ ≠ 0) :
    1 ≤ normFamily.dual.norm a ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] ℓ) := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hℓ
  have hval : ℓ x ≠ 0 := by simpa only [LinearMap.zero_apply] using hx
  have he := normFamily.norm_dual_tmul_apply_tmul_le a
    (1 : (countingCurve.ϕ a).Completion) 1 ℓ x
  have heval : ‖(1 : (countingCurve.ϕ a).Completion) * 1 *
      algebraMap ℚ (countingCurve.ϕ a).Completion (ℓ x)‖ = 1 := by
    rw [one_mul, one_mul, norm_trivialCompletion ℚ, trivialCompletionAlgEquiv_algebraMap,
      AbsoluteValue.trivial_apply hval]
  have hn := normFamily_norm_rational a x
  rw [heval, hn] at he
  exact he.trans (by
    have hmul := mul_le_mul_of_nonneg_left (rawNorm_le_one a x)
      (normFamily.dual.norm_nonneg a ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] ℓ))
    simpa only [mul_one] using hmul)

open Classical in
/-- The actual operator dual norm on every rational functional: zero
at zero, one on the cheap-line annihilator, and two otherwise. -/
theorem dual_norm_rational (a : countingCurve.Ω) (ℓ : Module.Dual ℚ Plane) :
    normFamily.dual.norm a ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] ℓ) =
      if ℓ = 0 then 0 else if ℓ ((1, a) : Plane) = 0 then 1 else 2 := by
  by_cases hℓ : ℓ = 0
  · subst ℓ
    simp
  rw [ite_eq_right hℓ]
  by_cases hcheap : ℓ ((1, a) : Plane) = 0
  · rw [ite_eq_left hcheap]
    apply le_antisymm
    · apply dual_norm_le_of_rational_bound a ℓ zero_le_one
      intro x
      simpa only [one_mul] using eval_le_rawNorm_of_annihilates a ℓ hcheap x
    · exact one_le_dual_norm_of_ne_zero a ℓ hℓ
  · rw [ite_eq_right hcheap]
    apply le_antisymm
    · apply dual_norm_le_of_rational_bound a ℓ (by norm_num)
      intro x
      by_cases hx : x = 0
      · simp [hx]
      have hp := half_le_rawNorm a hx
      have hs := trivial_apply_le_one (ℓ x)
      linarith
    · have he := normFamily.norm_dual_tmul_apply_tmul_le a
        (1 : (countingCurve.ϕ a).Completion) 1 ℓ ((1, a) : Plane)
      have heval : ‖(1 : (countingCurve.ϕ a).Completion) * 1 *
          algebraMap ℚ (countingCurve.ϕ a).Completion (ℓ ((1, a) : Plane))‖ = 1 := by
        rw [one_mul, one_mul, norm_trivialCompletion ℚ, trivialCompletionAlgEquiv_algebraMap,
          AbsoluteValue.trivial_apply hcheap]
      have hn : normFamily.norm a
          ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] ((1, a) : Plane)) = (1 / 2 : ℝ) := by
        rw [normFamily_norm_rational]
        simp [rawNorm]
      rw [heval, hn] at he
      linarith

open Classical in
/-- The operator formula covers every actual completed functional, using
its canonical rational inverse and the proved all-vector evaluation bounds. -/
theorem dual_norm_completed (a : countingCurve.Ω)
    (z : (countingCurve.ϕ a).Completion ⊗[ℚ] Module.Dual ℚ Plane) :
    normFamily.dual.norm a z =
      if trivialCompletedTensorEquiv ℚ (Module.Dual ℚ Plane) z = 0 then 0
      else if trivialCompletedTensorEquiv ℚ (Module.Dual ℚ Plane) z ((1, a) : Plane) = 0
        then 1 else 2 := by
  calc
    _ = normFamily.dual.norm a
        ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ]
          trivialCompletedTensorEquiv ℚ (Module.Dual ℚ Plane) z) :=
      congrArg (normFamily.dual.norm a) (completed_eq_one_tmul a z)
    _ = _ := dual_norm_rational a _

/-- The canonical coordinate pairing identifies each rational coefficient
pair with its actual algebraic functional. -/
def coordinateFunctional (u v : ℚ) : Module.Dual ℚ Plane :=
  u • LinearMap.fst ℚ ℚ ℚ + v • LinearMap.snd ℚ ℚ ℚ

@[simp]
theorem coordinateFunctional_apply (u v : ℚ) (x : Plane) :
    coordinateFunctional u v x = u * x.1 + v * x.2 := rfl

theorem coordinateFunctional_eq_zero_iff (u v : ℚ) :
    coordinateFunctional u v = 0 ↔ (u, v) = ((0, 0) : Plane) := by
  constructor
  · intro h
    have hu := congrArg (fun ℓ : Module.Dual ℚ Plane ↦ ℓ ((1, 0) : Plane)) h
    have hv := congrArg (fun ℓ : Module.Dual ℚ Plane ↦ ℓ ((0, 1) : Plane)) h
    simp only [coordinateFunctional_apply, mul_one, mul_zero, add_zero, zero_add,
      LinearMap.zero_apply] at hu hv
    exact Prod.ext hu hv
  · intro h
    have hu : u = 0 := congrArg Prod.fst h
    have hv : v = 0 := congrArg Prod.snd h
    simp [coordinateFunctional, hu, hv]

open Classical in
/-- The source's coefficient-pair dual formula follows from the actual
completed operator norm, using the canonical coordinate pairing. -/
theorem dual_norm_coordinates (a : countingCurve.Ω) (u v : ℚ) :
    normFamily.dual.norm a
      ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] coordinateFunctional u v) =
      if (u, v) = ((0, 0) : Plane) then 0 else if u + a * v = 0 then 1 else 2 := by
  rw [dual_norm_rational, coordinateFunctional_eq_zero_iff]
  have he : coordinateFunctional u v ((1, a) : Plane) = u + a * v := by
    simp only [coordinateFunctional_apply, mul_one, mul_comm v a]
  rw [he]
  split_ifs <;> rfl

/-- A concrete nonzero rational functional whose actual completed
operator norm will be two at every counting place. -/
def firstCoordinate : Module.Dual ℚ Plane := LinearMap.fst ℚ ℚ ℚ

theorem firstCoordinate_ne_zero : firstCoordinate ≠ 0 := by
  intro h
  have he := congrArg (fun ℓ : Module.Dual ℚ Plane ↦ ℓ ((1, 0) : Plane)) h
  norm_num [firstCoordinate] at he

open Classical in
/-- The non-domination witness is an actual algebraic functional and
its norm is the canonical completed operator dual norm. -/
theorem firstCoordinate_dual_norm (a : countingCurve.Ω) :
    normFamily.dual.norm a
      ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] firstCoordinate) = 2 := by
  have he : firstCoordinate ((1, a) : Plane) ≠ 0 := by simp [firstCoordinate]
  rw [dual_norm_rational, ite_eq_right firstCoordinate_ne_zero, ite_eq_right he]

/-- Its genuine rational logarithmic dual norm is the positive constant log two. -/
theorem firstCoordinate_dual_logNorm (a : countingCurve.Ω) :
    normFamily.dual.logNorm firstCoordinate a = Real.log 2 :=
  congrArg Real.log (firstCoordinate_dual_norm a)

/-- Infinite counting measure admits no integrable upper envelope of
the actual dual logarithmic norm of first-coordinate evaluation. -/
theorem dual_not_isUpperDominated : ¬ normFamily.dual.IsUpperDominated := by
  intro h
  obtain ⟨A, hA, hbound⟩ := h firstCoordinate firstCoordinate_ne_zero
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : Integrable (fun _ : countingCurve.Ω ↦ Real.log 2) countingCurve.v := by
    apply hA.mono' measurable_const.aestronglyMeasurable
    filter_upwards [hbound] with a ha
    rw [firstCoordinate_dual_logNorm] at ha
    simpa only [Real.norm_eq_abs, abs_of_pos hp] using ha
  have hs := integrable_count_iff.mp hc
  have hz : ‖Real.log 2‖ = 0 := (summable_const_iff _).mp hs
  exact hp.ne' (norm_eq_zero.mp hz)

/-- The actual family is upper and lower dominated but fails source
domination, which also requires upper domination of its actual dual. -/
theorem not_isDominated : ¬ normFamily.IsDominated :=
  fun h ↦ dual_not_isUpperDominated h.2

/-- Remark 4.1.4 is realized by an actual proper counting curve and a
genuine completed norm family, with no domination conclusion supplied. -/
theorem exists_upper_lower_not_dominated :
    ∃ S : AdelicStructure.{0, 0} ℚ, S.IsProper ∧
      ∃ ξ : NormFamily S Plane,
        ξ.IsUpperDominated ∧ ξ.IsLowerDominated ∧ ¬ ξ.IsDominated :=
  ⟨countingCurve, inferInstance, normFamily, isUpperDominated, isLowerDominated,
    not_isDominated⟩

end

end ArakelovGeometry.CountingDominationCounterexample
