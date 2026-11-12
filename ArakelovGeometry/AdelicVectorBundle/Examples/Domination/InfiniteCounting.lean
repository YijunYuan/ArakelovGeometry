/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicStructure.TrivialPlace
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Basic
public import Mathlib.RingTheory.Finiteness.Prod

import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Upper and lower domination do not imply domination

The full arbitrary infinite-field counting-place example of Remark 4.1.4.
The sigma-algebra consists of all subsets; no countability is assumed.
Norms use the existing genuine trivial completed tensor fibres and their
canonical operator duals, in every characteristic.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.InfiniteCountingDominationCounterexample

noncomputable section

open AdelicStructure

universe u

variable (K : Type u) [Field K]

local instance : MeasurableSpace K := ⊤

-- Match the canonical trivial-completion zero-decidability datum.
local instance : DecidablePred (fun x : K ↦ x = 0) :=
  fun _ ↦ Classical.propDecidable _

open Classical in
/-- The actual proper trivial adelic structure on the infinite field
counting space. -/
abbrev countingCurve : AdelicStructure K where
  Ω := K
  A := inferInstance
  v := Measure.count
  ϕ := fun _ ↦ AbsoluteValue.trivial
  measurable_log := (trivialAdelicStructure K K Measure.count).measurable_log
  integrable_log := (trivialAdelicStructure K K Measure.count).integrable_log

/-- The transparent counting curve is exactly the existing canonical
trivial adelic structure, including its original measure. -/
theorem countingCurve_eq_trivialAdelicStructure :
    (countingCurve K) = trivialAdelicStructure K K Measure.count := rfl

instance countingCurve_isProper : (countingCurve K).IsProper := by
  change (trivialAdelicStructure K K Measure.count).IsProper
  infer_instance

instance countingCurve_discreteMeasurableSpace :
    DiscreteMeasurableSpace (countingCurve K).Ω := by
  change DiscreteMeasurableSpace K
  infer_instance

/-- The base-field plane underlying the source example. -/
abbrev Plane := K × K

open Classical in
/-- The source's varying cheap-line norm before canonical completion transport. -/
def rawNorm (a : K) (x : (Plane K)) : ℝ :=
  if x = 0 then 0 else if x.2 = a * x.1 then 1 / 2 else 1

@[simp]
theorem rawNorm_zero (a : K) : (rawNorm K) a 0 = 0 := by
  simp [rawNorm]

theorem rawNorm_le_one (a : K) (x : (Plane K)) : (rawNorm K) a x ≤ 1 := by
  simp only [rawNorm]
  split_ifs <;> norm_num

theorem half_le_rawNorm (a : K) {x : (Plane K)} (hx : x ≠ 0) :
    (1 / 2 : ℝ) ≤ (rawNorm K) a x := by
  simp only [rawNorm, ite_eq_right hx]
  split_ifs <;> norm_num

theorem rawNorm_eq_zero_iff (a : K) (x : (Plane K)) :
    (rawNorm K) a x = 0 ↔ x = 0 := by
  by_cases hx : x = 0
  · simp [hx]
  · simp only [rawNorm, ite_eq_right hx]
    split_ifs <;> norm_num [hx]

/-- The weighted coordinate norm satisfies the triangle inequality. -/
theorem rawNorm_add_le (a : K) (x y : (Plane K)) :
    (rawNorm K) a (x + y) ≤ (rawNorm K) a x + (rawNorm K) a y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  have hsum := (rawNorm_le_one K) a (x + y)
  have hleft := (half_le_rawNorm K) a hx
  have hright := (half_le_rawNorm K) a hy
  linarith

open Classical in
private theorem rawNorm_smul (a c : K) (x : (Plane K)) :
    (rawNorm K) a (c • x) = (AbsoluteValue.trivial : AbsoluteValue K ℝ) c * (rawNorm K) a x := by
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
over the original trivially normed field. -/
def localSeminorm (a : K) :
    Seminorm (WithAbs (AbsoluteValue.trivial : AbsoluteValue K ℝ)) (Plane K) :=
  Seminorm.of ((rawNorm K) a) ((rawNorm_add_le K) a) (by
    intro c x
    change (rawNorm K) a (c.ofAbs • x) = ‖c‖ * (rawNorm K) a x
    rw [WithAbs.norm_eq_apply_ofAbs]
    exact (rawNorm_smul K) a c.ofAbs x)

open Classical in
@[simp]
theorem localSeminorm_apply (a : K) (x : (Plane K)) :
    (localSeminorm K) a x = (rawNorm K) a x := rfl

open Classical in
/-- The actual completed norm family, transported through the existing
canonical trivial-completion tensor equivalence at every counting place. -/
def normFamily : NormFamily (countingCurve K) (Plane K) where
  norm a := by
    change Seminorm (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
      ((AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion ⊗[K] (Plane K))
    exact Seminorm.of (fun z ↦ (localSeminorm K) a (trivialCompletedTensorEquiv K (Plane K) z))
      (by
        intro x y
        rw [map_add]
        exact map_add_le_add ((localSeminorm K) a) _ _)
      (by
        intro c z
        rw [trivialCompletedTensorEquiv_smul]
        change (localSeminorm K) a
          (WithAbs.toAbs (AbsoluteValue.trivial : AbsoluteValue K ℝ)
            (trivialCompletionAlgEquiv K c) • trivialCompletedTensorEquiv K (Plane K) z) = _
        rw [map_smul_eq_mul, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_toAbs,
          ← norm_trivialCompletion K c])
  norm_eq_zero_iff a z := by
    change (rawNorm K) a (trivialCompletedTensorEquiv K (Plane K) z) = 0 ↔ z = 0
    rw [(rawNorm_eq_zero_iff K), LinearEquiv.map_eq_zero_iff]

open Classical in
/-- The norm formula on every actual completed vector, without a
base-field-pure-tensor restriction. -/
theorem normFamily_norm (a : (countingCurve K).Ω)
    (z : ((countingCurve K).ϕ a).Completion ⊗[K] (Plane K)) :
    (normFamily K).norm a z = (rawNorm K) a (trivialCompletedTensorEquiv K (Plane K) z) := rfl

open Classical in
@[simp]
theorem normFamily_norm_rational (a : (countingCurve K).Ω) (x : (Plane K)) :
    (normFamily K).norm a ((1 : ((countingCurve K).ϕ a).Completion) ⊗ₜ[K] x) =
      (rawNorm K) a x := by
  rw [(normFamily_norm K), trivialCompletedTensorEquiv_one_tmul]

open Classical in
/-- At a nonzero base-field vector, the genuine logarithmic norm is the
indicator of its unique possible cheap-line place. -/
theorem logNorm_eq (a : (countingCurve K).Ω) {x : (Plane K)} (hx : x ≠ 0) :
    (normFamily K).logNorm x a =
      if x.2 = a * x.1 then -Real.log 2 else 0 := by
  have hn : (normFamily K).logNorm x a = Real.log ((rawNorm K) a x) :=
    congrArg Real.log ((normFamily_norm_rational K) a x)
  rw [hn]
  simp only [rawNorm, ite_eq_right hx]
  split_ifs
  · rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  · exact Real.log_one

/-- Every base-field logarithmic norm is genuinely integrable against
infinite counting measure: its support is contained in one singleton. -/
theorem integrable_logNorm {x : (Plane K)} (hx : x ≠ 0) :
    Integrable ((normFamily K).logNorm x) (countingCurve K).v := by
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
  rw [(logNorm_eq K) a hx, ite_eq_right hline]
  exact _root_.norm_zero

/-- The primal norm family is upper dominated by its actual logarithmic
norm itself, whose integrability is produced for every nonzero vector. -/
theorem isUpperDominated : (normFamily K).IsUpperDominated := by
  constructor
  intro x hx
  exact ⟨(normFamily K).logNorm x, (integrable_logNorm K) hx,
    Filter.Eventually.of_forall fun _ ↦ le_rfl⟩

/-- The same produced logarithmic norm gives lower domination. -/
theorem isLowerDominated : (normFamily K).IsLowerDominated := by
  constructor
  intro x hx
  exact ⟨(normFamily K).logNorm x, (integrable_logNorm K) hx,
    Filter.Eventually.of_forall fun _ ↦ le_rfl⟩

open Classical in
/-- Every vector of every actual trivial completed tensor fibre is a
base-field pure tensor, through the existing canonical equivalence. -/
theorem completed_eq_one_tmul {F : Type*} [AddCommGroup F] [Module K F]
    (a : (countingCurve K).Ω) (z : ((countingCurve K).ϕ a).Completion ⊗[K] F) :
    z = (1 : ((countingCurve K).ϕ a).Completion) ⊗ₜ[K]
      trivialCompletedTensorEquiv K F z := by
  apply (trivialCompletedTensorEquiv K F).injective
  rw [trivialCompletedTensorEquiv_one_tmul]

private theorem trivial_apply_le_one (b : K) :
    (AbsoluteValue.trivial : AbsoluteValue K ℝ) b ≤ 1 := by
  by_cases hb : b = 0
  · simp [hb]
  · rw [AbsoluteValue.trivial_apply hb]

private theorem eval_le_rawNorm_of_annihilates (a : K) (ℓ : Module.Dual K (Plane K))
    (hcheap : ℓ ((1, a) : (Plane K)) = 0) (x : (Plane K)) :
    (AbsoluteValue.trivial : AbsoluteValue K ℝ) (ℓ x) ≤ (rawNorm K) a x := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hline : x.2 = a * x.1
  · have he : x = x.1 • ((1, a) : (Plane K)) := by
      ext <;> simp [smul_eq_mul, hline, mul_comm]
    have hval : ℓ x = 0 := by rw [he, map_smul, hcheap, smul_zero]
    rw [hval, map_zero]
    exact apply_nonneg ((localSeminorm K) a) x
  · rw [rawNorm, ite_eq_right hx, ite_eq_right hline]
    exact (trivial_apply_le_one K) (ℓ x)

open Classical in
private theorem dual_norm_le_of_rational_bound (a : (countingCurve K).Ω)
    (ℓ : Module.Dual K (Plane K)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : (Plane K), (AbsoluteValue.trivial : AbsoluteValue K ℝ) (ℓ x) ≤ C * (rawNorm K) a x) :
    (normFamily K).dual.norm a ((1 : ((countingCurve K).ϕ a).Completion) ⊗ₜ[K] ℓ) ≤ C := by
  apply (normFamily K).dual_norm_le a _ hC
  intro z
  have hz := (completed_eq_one_tmul K) a z
  have heval :
      ‖dualBaseChangeEquiv K ((countingCurve K).ϕ a).Completion (Plane K)
        ((1 : ((countingCurve K).ϕ a).Completion) ⊗ₜ[K] ℓ) z‖ =
      (AbsoluteValue.trivial : AbsoluteValue K ℝ)
        (ℓ (trivialCompletedTensorEquiv K (Plane K) z)) := by
    rw [hz, dualBaseChangeEquiv_tmul_apply_tmul, one_mul, one_mul,
      norm_trivialCompletion K, trivialCompletionAlgEquiv_algebraMap,
      trivialCompletedTensorEquiv_one_tmul]
  calc
    _ = (AbsoluteValue.trivial : AbsoluteValue K ℝ)
        (ℓ (trivialCompletedTensorEquiv K (Plane K) z)) := heval
    _ ≤ C * (rawNorm K) a (trivialCompletedTensorEquiv K (Plane K) z) := h _
    _ = C * (normFamily K).norm a z := congrArg (C * ·) ((normFamily_norm K) a z).symm

open Classical in
private theorem one_le_dual_norm_of_ne_zero (a : (countingCurve K).Ω)
    (ℓ : Module.Dual K (Plane K)) (hℓ : ℓ ≠ 0) :
    1 ≤ (normFamily K).dual.norm a ((1 : ((countingCurve K).ϕ a).Completion) ⊗ₜ[K] ℓ) := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hℓ
  have hval : ℓ x ≠ 0 := by simpa only [LinearMap.zero_apply] using hx
  have he := (normFamily K).norm_dual_tmul_apply_tmul_le a
    (1 : ((countingCurve K).ϕ a).Completion) 1 ℓ x
  have heval : ‖(1 : ((countingCurve K).ϕ a).Completion) * 1 *
      algebraMap K ((countingCurve K).ϕ a).Completion (ℓ x)‖ = 1 := by
    rw [one_mul, one_mul, norm_trivialCompletion K, trivialCompletionAlgEquiv_algebraMap,
      AbsoluteValue.trivial_apply hval]
  have hn := (normFamily_norm_rational K) a x
  rw [heval, hn] at he
  exact he.trans (by
    have hmul := mul_le_mul_of_nonneg_left ((rawNorm_le_one K) a x)
      ((normFamily K).dual.norm_nonneg a ((1 : ((countingCurve K).ϕ a).Completion) ⊗ₜ[K] ℓ))
    simpa only [mul_one] using hmul)

open Classical in
/-- The actual operator dual norm on every base-field functional: zero
at zero, one on the cheap-line annihilator, and two otherwise. -/
theorem dual_norm_rational (a : (countingCurve K).Ω) (ℓ : Module.Dual K (Plane K)) :
    (normFamily K).dual.norm a ((1 : ((countingCurve K).ϕ a).Completion) ⊗ₜ[K] ℓ) =
      if ℓ = 0 then 0 else if ℓ ((1, a) : (Plane K)) = 0 then 1 else 2 := by
  by_cases hℓ : ℓ = 0
  · subst ℓ
    simp
  rw [ite_eq_right hℓ]
  by_cases hcheap : ℓ ((1, a) : (Plane K)) = 0
  · rw [ite_eq_left hcheap]
    apply le_antisymm
    · apply (dual_norm_le_of_rational_bound K) a ℓ zero_le_one
      intro x
      simpa only [one_mul] using (eval_le_rawNorm_of_annihilates K) a ℓ hcheap x
    · exact (one_le_dual_norm_of_ne_zero K) a ℓ hℓ
  · rw [ite_eq_right hcheap]
    apply le_antisymm
    · apply (dual_norm_le_of_rational_bound K) a ℓ (by norm_num)
      intro x
      by_cases hx : x = 0
      · simp [hx]
      have hp := (half_le_rawNorm K) a hx
      have hs := (trivial_apply_le_one K) (ℓ x)
      linarith
    · have he := (normFamily K).norm_dual_tmul_apply_tmul_le a
        (1 : ((countingCurve K).ϕ a).Completion) 1 ℓ ((1, a) : (Plane K))
      have heval : ‖(1 : ((countingCurve K).ϕ a).Completion) * 1 *
          algebraMap K ((countingCurve K).ϕ a).Completion (ℓ ((1, a) : (Plane K)))‖ = 1 := by
        rw [one_mul, one_mul, norm_trivialCompletion K, trivialCompletionAlgEquiv_algebraMap,
          AbsoluteValue.trivial_apply hcheap]
      have hn : (normFamily K).norm a
          ((1 : ((countingCurve K).ϕ a).Completion) ⊗ₜ[K] ((1, a) : (Plane K))) = (1 / 2 : ℝ) := by
        rw [(normFamily_norm_rational K)]
        simp [rawNorm]
      rw [heval, hn] at he
      linarith

open Classical in
/-- The operator formula covers every actual completed functional, using
its canonical base-field inverse and the proved all-vector evaluation bounds. -/
theorem dual_norm_completed (a : (countingCurve K).Ω)
    (z : ((countingCurve K).ϕ a).Completion ⊗[K] Module.Dual K (Plane K)) :
    (normFamily K).dual.norm a z =
      if trivialCompletedTensorEquiv K (Module.Dual K (Plane K)) z = 0 then 0
      else if trivialCompletedTensorEquiv K (Module.Dual K (Plane K)) z ((1, a) : (Plane K)) = 0
        then 1 else 2 := by
  calc
    _ = (normFamily K).dual.norm a
        ((1 : ((countingCurve K).ϕ a).Completion) ⊗ₜ[K]
          trivialCompletedTensorEquiv K (Module.Dual K (Plane K)) z) :=
      congrArg ((normFamily K).dual.norm a) ((completed_eq_one_tmul K) a z)
    _ = _ := (dual_norm_rational K) a _

/-- The canonical coordinate pairing identifies each base-field coefficient
pair with its actual algebraic functional. -/
def coordinateFunctional (u v : K) : Module.Dual K (Plane K) :=
  u • LinearMap.fst K K K + v • LinearMap.snd K K K

@[simp]
theorem coordinateFunctional_apply (u v : K) (x : (Plane K)) :
    (coordinateFunctional K) u v x = u * x.1 + v * x.2 := rfl

theorem coordinateFunctional_eq_zero_iff (u v : K) :
    (coordinateFunctional K) u v = 0 ↔ (u, v) = ((0, 0) : (Plane K)) := by
  constructor
  · intro h
    have hu := congrArg (fun ℓ : Module.Dual K (Plane K) ↦ ℓ ((1, 0) : (Plane K))) h
    have hv := congrArg (fun ℓ : Module.Dual K (Plane K) ↦ ℓ ((0, 1) : (Plane K))) h
    simp only [(coordinateFunctional_apply K), mul_one, mul_zero, add_zero, zero_add,
      LinearMap.zero_apply] at hu hv
    exact Prod.ext hu hv
  · intro h
    have hu : u = 0 := congrArg Prod.fst h
    have hv : v = 0 := congrArg Prod.snd h
    simp [coordinateFunctional, hu, hv]

open Classical in
/-- The source's coefficient-pair dual formula follows from the actual
completed operator norm, using the canonical coordinate pairing. -/
theorem dual_norm_coordinates (a : (countingCurve K).Ω) (u v : K) :
    (normFamily K).dual.norm a
      ((1 : ((countingCurve K).ϕ a).Completion) ⊗ₜ[K] (coordinateFunctional K) u v) =
      if (u, v) = ((0, 0) : (Plane K)) then 0 else if u + a * v = 0 then 1 else 2 := by
  rw [(dual_norm_rational K), (coordinateFunctional_eq_zero_iff K)]
  have he : (coordinateFunctional K) u v ((1, a) : (Plane K)) = u + a * v := by
    simp only [(coordinateFunctional_apply K), mul_one, mul_comm v a]
  rw [he]
  split_ifs <;> rfl

/-- A concrete nonzero base-field functional whose actual completed
operator norm will be two at every counting place. -/
def firstCoordinate : Module.Dual K (Plane K) := LinearMap.fst K K K

theorem firstCoordinate_ne_zero : (firstCoordinate K) ≠ 0 := by
  intro h
  have he := congrArg (fun ℓ : Module.Dual K (Plane K) ↦ ℓ ((1, 0) : (Plane K))) h
  norm_num [firstCoordinate] at he

open Classical in
/-- The non-domination witness is an actual algebraic functional and
its norm is the canonical completed operator dual norm. -/
theorem firstCoordinate_dual_norm (a : (countingCurve K).Ω) :
    (normFamily K).dual.norm a
      ((1 : ((countingCurve K).ϕ a).Completion) ⊗ₜ[K] (firstCoordinate K)) = 2 := by
  have he : (firstCoordinate K) ((1, a) : (Plane K)) ≠ 0 := by simp [firstCoordinate]
  rw [(dual_norm_rational K), ite_eq_right (firstCoordinate_ne_zero K), ite_eq_right he]

/-- Its genuine base-field logarithmic dual norm is the positive constant log two. -/
theorem firstCoordinate_dual_logNorm (a : (countingCurve K).Ω) :
    (normFamily K).dual.logNorm (firstCoordinate K) a = Real.log 2 :=
  congrArg Real.log ((firstCoordinate_dual_norm K) a)

/-- Every actual nonzero functional, rather than just the selected witness,
has dual log norm log2 outside a produced set of at most one place. -/
theorem all_nonzero_functionals_cofinite_profile (ℓ : Module.Dual K (Plane K)) (hℓ : ℓ ≠ 0) :
    ∃ bad : Finset K, bad.card ≤ 1 ∧
      ∀ a : K, a ∉ bad → (normFamily K).dual.logNorm ℓ a = Real.log 2 := by
  classical
  have heval (a : K) : ℓ ((1, a) : (Plane K)) =
      ℓ ((1, 0) : (Plane K)) + a * ℓ ((0, 1) : (Plane K)) := by
    have he : ((1, a) : (Plane K)) = ((1, 0) : (Plane K)) + a • ((0, 1) : (Plane K)) := by
      ext <;> simp [smul_eq_mul]
    rw [he, map_add, map_smul]
    rfl
  by_cases hv : ℓ ((0, 1) : (Plane K)) = 0
  · have hu : ℓ ((1, 0) : (Plane K)) ≠ 0 := by
      intro hu
      apply hℓ
      apply LinearMap.ext
      intro x
      change ℓ x = 0
      have he : x = x.1 • ((1, 0) : (Plane K)) + x.2 • ((0, 1) : (Plane K)) := by
        ext <;> simp [smul_eq_mul]
      rw [he, map_add, map_smul, map_smul, hu, hv, smul_zero, smul_zero, add_zero]
    refine ⟨∅, by simp, ?_⟩
    intro a _
    have hc : ℓ ((1, a) : (Plane K)) ≠ 0 := by
      rw [heval, hv, mul_zero, add_zero]
      exact hu
    unfold NormFamily.logNorm
    rw [dual_norm_rational K, ite_eq_right hℓ, ite_eq_right hc]
  · refine ⟨{-ℓ ((1, 0) : (Plane K)) / ℓ ((0, 1) : (Plane K))}, by simp, ?_⟩
    intro a ha
    have hc : ℓ ((1, a) : (Plane K)) ≠ 0 := by
      intro hc
      have hz : ℓ ((1, 0) : (Plane K)) + a * ℓ ((0, 1) : (Plane K)) = 0 := (heval a).symm.trans hc
      have he : a = -ℓ ((1, 0) : (Plane K)) / ℓ ((0, 1) : (Plane K)) :=
        (eq_div_iff hv).mpr (by linear_combination hz)
      exact ha (by simpa only [Finset.mem_singleton] using he)
    unfold NormFamily.logNorm
    rw [dual_norm_rational K, ite_eq_right hℓ, ite_eq_right hc]


variable [Infinite K]

/-- Every nonzero base-field functional has a genuinely nonintegrable actual
operator-dual logarithmic norm, on any infinite field counting space. -/
theorem dual_logNorm_not_integrable (ℓ : Module.Dual K (Plane K)) (hℓ : ℓ ≠ 0) :
    ¬ Integrable ((normFamily K).dual.logNorm ℓ) (countingCurve K).v := by
  intro h
  obtain ⟨bad, _, hbad⟩ := all_nonzero_functionals_cofinite_profile K ℓ hℓ
  have hs := integrable_count_iff.mp h
  have hc : Summable (fun _ : K ↦ ‖Real.log 2‖) := by
    apply hs.congr_cofinite
    filter_upwards [bad.eventually_cofinite_notMem] with a ha
    rw [hbad a ha]
  have hz : ‖Real.log 2‖ = 0 := (summable_const_iff _).mp hc
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne' (norm_eq_zero.mp hz)

/-- No actual nonzero dual logarithmic norm admits an integrable upper
envelope; this is stronger than mere failure of its integrability. -/
theorem dual_logNorm_not_hasIntegrableUpperBound
    (ℓ : Module.Dual K (Plane K)) (hℓ : ℓ ≠ 0) :
    ¬ HasIntegrableUpperBound ((normFamily K).dual.logNorm ℓ) (countingCurve K).v := by
  rintro ⟨A, hA, hbound⟩
  apply dual_logNorm_not_integrable K ℓ hℓ
  have hm : Measurable ((normFamily K).dual.logNorm ℓ) := by
    intro s _
    trivial
  apply hA.mono' hm.aestronglyMeasurable
  filter_upwards [hbound] with a ha
  have hp : 0 ≤ (normFamily K).dual.logNorm ℓ a :=
    Real.log_nonneg (one_le_dual_norm_of_ne_zero K a ℓ hℓ)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp] using ha

/-- Infinite counting measure admits no integrable upper envelope of
the actual dual logarithmic norm of first-coordinate evaluation. -/
theorem dual_not_isUpperDominated : ¬ (normFamily K).dual.IsUpperDominated :=
  fun h ↦ dual_logNorm_not_hasIntegrableUpperBound K (firstCoordinate K)
    (firstCoordinate_ne_zero K) (h (firstCoordinate K) (firstCoordinate_ne_zero K))

/-- The actual family is upper and lower dominated but fails source
domination, which also requires upper domination of its actual dual. -/
theorem not_isDominated : ¬ (normFamily K).IsDominated :=
  fun h ↦ (dual_not_isUpperDominated K) h.2

/-- Remark 4.1.4 is realized by an actual proper counting curve and a
genuine completed norm family, with no domination conclusion supplied. -/
theorem exists_upper_lower_not_dominated :
    ∃ S : AdelicStructure.{u, u} K, S.IsProper ∧
      ∃ ξ : NormFamily S (Plane K),
        ξ.IsUpperDominated ∧ ξ.IsLowerDominated ∧ ¬ ξ.IsDominated :=
  ⟨(countingCurve K), inferInstance, (normFamily K), (isUpperDominated K), (isLowerDominated K),
    (not_isDominated K)⟩

end

end ArakelovGeometry.InfiniteCountingDominationCounterexample
