/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Basic
public import ArakelovGeometry.LinearAlgebra.FiniteFiltration
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Actual trivial norms from real subspace filtrations

The inverse uses the existing canonical subspace jump. Norm laws follow
from genuine submodule membership cuts, without an input finite flag.
-/

@[expose] public section

namespace Submodule

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- Attainment of the whole space replaces the earlier requirement that
the nonzero subspace itself be an attained filtration level. -/
theorem le_filtration_iff_le_jump_of_attains_top {F : ℝ → Submodule K E}
    (hF : Antitone F) (hbot : ∃ t, F t = ⊥) (htop : ∃ t, F t = ⊤)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t)
    {U : Submodule K E} (hne : U ≠ ⊥) (t : ℝ) :
    U ≤ F t ↔ t ≤ filtrationJump F U := by
  let A : Set ℝ := {s | U ≤ F s}
  have hn : A.Nonempty := by
    obtain ⟨s, hs⟩ := htop
    refine ⟨s, ?_⟩
    change U ≤ F s
    rw [hs]
    exact le_top
  have hb : BddAbove A := by
    obtain ⟨z, hz⟩ := hbot
    refine ⟨z, fun s hs ↦ ?_⟩
    by_contra hsz
    have hu : U ≤ ⊥ := (hs.trans (hF (lt_of_not_ge hsz).le)).trans (le_of_eq hz)
    exact hne (le_antisymm hu bot_le)
  have hbelow : ∀ s < filtrationJump F U, U ≤ F s := by
    intro s hs
    obtain ⟨z, hz, hsz⟩ := exists_lt_of_lt_csSup hn hs
    exact hz.trans (hF hsz.le)
  have hat : U ≤ F (filtrationJump F U) := by
    obtain ⟨ε, hε, hc⟩ := hleft (filtrationJump F U)
    have h1 : filtrationJump F U - ε < filtrationJump F U - ε / 2 := by linarith
    have h2 : filtrationJump F U - ε / 2 < filtrationJump F U := by linarith
    exact (hc _ h1 h2.le) ▸ hbelow _ h2
  exact ⟨fun ht ↦ le_csSup hb ht, fun ht ↦ hat.trans (hF ht)⟩

/-- A nonzero vector's canonical line jump is exactly its included
membership cut. -/
theorem mem_filtration_iff_le_jump_span {F : ℝ → Submodule K E}
    (hF : Antitone F) (hbot : ∃ t, F t = ⊥) (htop : ∃ t, F t = ⊤)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t)
    (x : E) (hx : x ≠ 0) (t : ℝ) :
    x ∈ F t ↔ t ≤ filtrationJump F (K ∙ x) := by
  rw [← span_singleton_le_iff_mem]
  exact le_filtration_iff_le_jump_of_attains_top hF hbot htop hleft
    (span_singleton_eq_bot.not.mpr hx) t

end Submodule

namespace ArakelovGeometry.NormFamily

noncomputable section

open AdelicStructure

universe u w

variable {K : Type u} [Field K] {E : Type w} [AddCommGroup E] [Module K E]
  (F : ℝ → Submodule K E) (hF : Antitone F)
  (hbot : ∃ t, F t = ⊥) (htop : ∃ t, F t = ⊤)
  (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t)

open Classical in
/-- The norm value associated to the jump of the line spanned by a vector. -/
def filtrationNormValue (x : E) : ℝ :=
  if x = 0 then 0 else Real.exp (-Submodule.filtrationJump F (K ∙ x))

open Classical in
/-- The jump formula gives a nonnegative norm value. -/
theorem filtrationNormValue_nonneg (x : E) : 0 ≤ filtrationNormValue F x := by
  by_cases hx : x = 0 <;> simp only [filtrationNormValue, hx, ite_true, ite_false]
  · exact le_rfl
  · exact (Real.exp_pos _).le

include hF hbot htop hleft in
open Classical in
/-- Filtration levels are submodules, so their associated norm is ultrametric. -/
theorem filtrationNormValue_add_le_max (x y : E) :
    filtrationNormValue F (x + y) ≤ max (filtrationNormValue F x) (filtrationNormValue F y) := by
  by_cases hx : x = 0
  · simp [hx, filtrationNormValue]
  by_cases hy : y = 0
  · simp [hy, filtrationNormValue]
  by_cases hs : x + y = 0
  · rw [filtrationNormValue, ite_eq_left hs]
    exact le_max_of_le_left (filtrationNormValue_nonneg F x)
  let a := Submodule.filtrationJump F (K ∙ x)
  let b := Submodule.filtrationJump F (K ∙ y)
  have hxm : x ∈ F a := (Submodule.mem_filtration_iff_le_jump_span
    hF hbot htop hleft x hx a).mpr le_rfl
  have hym : y ∈ F b := (Submodule.mem_filtration_iff_le_jump_span
    hF hbot htop hleft y hy b).mpr le_rfl
  rw [filtrationNormValue, ite_eq_right hs, filtrationNormValue, ite_eq_right hx,
    filtrationNormValue, ite_eq_right hy]
  rcases le_total a b with hab | hba
  · have hsm := (F a).add_mem hxm (hF hab hym)
    have hle := (Submodule.mem_filtration_iff_le_jump_span
      hF hbot htop hleft (x + y) hs a).mp hsm
    exact (Real.exp_le_exp.mpr (neg_le_neg hle)).trans (le_max_left _ _)
  · have hsm := (F b).add_mem (hF hba hxm) hym
    have hle := (Submodule.mem_filtration_iff_le_jump_span
      hF hbot htop hleft (x + y) hs b).mp hsm
    exact (Real.exp_le_exp.mpr (neg_le_neg hle)).trans (le_max_right _ _)

include hF hbot htop hleft in
open Classical in
/-- The jump formula is homogeneous for the trivial absolute value. -/
theorem filtrationNormValue_smul (a : K) (x : E) :
    filtrationNormValue F (a • x) =
      (AbsoluteValue.trivial : AbsoluteValue K ℝ) a * filtrationNormValue F x := by
  by_cases ha : a = 0
  · simp [ha, filtrationNormValue]
  by_cases hx : x = 0
  · simp [hx, filtrationNormValue]
  have hn : a • x ≠ 0 := smul_ne_zero ha hx
  have hj : Submodule.filtrationJump F (K ∙ (a • x)) =
      Submodule.filtrationJump F (K ∙ x) :=
    Submodule.filtrationJump_eq_of_cut (fun t ↦ by
      rw [Submodule.span_singleton_le_iff_mem, (F t).smul_mem_iff ha]
      exact Submodule.mem_filtration_iff_le_jump_span hF hbot htop hleft x hx t)
  simp only [filtrationNormValue, ite_eq_right hn, ite_eq_right hx, hj,
    AbsoluteValue.trivial_apply ha, one_mul]

open Classical in
/-- The source inverse norm built from the actual membership jumps.
Ultrametricity and scalar homogeneity are proved from the filtration. -/
def trivialFiltrationSeminorm :
    Seminorm (WithAbs (AbsoluteValue.trivial : AbsoluteValue K ℝ)) E :=
  Seminorm.of (filtrationNormValue F)
    (fun x y ↦ (filtrationNormValue_add_le_max F hF hbot htop hleft x y).trans
      (max_le (le_add_of_nonneg_right (filtrationNormValue_nonneg F y))
        (le_add_of_nonneg_left (filtrationNormValue_nonneg F x))))
    (fun a x ↦ by
      change filtrationNormValue F (a.ofAbs • x) = ‖a‖ * filtrationNormValue F x
      rw [WithAbs.norm_eq_apply_ofAbs]
      exact filtrationNormValue_smul F hF hbot htop hleft a.ofAbs x)

open Classical in
/-- The inverse norm uses the canonical jump away from zero. -/
theorem trivialFiltrationSeminorm_apply (x : E) :
    trivialFiltrationSeminorm F hF hbot htop hleft x =
      if x = 0 then 0 else Real.exp (-Submodule.filtrationJump F (K ∙ x)) := rfl

open Classical in
/-- Positivity of the exponential gives actual separation of zero. -/
theorem trivialFiltrationSeminorm_eq_zero_iff (x : E) :
    trivialFiltrationSeminorm F hF hbot htop hleft x = 0 ↔ x = 0 := by
  rw [trivialFiltrationSeminorm_apply]
  by_cases hx : x = 0 <;> simp [hx, Real.exp_ne_zero]

open Classical in
/-- The inverse seminorm is ultrametric on all rational vectors. -/
theorem trivialFiltrationSeminorm_add_le_max (x y : E) :
    trivialFiltrationSeminorm F hF hbot htop hleft (x + y) ≤
      max (trivialFiltrationSeminorm F hF hbot htop hleft x)
        (trivialFiltrationSeminorm F hF hbot htop hleft y) :=
  filtrationNormValue_add_le_max F hF hbot htop hleft x y

open Classical in
/-- Transport the produced separating norm to the genuine actual
completed tensor fibre of the single trivial place. -/
def ofTrivialFiltration : NormFamily (singleTrivialPlace K) E :=
  ofTrivialNorm (trivialFiltrationSeminorm F hF hbot htop hleft)
    (trivialFiltrationSeminorm_eq_zero_iff F hF hbot htop hleft)

/-- The produced actual family is ultrametric on every completed vector. -/
theorem ofTrivialFiltration_isUltrametric :
    (ofTrivialFiltration F hF hbot htop hleft).IsUltrametric :=
  (ofTrivialNorm_isUltrametric_iff _ _).mpr
    (trivialFiltrationSeminorm_add_le_max F hF hbot htop hleft)

open Classical in
/-- Exact recovery of the original filtration by the produced actual
family's literal closed balls, including zero vectors and endpoints. -/
theorem trivialFiltration_ofTrivialFiltration (t : ℝ) :
    (ofTrivialFiltration F hF hbot htop hleft).trivialFiltration
      (ofTrivialFiltration_isUltrametric F hF hbot htop hleft) t = F t := by
  ext x
  simp only [mem_trivialFiltration, ofTrivialFiltration, trivialSeminorm_ofTrivialNorm,
    trivialFiltrationSeminorm_apply]
  by_cases hx : x = 0
  · simp [hx, (Real.exp_pos (-t)).le]
  · rw [ite_eq_right hx, Real.exp_le_exp, neg_le_neg_iff]
    exact (Submodule.mem_filtration_iff_le_jump_span hF hbot htop hleft x hx t).symm

open Classical in
/-- The inverse construction recovers an actual ultrametric family on
all completed vectors, via equality of its genuine extracted norm. -/
theorem ofTrivialFiltration_trivialFiltration [FiniteDimensional K E]
    (ξ : NormFamily (singleTrivialPlace K) E) (hξ : ξ.IsUltrametric) :
    ofTrivialFiltration (ξ.trivialFiltration hξ) (ξ.antitone_trivialFiltration hξ)
      (ξ.trivialFiltration_attains_bot_top hξ).1 (ξ.trivialFiltration_attains_bot_top hξ).2
      (ξ.trivialFiltration_locallyConstant_left hξ) = ξ := by
  let p := trivialFiltrationSeminorm (ξ.trivialFiltration hξ) (ξ.antitone_trivialFiltration hξ)
    (ξ.trivialFiltration_attains_bot_top hξ).1 (ξ.trivialFiltration_attains_bot_top hξ).2
    (ξ.trivialFiltration_locallyConstant_left hξ)
  have hp : p = ξ.trivialSeminorm := by
    ext x
    change trivialFiltrationSeminorm _ _ _ _ _ x = ξ.trivialSeminorm x
    rw [trivialFiltrationSeminorm_apply]
    by_cases hx : x = 0
    · rw [ite_eq_left hx, hx]
      exact (map_zero ξ.trivialSeminorm).symm
    · have hj : Submodule.filtrationJump (ξ.trivialFiltration hξ) (K ∙ x) =
          -Real.log (ξ.trivialSeminorm x) :=
        Submodule.filtrationJump_eq_of_cut (fun t ↦ by
          rw [Submodule.span_singleton_le_iff_mem]
          exact ξ.mem_trivialFiltration_iff_le_neg_log hξ t x hx)
      have hxpos : 0 < ξ.trivialSeminorm x := by
        rw [trivialSeminorm_apply]
        exact ξ.norm_rational_pos PUnit.unit hx
      rw [ite_eq_right hx, hj, neg_neg, Real.exp_log hxpos]
  ext ω z
  calc
    _ = p (trivialCompletedTensorEquiv K E z) := rfl
    _ = ξ.trivialSeminorm (trivialCompletedTensorEquiv K E z) :=
      congrArg (fun q ↦ q (trivialCompletedTensorEquiv K E z)) hp
    _ = ξ.norm ω z := congrArg (fun η : NormFamily (singleTrivialPlace K) E ↦ η.norm ω z)
      ξ.ofTrivialNorm_trivialSeminorm

end

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

open AdelicStructure

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The inverse real filtration gives the actual adelic bundle with
automatically produced one-point measurability and domination. -/
def ofTrivialFiltration (F : ℝ → Submodule K E) (hF : Antitone F)
    (hbot : ∃ t, F t = ⊥) (htop : ∃ t, F t = ⊤)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t) :
    AdelicVectorBundle (singleTrivialPlace K) E :=
  ofSingleTrivialPlace (NormFamily.ofTrivialFiltration F hF hbot htop hleft)

@[simp]
theorem ofTrivialFiltration_toNormFamily (F : ℝ → Submodule K E) (hF : Antitone F)
    (hbot : ∃ t, F t = ⊥) (htop : ∃ t, F t = ⊤)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t) :
    (ofTrivialFiltration F hF hbot htop hleft).toNormFamily =
      NormFamily.ofTrivialFiltration F hF hbot htop hleft := rfl

end

end ArakelovGeometry.AdelicVectorBundle
