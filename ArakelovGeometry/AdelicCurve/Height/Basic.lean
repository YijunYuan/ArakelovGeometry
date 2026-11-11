/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Defs
public import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Heights of tuples and projective points

The integral of the logarithm of the coordinate maximum is integrable for any
adelic structure. For a proper structure, the product formula makes this height
invariant under nonzero scaling and hence defines a height on projective space.

Reference: Chen–Moriwaki, Definition 3.5.1. Applying these constructions to the
algebraic extension to an algebraic closure gives the height in that definition.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure

open MeasureTheory

universe u v

variable {K : Type u} [Field K] (AS : AdelicStructure.{u, v} K)

/-- Logarithmic evaluations, extended by zero at the field element zero, are measurable. -/
theorem measurable_log_eval (a : K) :
    Measurable (fun ω : AS.Ω ↦ Real.log (AS.ϕ ω a)) := by
  by_cases ha : a = 0
  · simp [ha]
  · exact AS.measurable_log a ha

/-- Logarithmic evaluations, extended by zero at zero, are integrable. -/
theorem integrable_log_eval (a : K) :
    Integrable (fun ω : AS.Ω ↦ Real.log (AS.ϕ ω a)) AS.v := by
  by_cases ha : a = 0
  · simp [ha]
  · exact AS.integrable_log a ha

/-- Absolute-value evaluations are measurable, including at zero. -/
theorem measurable_eval (a : K) : Measurable (fun ω : AS.Ω ↦ AS.ϕ ω a) := by
  by_cases ha : a = 0
  · simp [ha]
  · have he : (fun ω : AS.Ω ↦ AS.ϕ ω a) =
        (fun ω : AS.Ω ↦ Real.exp (Real.log (AS.ϕ ω a))) := by
      funext ω
      exact (Real.exp_log ((AS.ϕ ω).pos ha)).symm
    rw [he]
    exact (AS.measurable_log a ha).exp

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The maximum of the absolute values of the coordinates at a place. -/
noncomputable def localHeight (a : ι → K) (ω : AS.Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i ↦ AS.ϕ ω (a i)

theorem eval_le_localHeight (a : ι → K) (ω : AS.Ω) (i : ι) :
    AS.ϕ ω (a i) ≤ AS.localHeight a ω :=
  Finset.le_sup' (fun j ↦ AS.ϕ ω (a j)) (Finset.mem_univ i)

theorem localHeight_pos {a : ι → K} (ha : a ≠ 0) (ω : AS.Ω) :
    0 < AS.localHeight a ω := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra! h
    exact ha (funext h)
  exact lt_of_lt_of_le ((AS.ϕ ω).pos hi) (AS.eval_le_localHeight a ω i)

theorem measurable_localHeight (a : ι → K) : Measurable (AS.localHeight a) := by
  have he : AS.localHeight a = Finset.univ.sup' Finset.univ_nonempty
      (fun i (ω : AS.Ω) ↦ AS.ϕ ω (a i)) := by
    funext ω
    exact (Finset.sup'_apply Finset.univ_nonempty
      (fun i (ω : AS.Ω) ↦ AS.ϕ ω (a i)) ω).symm
  rw [he]
  exact Finset.measurable_sup' Finset.univ_nonempty
    (fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦ AS.measurable_eval (a i))

/-- The local logarithmic maximum is integrable without a finite-measure hypothesis. -/
theorem integrable_log_localHeight (a : ι → K) :
    Integrable (fun ω ↦ Real.log (AS.localHeight a ω)) AS.v := by
  have hi := integrable_finsetSum Finset.univ
    (fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦ (AS.integrable_log_eval (a i)).norm)
  apply hi.mono' (AS.measurable_localHeight a).log.aestronglyMeasurable
  filter_upwards [] with ω
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i ↦ AS.ϕ ω (a i))
  change ‖Real.log (Finset.univ.sup' _ _)‖ ≤ _
  rw [he]
  exact Finset.single_le_sum (fun j _ ↦ norm_nonneg (Real.log (AS.ϕ ω (a j)))) hi

/-- The logarithmic height of a coordinate tuple. For the zero tuple its value is zero. -/
noncomputable def logHeight (a : ι → K) : ℝ :=
  ∫ ω, Real.log (AS.localHeight a ω) ∂AS.v

@[simp] theorem localHeight_zero (ω : AS.Ω) : AS.localHeight (0 : ι → K) ω = 0 := by
  simp [localHeight]

@[simp] theorem logHeight_zero : AS.logHeight (0 : ι → K) = 0 := by
  simp [logHeight]

theorem localHeight_smul (a : ι → K) (t : K) (ω : AS.Ω) :
    AS.localHeight (t • a) ω = AS.ϕ ω t * AS.localHeight a ω := by
  simp only [localHeight, Pi.smul_apply, smul_eq_mul, map_mul]
  simpa only [mul_comm] using
    (Finset.sup'_mul₀ ((AS.ϕ ω).nonneg t) (fun i ↦ AS.ϕ ω (a i))
      Finset.univ Finset.univ_nonempty).symm

theorem log_localHeight_smul {a : ι → K} (ha : a ≠ 0) {t : K} (ht : t ≠ 0)
    (ω : AS.Ω) : Real.log (AS.localHeight (t • a) ω) =
      Real.log (AS.ϕ ω t) + Real.log (AS.localHeight a ω) := by
  rw [AS.localHeight_smul, Real.log_mul ((AS.ϕ ω).pos ht).ne'
    (AS.localHeight_pos ha ω).ne']

/-- Scaling a nonzero tuple adds the integral of the logarithm of the scalar. -/
theorem logHeight_smul {a : ι → K} (ha : a ≠ 0) {t : K} (ht : t ≠ 0) :
    AS.logHeight (t • a) = (∫ ω, Real.log (AS.ϕ ω t) ∂AS.v) + AS.logHeight a := by
  simp only [logHeight, AS.log_localHeight_smul ha ht]
  exact integral_add (AS.integrable_log t ht) (AS.integrable_log_localHeight a)

variable [AS.IsProper]

/-- The product formula makes height invariant under nonzero scalar multiplication. -/
theorem logHeight_smul_eq {a : ι → K} (ha : a ≠ 0) {t : K} (ht : t ≠ 0) :
    AS.logHeight (t • a) = AS.logHeight a := by
  have hp := AdelicStructure.IsProper.product_formula (AS := AS) t ht
  change (∫ ω, Real.log (AS.ϕ ω t) ∂AS.v) = 0 at hp
  rw [AS.logHeight_smul ha ht, hp, zero_add]

/-- Heights for a proper adelic structure are nonnegative. -/
theorem logHeight_nonneg (a : ι → K) : 0 ≤ AS.logHeight a := by
  by_cases ha : a = 0
  · simp [ha]
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra! h
    exact ha (funext h)
  have h := integral_mono (AS.integrable_log (a i) hi)
    (AS.integrable_log_localHeight a)
    (fun ω ↦ Real.log_le_log ((AS.ϕ ω).pos hi) (AS.eval_le_localHeight a ω i))
  have hp := AdelicStructure.IsProper.product_formula (AS := AS) (a i) hi
  change (∫ ω, Real.log (AS.ϕ ω (a i)) ∂AS.v) = 0 at hp
  rwa [hp] at h

/-- Projective height, well-defined by the product formula (Definition 3.5.1). -/
noncomputable def projectiveHeight (x : Projectivization K (ι → K)) : ℝ :=
  x.lift (fun a ↦ AS.logHeight a.val) fun a b t h ↦ by
    have ht : t ≠ 0 := by
      intro ht
      exact a.property (by simpa [ht] using h)
    rw [h, AS.logHeight_smul_eq b.property ht]

@[simp] theorem projectiveHeight_mk {a : ι → K} (ha : a ≠ 0) :
    AS.projectiveHeight (Projectivization.mk K a ha) = AS.logHeight a := rfl

theorem projectiveHeight_nonneg (x : Projectivization K (ι → K)) :
    0 ≤ AS.projectiveHeight x := by
  rw [← x.mk_rep, AS.projectiveHeight_mk]
  exact AS.logHeight_nonneg x.rep

end ArakelovGeometry.AdelicStructure
