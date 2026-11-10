/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.GeometryOfNumbers.Measure.IntegralDualCovolume
public import Mathlib.Analysis.LocallyConvex.Polar

/-! # Actual interior lattice points annihilate actual polar lattice points -/

@[expose] public section

noncomputable section
open Set Topology

namespace ArakelovGeometry.GeometryOfNumbers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonzero actual polar functional is strictly bounded at an actual interior point. -/
theorem polar_eval_norm_lt_one_of_mem_interior {C : Set E} {x : E}
    {f : StrongDual ℝ E} (hx : x ∈ interior C) (hf : f ∈ StrongDual.polar ℝ C)
    (hfne : f ≠ 0) : ‖f x‖ < 1 := by
  have hfl : f.toLinearMap ≠ 0 := by
    intro h
    apply hfne
    ext y
    exact LinearMap.congr_fun h y
  have hopen : IsOpenMap f :=
    LinearMap.isOpenMap_of_finiteDimensional f.toLinearMap (LinearMap.surjective hfl)
  have hbound : f '' C ⊆ Icc (-1 : ℝ) 1 := by
    rintro y ⟨z, hz, rfl⟩
    have h := hf z hz
    change ‖f z‖ ≤ 1 at h
    rw [Real.norm_eq_abs] at h
    exact abs_le.mp h
  have hnhds : Icc (-1 : ℝ) 1 ∈ 𝓝 (f x) :=
    Filter.mem_of_superset (hopen.image_mem_nhds (mem_interior_iff_mem_nhds.mp hx)) hbound
  have hi := mem_interior_iff_mem_nhds.mpr hnhds
  rw [interior_Icc] at hi
  rw [Real.norm_eq_abs]
  exact abs_lt.mpr hi

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The actual integer value of an actual polar functional on an interior lattice point is zero. -/
theorem integralDual_eval_eq_zero_of_mem_interior_polar (L : Submodule ℤ V)
    {C : Set V} {x : V} (hxL : x ∈ L) (hx : x ∈ interior C)
    {f : StrongDual ℝ V} (hfL : f ∈ integralDual L) (hf : f ∈ StrongDual.polar ℝ C) :
    f x = 0 := by
  by_cases hfzero : f = 0
  · subst f
    rfl
  have hfx := polar_eval_norm_lt_one_of_mem_interior hx hf hfzero
  obtain ⟨z, hz⟩ := hfL x hxL
  change (z : ℝ) = f x at hz
  rw [← hz, Real.norm_eq_abs] at hfx
  have hzlo : (-1 : ℤ) < z := by exact_mod_cast (abs_lt.mp hfx).1
  have hzhi : z < 1 := by exact_mod_cast (abs_lt.mp hfx).2
  have hz0 : z = 0 := by omega
  simpa only [hz0, Int.cast_zero] using hz.symm

/-- The actual real span of polar lattice functionals lies in the actual evaluation kernel. -/
theorem span_polar_integralDual_le_eval_ker (L : Submodule ℤ V)
    {C : Set V} {x : V} (hxL : x ∈ L) (hx : x ∈ interior C) :
    Submodule.span ℝ {f : StrongDual ℝ V | f ∈ integralDual L ∧ f ∈ StrongDual.polar ℝ C} ≤
      LinearMap.ker (ContinuousLinearMap.apply ℝ ℝ (E' := V) x).toLinearMap := by
  apply Submodule.span_le.mpr
  intro f hf
  change f x = 0
  exact integralDual_eval_eq_zero_of_mem_interior_polar L hxL hx hf.1 hf.2

/-- Actual interior lattice points lie in the kernel intersection annihilating the polar span. -/
theorem interior_lattice_subset_polar_span_annihilator (L : Submodule ℤ V) (C : Set V) :
    (L : Set V) ∩ interior C ⊆
      ((⨅ f : Submodule.span ℝ
        {g : StrongDual ℝ V | g ∈ integralDual L ∧ g ∈ StrongDual.polar ℝ C},
        f.val.ker) : Submodule ℝ V) := by
  rintro x ⟨hxL, hx⟩
  apply (Submodule.mem_iInf _).mpr
  intro f
  exact span_polar_integralDual_le_eval_ker L hxL hx f.property

end ArakelovGeometry.GeometryOfNumbers
