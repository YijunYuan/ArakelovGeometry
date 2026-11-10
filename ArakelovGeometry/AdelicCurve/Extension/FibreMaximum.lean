/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Basic
public import ArakelovGeometry.AdelicCurve.Extension.Finite.Tower
import ArakelovGeometry.AdelicCurve.Extension.Finite.Probability
import Mathlib.CategoryTheory.Category.Init

/-!
# Measurable maxima over finite extension fibres

Chen--Moriwaki, Proposition 3.6.2: for every finite field extension, the attained
maximum of a measurable real function over each extension fibre is measurable.
The proof uses positive masses in the finite fibre probabilities and their
measurable integration operator. The existing measurable equivalence with the
separable model transports the argument to the intrinsic parameter space.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ArakelovGeometry.AdelicStructure.ParameterSpaceExtension

variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Every finite extension fibre contains an extending absolute value. -/
theorem nonempty_extensionFiber (ω : AS.Ω) : Nonempty (ExtensionFiber AS L ω) := by
  obtain ⟨x, hx⟩ := Algebraic.surjective_proj AS L ω
  exact ⟨⟨x, hx⟩⟩

/-- The maximum of a real function over a finite extension fibre. -/
noncomputable def fibreMaximum (f : ParameterSpaceExtension AS L → ℝ) (ω : AS.Ω) : ℝ :=
  ⨆ x : ExtensionFiber AS L ω, f x.val

/-- Every value on a finite fibre is bounded by its maximum. -/
theorem le_fibreMaximum (f : ParameterSpaceExtension AS L → ℝ) (ω : AS.Ω)
    (x : ExtensionFiber AS L ω) : f x.val ≤ fibreMaximum AS L f ω := by
  let := finite_extensionFiber AS L ω
  exact Finite.le_ciSup (fun x : ExtensionFiber AS L ω ↦ f x.val) x

/-- The real maximum on a finite fibre is attained. -/
theorem exists_eq_fibreMaximum (f : ParameterSpaceExtension AS L → ℝ) (ω : AS.Ω) :
    ∃ x : ExtensionFiber AS L ω, f x.val = fibreMaximum AS L f ω := by
  let := finite_extensionFiber AS L ω
  let := nonempty_extensionFiber AS L ω
  exact exists_eq_ciSup_of_finite

/-- The fibre maximum is the least upper bound of the values on that fibre. -/
theorem fibreMaximum_le_iff (f : ParameterSpaceExtension AS L → ℝ) (ω : AS.Ω) (c : ℝ) :
    fibreMaximum AS L f ω ≤ c ↔ ∀ x : ExtensionFiber AS L ω, f x.val ≤ c := by
  constructor
  · exact fun h x ↦ (le_fibreMaximum AS L f ω x).trans h
  · intro h
    obtain ⟨x, hx⟩ := exists_eq_fibreMaximum AS L f ω
    rw [← hx]
    exact h x

/-- A strict lower bound for the maximum is witnessed by a point of the fibre. -/
theorem lt_fibreMaximum_iff (f : ParameterSpaceExtension AS L → ℝ) (ω : AS.Ω) (c : ℝ) :
    c < fibreMaximum AS L f ω ↔ ∃ x : ExtensionFiber AS L ω, c < f x.val := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := exists_eq_fibreMaximum AS L f ω
    exact ⟨x, hx ▸ h⟩
  · rintro ⟨x, hx⟩
    exact hx.trans_le (le_fibreMaximum AS L f ω x)

end ArakelovGeometry.AdelicStructure.ParameterSpaceExtension

namespace ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension

variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Positive fibre mass detects whether a set meets the finite fibre, including for
inseparable extensions through their separable parameter model. -/
theorem fibreLIntegral_indicator_pos_iff (s : Set (ParameterSpaceFinExtension AS L))
    (ω : AS.Ω) :
    0 < fibreLIntegral AS L (s.indicator fun _ ↦ (1 : ℝ≥0∞)) ω ↔
      ∃ x : BaseFiber (AS := AS) L ω, x.val ∈ s := by
  classical
  let := ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K L) ω
  let : Fintype (BaseFiber (AS := AS) L ω) := Fintype.ofFinite _
  have hw (x : BaseFiber (AS := AS) L ω) :
      ParameterSpaceExtension.fibreWeight AS (separableClosure K L) ω x ≠ 0 :=
    ne_of_gt (ParameterSpaceExtension.fibreWeight_pos AS (separableClosure K L) ω x)
  simp [fibreLIntegral_eq_sum, pos_iff_ne_zero, Finset.sum_eq_zero_iff, mul_eq_zero, hw]

end ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension

namespace ArakelovGeometry.AdelicStructure.ParameterSpaceExtension

variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The projection of a finite extension maps every measurable set to a measurable set. -/
theorem measurableSet_image_proj {s : Set (ParameterSpaceExtension AS L)}
    (hs : MeasurableSet s) : MeasurableSet (proj '' s) := by
  let e := ParameterSpaceFinExtension.measurableEquivFull AS L
  let B := e ⁻¹' s
  let g := B.indicator fun _ ↦ (1 : ℝ≥0∞)
  have hg : Measurable g := measurable_const.indicator (hs.preimage e.measurable)
  have hI := ParameterSpaceFinExtension.measurable_fibreLIntegral AS L hg
  have heq : proj '' s =
      {ω | 0 < ParameterSpaceFinExtension.fibreLIntegral AS L g ω} := by
    ext ω
    rw [Set.mem_ofPred_eq, ParameterSpaceFinExtension.fibreLIntegral_indicator_pos_iff]
    constructor
    · rintro ⟨x, hx, hω⟩
      refine ⟨⟨e.symm x, hω⟩, ?_⟩
      change e (e.symm x) ∈ s
      simpa only [e.apply_symm_apply] using hx
    · rintro ⟨x, hx⟩
      exact ⟨e x.val, hx, x.property⟩
  rw [heq]
  exact measurableSet_lt measurable_const hI

/-- Chen--Moriwaki, Proposition 3.6.2: maxima over finite extension fibres are
measurable for every measurable real function, without normality or separability. -/
theorem measurable_fibreMaximum {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Measurable f) : Measurable (fibreMaximum AS L f) := by
  apply measurable_of_Ioi
  intro c
  have heq : fibreMaximum AS L f ⁻¹' Set.Ioi c = proj '' (f ⁻¹' Set.Ioi c) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Ioi, lt_fibreMaximum_iff, Set.mem_image]
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨x.val, hx, x.property⟩,
      fun ⟨x, hx, hω⟩ ↦ ⟨⟨x, hω⟩, hx⟩⟩
  rw [heq]
  exact measurableSet_image_proj AS L (hf measurableSet_Ioi)

/-- Proposition 3.6.2 for the projective sigma algebra defining the algebraic
extension adelic structure; it equals the intrinsic evaluation sigma algebra. -/
theorem measurable_fibreMaximum_projective {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Measurable[Algebraic.projectiveMeasurableSpace AS L] f) :
    Measurable (fibreMaximum AS L f) := by
  rw [Algebraic.projectiveMeasurableSpace_eq] at hf
  exact measurable_fibreMaximum AS L hf

end ArakelovGeometry.AdelicStructure.ParameterSpaceExtension
