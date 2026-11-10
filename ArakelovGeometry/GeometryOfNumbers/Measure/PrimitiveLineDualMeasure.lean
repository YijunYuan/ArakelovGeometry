/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.GeometryOfNumbers.Lattice.LatticeSubspaceCoordinates
public import ArakelovGeometry.GeometryOfNumbers.Measure.IntegralDualCovolume
public import Mathlib.Analysis.LocallyConvex.Polar
import ArakelovGeometry.GeometryOfNumbers.Convex.RealIntervalPolar
import ArakelovGeometry.GeometryOfNumbers.Lattice.LatticePrimitiveVector
import ArakelovGeometry.GeometryOfNumbers.Measure.LatticeNormalizedMeasureEquiv
import ArakelovGeometry.GeometryOfNumbers.Measure.PrimitiveLineMeasure
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Actual integral-dual coordinates and primitive-line polar measure -/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.GeometryOfNumbers.PrimitiveLineDualMeasure

open MeasureTheory Set
open LatticeSubspaceCoordinates LatticePrimitiveVector PrimitiveLineMeasure

section Coordinates

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Canonical continuous-dual coordinates pull the actual integral dual back exactly. -/
theorem comap_integralDual_arrowCongr (L : Submodule ℤ E) (e : F ≃L[ℝ] E) :
    ZLattice.comap ℝ (integralDual L)
        (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)).toLinearMap =
      integralDual (ZLattice.comap ℝ L e.toLinearMap) := by
  ext f
  change (∀ x ∈ L, f (e.symm x) ∈ LinearMap.range (Algebra.linearMap ℤ ℝ)) ↔
    ∀ y ∈ ZLattice.comap ℝ L e.toLinearMap,
      f y ∈ LinearMap.range (Algebra.linearMap ℤ ℝ)
  constructor
  · intro hf y hy
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf (e y) hy
  · intro hf x hx
    apply hf (e.symm x)
    change e (e.symm x) ∈ L
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hx

/-- The same canonical dual coordinate identifies actual polar sets by literal preimages. -/
theorem preimage_polar_arrowCongr (e : F ≃L[ℝ] E) (C : Set E) :
    (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) ⁻¹' StrongDual.polar ℝ C =
      StrongDual.polar ℝ (e ⁻¹' C) := by
  ext f
  change (∀ x ∈ C, ‖f (e.symm x)‖ ≤ 1) ↔ ∀ y ∈ e ⁻¹' C, ‖f y‖ ≤ 1
  constructor
  · intro hf y hy
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf (e y) hy
  · intro hf x hx
    exact hf (e.symm x) (by simpa only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply]
      using hx)

section Measure

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace (StrongDual ℝ E)] [BorelSpace (StrongDual ℝ E)]
  [MeasurableSpace (StrongDual ℝ F)] [BorelSpace (StrongDual ℝ F)]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (e : F ≃L[ℝ] E)
  (μ : Measure (StrongDual ℝ E)) [μ.IsAddHaarMeasure]
  (ν : Measure (StrongDual ℝ F)) [ν.IsAddHaarMeasure]

/-- Normalized Haar measure on actual integral duals is preserved by canonical dual coordinates. -/
theorem measurePreserving_integralDual_arrowCongr :
    MeasurePreserving (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))
      (latticeNormalizedMeasure (integralDual (ZLattice.comap ℝ L e.toLinearMap)) ν)
      (latticeNormalizedMeasure (integralDual L) μ) := by
  let := integralDual_discrete L
  let := integralDual_isZLattice L
  have h := measurePreserving_latticeNormalizedMeasure_comap (integralDual L)
    (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) μ ν
  rw [comap_integralDual_arrowCongr] at h
  exact h

/-- The normalized measure of an actual polar equals that of its actual coordinate polar. -/
theorem normalizedMeasure_polar_arrowCongr (C : Set E) :
    latticeNormalizedMeasure (integralDual L) μ (StrongDual.polar ℝ C) =
      latticeNormalizedMeasure (integralDual (ZLattice.comap ℝ L e.toLinearMap)) ν
        (StrongDual.polar ℝ (e ⁻¹' C)) := by
  have h := (measurePreserving_integralDual_arrowCongr L e μ ν).measure_preimage
    (NormedSpace.isClosed_polar ℝ C).measurableSet.nullMeasurableSet
  rw [preimage_polar_arrowCongr] at h
  exact h.symm

end Measure

end Coordinates

section PrimitiveLine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (v : L) (hv : (v : E) ≠ 0)

attribute [local instance] Submodule.closed_of_finiteDimensional

omit [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L] in
/-- The intrinsic actual line integral dual has the unit-lattice integral dual as pullback. -/
theorem comap_integralDual_primitiveLine
    (hprimitive : L ⊓ (ℝ ∙ (v : E)).restrictScalars ℤ = ℤ ∙ (v : E)) :
    ZLattice.comap ℝ (integralDual (intersectionAsSubmodule L (ℝ ∙ (v : E))))
        ((ContinuousLinearEquiv.toSpanNonzeroSingleton ℝ (v : E) hv).arrowCongr
          (ContinuousLinearEquiv.refl ℝ ℝ)).toLinearMap =
      integralDual (ℤ ∙ (1 : ℝ)) := by
  rw [comap_integralDual_arrowCongr,
    comap_intersection_toSpanNonzeroSingleton L v hv hprimitive]

omit [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L] in
/-- The intrinsic polar of the original line section has its literal scalar polar as preimage. -/
theorem preimage_polar_primitiveLine (C : Set E) :
    ((ContinuousLinearEquiv.toSpanNonzeroSingleton ℝ (v : E) hv).arrowCongr
        (ContinuousLinearEquiv.refl ℝ ℝ)) ⁻¹'
        StrongDual.polar ℝ ((ℝ ∙ (v : E)).subtype ⁻¹' C) =
      StrongDual.polar ℝ ((fun t : ℝ => t • (v : E)) ⁻¹' C) :=
  preimage_polar_arrowCongr _ _

section Measure

variable [MeasurableSpace (StrongDual ℝ (ℝ ∙ (v : E)))]
  [BorelSpace (StrongDual ℝ (ℝ ∙ (v : E)))]
  [MeasurableSpace (StrongDual ℝ ℝ)] [BorelSpace (StrongDual ℝ ℝ)]
  (μ : Measure (StrongDual ℝ ℝ)) [μ.IsAddHaarMeasure]
  (ν : Measure (StrongDual ℝ (ℝ ∙ (v : E)))) [ν.IsAddHaarMeasure]

/-- Actual unit-integral-dual and line-integral-dual normalized Haar measures are transported. -/
theorem measurePreserving_primitiveLine_dualCoordinate
    (hprimitive : L ⊓ (ℝ ∙ (v : E)).restrictScalars ℤ = ℤ ∙ (v : E)) :
    MeasurePreserving
      ((ContinuousLinearEquiv.toSpanNonzeroSingleton ℝ (v : E) hv).arrowCongr
        (ContinuousLinearEquiv.refl ℝ ℝ))
      (latticeNormalizedMeasure (integralDual (ℤ ∙ (1 : ℝ))) μ)
      (latticeNormalizedMeasure (integralDual (intersectionAsSubmodule L (ℝ ∙ (v : E)))) ν) := by
  let hU := span_singleton_rational L v.property
  let := intersectionAsSubmodule_discrete L (ℝ ∙ (v : E)) hU
  let := intersectionAsSubmodule_isZLattice L (ℝ ∙ (v : E)) hU
  have h := measurePreserving_integralDual_arrowCongr
    (intersectionAsSubmodule L (ℝ ∙ (v : E)))
    (ContinuousLinearEquiv.toSpanNonzeroSingleton ℝ (v : E) hv) ν μ
  rw [comap_intersection_toSpanNonzeroSingleton L v hv hprimitive] at h
  exact h

include hv in
/-- The actual original line polar has exactly the scalar-coordinate normalized dual measure. -/
theorem normalizedMeasure_primitiveLine_polar
    (hprimitive : L ⊓ (ℝ ∙ (v : E)).restrictScalars ℤ = ℤ ∙ (v : E)) (C : Set E) :
    latticeNormalizedMeasure (integralDual (intersectionAsSubmodule L (ℝ ∙ (v : E)))) ν
        (StrongDual.polar ℝ ((ℝ ∙ (v : E)).subtype ⁻¹' C)) =
      latticeNormalizedMeasure (integralDual (ℤ ∙ (1 : ℝ))) μ
        (StrongDual.polar ℝ ((fun t : ℝ => t • (v : E)) ⁻¹' C)) := by
  have h := (measurePreserving_primitiveLine_dualCoordinate L v hv μ ν hprimitive).measure_preimage
    (NormedSpace.isClosed_polar ℝ ((ℝ ∙ (v : E)).subtype ⁻¹' C)).measurableSet.nullMeasurableSet
  rw [preimage_polar_primitiveLine] at h
  exact h.symm

end Measure

section Factor

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (ℝ ∙ (v : E))] [BorelSpace (ℝ ∙ (v : E))]
  [MeasurableSpace (StrongDual ℝ (ℝ ∙ (v : E)))]
  [BorelSpace (StrongDual ℝ (ℝ ∙ (v : E)))]
  (η : Measure (ℝ ∙ (v : E))) [η.IsAddHaarMeasure]
  (ν : Measure (StrongDual ℝ (ℝ ∙ (v : E)))) [ν.IsAddHaarMeasure]

include hv in
/-- The actual primitive-line dual polar measure is four divided by the actual normalized length. -/
theorem normalizedMeasure_primitiveLine_polar_toReal_eq_four_div
    (hprimitive : L ⊓ (ℝ ∙ (v : E)).restrictScalars ℤ = ℤ ∙ (v : E))
    {C : Set E} (hC : IsCompact C) (hcC : Convex ℝ C) (hsC : ∀ x ∈ C, -x ∈ C)
    (hvC : (v : E) ∈ C) :
    (latticeNormalizedMeasure (integralDual (intersectionAsSubmodule L (ℝ ∙ (v : E)))) ν
      (StrongDual.polar ℝ ((ℝ ∙ (v : E)).subtype ⁻¹' C))).toReal =
        4 / (latticeNormalizedMeasure (intersectionAsSubmodule L (ℝ ∙ (v : E))) η
          ((ℝ ∙ (v : E)).subtype ⁻¹' C)).toReal := by
  let : MeasurableSpace (StrongDual ℝ ℝ) := borel _
  let : BorelSpace (StrongDual ℝ ℝ) := ⟨rfl⟩
  let μ : Measure (StrongDual ℝ ℝ) := (Module.finBasis ℝ (StrongDual ℝ ℝ)).addHaar
  let : μ.IsAddHaarMeasure := by dsimp [μ]; infer_instance
  let S : Set ℝ := (fun t : ℝ => t • (v : E)) ⁻¹' C
  have hS : IsCompact S :=
    (isClosedEmbedding_smul_left (𝕜 := ℝ) hv).isCompact_preimage hC
  have hcS : Convex ℝ S := hcC.linear_preimage (LinearMap.toSpanSingleton ℝ E (v : E))
  have hsS : ∀ t ∈ S, -t ∈ S := by
    intro t ht
    simpa only [S, mem_preimage, neg_smul] using hsC _ ht
  have h1 : (1 : ℝ) ∈ S := by simpa only [S, mem_preimage, one_smul] using hvC
  rw [normalizedMeasure_primitiveLine_polar L v hv μ ν hprimitive,
    latticeNormalizedMeasure_section_eq_volume_preimage L v hv η hprimitive
      hC.isClosed.measurableSet]
  exact RealIntervalPolar.normalizedMeasure_polar_toReal_eq_four_div μ hS hcS hsS h1

end Factor

end PrimitiveLine

end ArakelovGeometry.GeometryOfNumbers.PrimitiveLineDualMeasure
