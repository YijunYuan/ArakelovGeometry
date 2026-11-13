/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Minima.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Tower.Transport

import Mathlib.CategoryTheory.Category.Init

/-!
# Rational vector degrees and logarithmic minima through the actual tower

The genuine tower pullback keeps the scalar field and rational vector space.
The actual measure-preserving place equivalence preserves section degree,
threshold spans, logarithmic minima and their completed filtration. No
properness or regularity hypothesis on intermediate place spaces is needed.
This is the place-transport part of absolute-minimum invariance; tensor
associator and closure-field identification are separate obligations.
-/

@[expose] public section

open MeasureTheory
noncomputable section

namespace ArakelovGeometry

universe u wL wE
variable {K : Type u} [Field K] {S : AdelicStructure K}
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module L E] [FiniteDimensional L E]

namespace NormFamily

/-- Actual nonzero-section degree is preserved by the genuine tower place
map and measure, using produced domination and measurability. -/
theorem vectorDegree_towerPullback (ξ : NormFamily (S.algebraicExtension L) E)
    [hd : ξ.IsDominated] [hm : ξ.IsMeasurable] (F : IntermediateField K L)
    (s : {x : E // x ≠ 0}) :
    (ξ.towerPullback F).vectorDegree (hd := (hd.towerPullback F)) (hm := (hm.towerPullback F)) s =
      ξ.vectorDegree s := by
  rw [vectorDegree_eq_neg_integral, vectorDegree_eq_neg_integral, towerPullback_logNorm]
  exact congrArg (fun t : ℝ => -t)
    ((measurePreserving_scalarExtensionTowerPlace (S := S) F).integral_comp
      (AdelicStructure.Algebraic.towerMeasurableEquiv S F).measurableEmbedding _)

end NormFamily
namespace AdelicVectorBundle

/-- The same actual rational vector has equal degree on direct and iterated
curves; intermediate place regularity and properness are not assumptions. -/
theorem vectorDegree_towerPullback (V : AdelicVectorBundle (S.algebraicExtension L))
    (F : IntermediateField K L) (s : {x : V // x ≠ 0}) :
    (V.towerPullback F).vectorDegree s = V.vectorDegree s :=
  V.toNormFamily.vectorDegree_towerPullback F s

/-- Actual degree-threshold generators, and hence their actual spans, agree. -/
theorem degreeThresholdSpan_towerPullback (V : AdelicVectorBundle (S.algebraicExtension L))
    (F : IntermediateField K L) (t : ℝ) :
    (V.towerPullback F).degreeThresholdSpan t = V.degreeThresholdSpan t := by
  simp only [degreeThresholdSpan, vectorDegree_towerPullback]

/-- Every natural-index minimum is preserved, including empty and unbounded
cuts; no threshold-attainment or finite-minimum premise is used. -/
theorem logarithmicMinimum_towerPullback (V : AdelicVectorBundle (S.algebraicExtension L))
    (F : IntermediateField K L) (i : ℕ) :
    (V.towerPullback F).logarithmicMinimum i = V.logarithmicMinimum i := by
  unfold logarithmicMinimum
  apply iSup_congr
  intro t
  have hr := congrArg (fun U : Submodule L V => Module.finrank L U)
    (V.degreeThresholdSpan_towerPullback F t)
  rw [hr]

/-- The actual first minimum is preserved, including its rank-zero bottom. -/
theorem maximalLogarithmicMinimum_towerPullback
    (V : AdelicVectorBundle (S.algebraicExtension L)) (F : IntermediateField K L) :
    (V.towerPullback F).maximalLogarithmicMinimum = V.maximalLogarithmicMinimum :=
  V.logarithmicMinimum_towerPullback F 1

/-- The actual last minimum is preserved, including its rank-zero top. -/
theorem minimalLogarithmicMinimum_towerPullback
    (V : AdelicVectorBundle (S.algebraicExtension L)) (F : IntermediateField K L) :
    (V.towerPullback F).minimalLogarithmicMinimum = V.minimalLogarithmicMinimum :=
  V.logarithmicMinimum_towerPullback F (Module.finrank L V)

/-- The source's completed filtration is preserved as an actual subspace. -/
theorem minimaFiltration_towerPullback (V : AdelicVectorBundle (S.algebraicExtension L))
    (F : IntermediateField K L) (t : ℝ) :
    (V.towerPullback F).minimaFiltration t = V.minimaFiltration t := by
  simp only [minimaFiltration, degreeThresholdSpan_towerPullback]

end AdelicVectorBundle
end ArakelovGeometry
