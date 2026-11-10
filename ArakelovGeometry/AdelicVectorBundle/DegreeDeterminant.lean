/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree

/-!
# Degree from measurability of the actual determinant

The canonical determinant adelic line defines vector degree whenever its actual
norm family is measurable. The usual discrete-or-common-density degree context
is a sufficient producer of this analytic property and gives the same degree.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Vector degree is the degree of the canonical actual determinant line
whenever its actual norm family is measurable. -/
def degreeOfMeasurableDeterminant [S.IsProper] (V : AdelicVectorBundle S E)
    (hdet : V.toNormFamily.determinant.IsMeasurable)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) : ℝ :=
  (V.determinant hdet hN).lineDegree (V.determinant_isLine hdet hN)

/-- The usual degree context produces determinant measurability and the
same degree; the canonical determinant adelic line is unchanged. -/
theorem degreeOfMeasurableDeterminant_eq_degree [S.IsProper]
    (V : AdelicVectorBundle S E) (hdet : V.toNormFamily.determinant.IsMeasurable)
    (hbase : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.degreeOfMeasurableDeterminant hdet hN = V.degree hbase hN := rfl

/-- Every nonzero actual rational determinant generator computes the
degree from the integral of its actual determinant log norm. -/
theorem degreeOfMeasurableDeterminant_eq_neg_integral [S.IsProper]
    (V : AdelicVectorBundle S E) (hdet : V.toNormFamily.determinant.IsMeasurable)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (s : {x : ⋀[K]^(Module.finrank K E) E // x ≠ 0}) :
    V.degreeOfMeasurableDeterminant hdet hN =
      -(∫ ω, V.toNormFamily.determinant.logNorm s.val ω ∂S.v) :=
  lineDegree_eq_neg_integral _ _ s

end

end ArakelovGeometry.AdelicVectorBundle
