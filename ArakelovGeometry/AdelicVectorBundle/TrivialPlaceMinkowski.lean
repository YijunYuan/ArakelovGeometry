/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.LineVectorDegree
public import ArakelovGeometry.AdelicVectorBundle.StrongMinkowskiImplication
public import ArakelovGeometry.AdelicVectorBundle.TrivialPlaceAdaptedBasis

/-!
# Genuine universal Minkowski level zero at a mass-one trivial place

The actual minimal-slope formula and genuine vector norms give the global
strong property without a level assumption. The proved zero-Archimedean-mass
implication produces the ordinary property. Both actual endpoint identities
include zero rank. These results concern a nonempty concrete curve.
-/

@[expose] public section

open MeasureTheory
noncomputable section
namespace ArakelovGeometry
universe u w
variable {K : Type u} [Field K]

namespace AdelicVectorBundle
/-- The degree integral over the nonempty mass-one atom is evaluation of
its actual completed norm. -/
theorem vectorDegree_singleTrivialPlace_eq_neg_log
    {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (V : AdelicVectorBundle (AdelicStructure.singleTrivialPlace K) E)
    (x : {x : E // x ≠ 0}) :
    V.vectorDegree x = -Real.log (V.toNormFamily.trivialSeminorm x.val) := by
  simp only [AdelicVectorBundle.vectorDegree, NormFamily.vectorDegree_eq_neg_integral,
    AdelicStructure.integral_singleTrivialPlace, NormFamily.logNorm,
    NormFamily.trivialSeminorm_apply]
  rfl
end AdelicVectorBundle

namespace AdelicStructure
/-- Every actual positive-rank admissible bundle satisfies the strong
inequality at zero, using an actual full basis and the produced norm bound. -/
theorem singleTrivialPlace_hasStrongMinkowskiPropertyAtLevel_zero (K : Type u) [Field K] :
    (singleTrivialPlace K).HasStrongMinkowskiPropertyAtLevel.{u, 0, w}
      (Or.inl inferInstance) (singleTrivialPlace_normalized K) 0 := by
  refine ⟨le_rfl, fun E _ _ _ V hr hV => ?_⟩
  obtain ⟨x, hx, he, hR, hbound⟩ :=
    V.toNormFamily.exists_nonzero_trivialSeminorm_eq_sSup_range hV hr
  let b := Module.finBasis K E
  let s : Fin (Module.finrank K E) → {x : E // x ≠ 0} :=
    fun i => ⟨b i, b.ne_zero i⟩
  have hd : ∀ i, -Real.log (sSup (Set.range V.toNormFamily.trivialSeminorm)) ≤
      V.vectorDegree (s i) := by
    intro i
    rw [V.vectorDegree_singleTrivialPlace_eq_neg_log]
    apply neg_le_neg
    apply Real.log_le_log
    · rw [NormFamily.trivialSeminorm_apply]
      exact V.toNormFamily.norm_rational_pos PUnit.unit (b.ne_zero i)
    · exact hbound (b i)
  have hm := V.coe_le_logarithmicMinimum_of_linearIndependent s b.linearIndependent hd
  rw [V.minimalSlope_eq_neg_log_sSup_range_of_isUltrametric
    (Or.inl inferInstance) (singleTrivialPlace_normalized K) hV hr]
  simpa only [zero_mul, EReal.coe_zero, sub_zero,
    AdelicVectorBundle.minimalLogarithmicMinimum] using hm

/-- The genuine strong property feeds the corrected implication at zero
Archimedean mass, giving the universal ordinary level without assumptions. -/
theorem singleTrivialPlace_hasMinkowskiPropertyAtLevel_zero (K : Type u) [Field K] :
    (singleTrivialPlace K).HasMinkowskiPropertyAtLevel.{u, 0, w}
      (Or.inl inferInstance) (singleTrivialPlace_normalized K) 0 := by
  have hz : (singleTrivialPlace K).v (singleTrivialPlace K).Ωinf = 0 := by
    rw [singleTrivialPlace_Ωinf, measure_empty]
  exact HasStrongMinkowskiPropertyAtLevel.minkowski_of_archimedeanMass_eq_zero
    (singleTrivialPlace_hasStrongMinkowskiPropertyAtLevel_zero K) hz
end AdelicStructure

namespace AdelicVectorBundle
variable {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Equality of the actual last minimum and minimal slope for all ranks. -/
theorem minimalLogarithmicMinimum_eq_minimalSlope_singleTrivialPlace
    (V : AdelicVectorBundle (AdelicStructure.singleTrivialPlace K) E)
    (hV : V.toNormFamily.IsUltrametric) :
    V.minimalLogarithmicMinimum = V.minimalSlope (Or.inl inferInstance)
      (AdelicStructure.singleTrivialPlace_normalized K) := by
  by_cases hz : Module.finrank K E = 0
  · rw [V.minimalLogarithmicMinimum_eq_top_of_finrank_eq_zero hz,
      V.minimalSlope_eq_top_of_finrank_eq_zero (Or.inl inferInstance)
        (AdelicStructure.singleTrivialPlace_normalized K) hz]
  have h := (AdelicStructure.singleTrivialPlace_hasStrongMinkowskiPropertyAtLevel_zero K).2
    E V (Nat.pos_of_ne_zero hz) hV
  simp only [zero_mul, EReal.coe_zero, sub_zero] at h
  exact le_antisymm (V.minimalLogarithmicMinimum_le_minimalSlope (Or.inl inferInstance)
    (AdelicStructure.singleTrivialPlace_normalized K)) h

/-- Equality of the actual first minimum and maximal slope for all ranks. -/
theorem maximalLogarithmicMinimum_eq_maximalSlope_singleTrivialPlace
    (V : AdelicVectorBundle (AdelicStructure.singleTrivialPlace K) E)
    (hV : V.toNormFamily.IsUltrametric) :
    V.maximalLogarithmicMinimum = V.maximalSlope (Or.inl inferInstance)
      (AdelicStructure.singleTrivialPlace_normalized K) := by
  by_cases hz : Module.finrank K E = 0
  · rw [V.maximalLogarithmicMinimum_eq_bot_of_finrank_eq_zero hz,
      V.maximalSlope_eq_bot_of_finrank_eq_zero (Or.inl inferInstance)
        (AdelicStructure.singleTrivialPlace_normalized K) hz]
  have h := (AdelicStructure.singleTrivialPlace_hasMinkowskiPropertyAtLevel_zero K).2
    E V (Nat.pos_of_ne_zero hz) hV
  simp only [zero_mul, EReal.coe_zero, sub_zero] at h
  exact le_antisymm (V.maximalLogarithmicMinimum_le_maximalSlope (Or.inl inferInstance)
    (AdelicStructure.singleTrivialPlace_normalized K)) h
end AdelicVectorBundle
end ArakelovGeometry
