/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Archimedean.Euclidean
public import Mathlib.Algebra.Module.ZLattice.Covolume

import Mathlib.Topology.Sheaves.Init

/-!
# Covolumes of original Archimedean diagonal lattices

The Euclidean measure comes from the actual Hermitian completed fibre
norms. Relative indices are transported from the original integral
submodules by their literal diagonal embedding.
-/

@[expose] public section

noncomputable section
open NumberField MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldArchimedeanCovolume

open NumberFieldArchimedeanVectorDiagonal NumberFieldArchimedeanEuclidean AdelicStructure

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]

theorem vectorDiagonalMap_injective :
    Function.Injective (vectorDiagonalMap (K := K) (E := E)) := by
  classical
  let w : InfinitePlace K := Classical.choice inferInstance
  intro x y h
  exact NormFamily.rational_tmul_injective (normalizedInfinitePlacePoint w)
    (congrFun h w)

theorem diagonalLattice_toAddSubgroup (M : Submodule (𝓞 K) E) :
    (diagonalLattice M).toAddSubgroup =
      M.toAddSubgroup.map (vectorDiagonalMap (K := K) (E := E)).toAddMonoidHom := by
  ext z
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, m.property, hm⟩
  · rintro ⟨m, hm, hz⟩
    exact ⟨⟨m, hm⟩, hz⟩

theorem diagonalLattice_mono {M₀ M : Submodule (𝓞 K) E} (h : M₀ ≤ M) :
    diagonalLattice M₀ ≤ diagonalLattice M := by
  rintro z ⟨m, hm⟩
  exact ⟨⟨m, h m.property⟩, hm⟩

theorem diagonalLattice_relIndex (M₀ M : Submodule (𝓞 K) E) :
    (diagonalLattice M₀).toAddSubgroup.relIndex (diagonalLattice M).toAddSubgroup =
      M₀.toAddSubgroup.relIndex M.toAddSubgroup := by
  rw [diagonalLattice_toAddSubgroup, diagonalLattice_toAddSubgroup]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ vectorDiagonalMap_injective

variable [FiniteDimensional K E]

/-- Covolume for the Euclidean volume of the original Hermitian completed product. -/
def euclideanCovolume (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [hξ : ξ.IsHermitian]
    (M : Submodule (𝓞 K) E) : ℝ := by
  letI := euclideanNormedAddCommGroup ξ
  letI := euclideanNormedSpace ξ
  letI := euclideanInnerProduct (ξ := ξ)
  letI : MeasurableSpace (CompletedVectorProduct K E) := borel _
  letI : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
  letI := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
  exact ZLattice.covolume (diagonalLattice M)

theorem euclideanCovolume_pos (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [hξ : ξ.IsHermitian]
    (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    0 < euclideanCovolume ξ M := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct (ξ := ξ)
  let : MeasurableSpace (CompletedVectorProduct K E) := borel _
  let : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
  let := euclidean_discrete_diagonalLattice ξ M hfg hspan
  let := euclidean_isZLattice_diagonalLattice ξ M hfg hspan
  exact ZLattice.covolume_pos (diagonalLattice M)

theorem euclideanCovolume_div_eq_relIndex
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [hξ : ξ.IsHermitian]
    (M₀ M : Submodule (𝓞 K) E) (hfg₀ : M₀.FG)
    (hspan₀ : Submodule.span K (M₀ : Set E) = ⊤) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) (h : M₀ ≤ M) :
    euclideanCovolume ξ M₀ / euclideanCovolume ξ M =
      (M₀.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct (ξ := ξ)
  let : MeasurableSpace (CompletedVectorProduct K E) := borel _
  let : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
  let := euclidean_discrete_diagonalLattice ξ M₀ hfg₀ hspan₀
  let := euclidean_isZLattice_diagonalLattice ξ M₀ hfg₀ hspan₀
  let := euclidean_discrete_diagonalLattice ξ M hfg hspan
  let := euclidean_isZLattice_diagonalLattice ξ M hfg hspan
  simpa only [euclideanCovolume, diagonalLattice_relIndex] using
    ZLattice.covolume_div_covolume_eq_relIndex' (diagonalLattice M₀)
      (diagonalLattice M) (diagonalLattice_mono h)

theorem original_relIndex_pos
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [hξ : ξ.IsHermitian]
    (M₀ M : Submodule (𝓞 K) E) (hfg₀ : M₀.FG)
    (hspan₀ : Submodule.span K (M₀ : Set E) = ⊤) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) (h : M₀ ≤ M) :
    0 < M₀.toAddSubgroup.relIndex M.toAddSubgroup := by
  have hpos := div_pos (euclideanCovolume_pos ξ M₀ hfg₀ hspan₀)
    (euclideanCovolume_pos ξ M hfg hspan)
  rw [euclideanCovolume_div_eq_relIndex ξ M₀ M hfg₀ hspan₀ hfg hspan h] at hpos
  exact_mod_cast hpos

theorem euclideanCovolume_eq_div_relIndex
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [hξ : ξ.IsHermitian]
    (M₀ M : Submodule (𝓞 K) E) (hfg₀ : M₀.FG)
    (hspan₀ : Submodule.span K (M₀ : Set E) = ⊤) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) (h : M₀ ≤ M) :
    euclideanCovolume ξ M = euclideanCovolume ξ M₀ /
      (M₀.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) := by
  have heq := euclideanCovolume_div_eq_relIndex ξ M₀ M hfg₀ hspan₀ hfg hspan h
  have hm : euclideanCovolume ξ M ≠ 0 :=
    ne_of_gt (euclideanCovolume_pos ξ M hfg hspan)
  have hq : (M₀.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (original_relIndex_pos ξ M₀ M hfg₀ hspan₀ hfg hspan h)
  apply (eq_div_iff hq).2
  simpa only [mul_comm] using ((div_eq_iff hm).1 heq).symm

end ArakelovGeometry.NumberFieldArchimedeanCovolume

namespace ArakelovGeometry.NormFamily

open AdelicStructure NumberFieldArchimedeanCovolume

variable {K E : Type*} [Field K] [NumberField K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}

theorem IsDominated.pure_globalBall_euclideanCovolume_pos
    (hdom : ξ.IsDominated) (hultra : ξ.IsUltrametricAtFinitePlaces)
    (hpure : ξ.IsPureAtFinitePlaces)
    (hHerm : ξ.IsHermitian) :
    0 < euclideanCovolume ξ (ξ.globalUnitBallModule) :=
  euclideanCovolume_pos ξ _
    (hdom.pure_normalizedGlobalUnitBall_finite_projective_span hultra hpure).1
    (hdom.pure_normalizedGlobalUnitBall_finite_projective_span hultra hpure).2.2

end ArakelovGeometry.NormFamily
