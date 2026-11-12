/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Archimedean.WeightedCovolume

import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Topology.Sheaves.Init

/-! # Minkowski's convex-body theorem on the original arithmetic diagonal lattice -/

@[expose] public section

noncomputable section
open NumberField MeasureTheory
open scoped TensorProduct ENNReal

namespace ArakelovGeometry.NumberFieldArithmeticMinkowski

open AdelicStructure NumberFieldArchimedeanVectorDiagonal NumberFieldArchimedeanEuclidean
  NumberFieldArchimedeanCovolume NumberFieldArchimedeanWeightedCovolume

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E]
  [Module K E] [FiniteDimensional K E]

/-- The canonical ordinary fundamental-domain measure is the actual real covolume. -/
theorem euclideanVolume_fundamentalDomain
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [hξ : ξ.IsHermitian]
    (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    euclideanVolume ξ (diagonalFundamentalDomain M hfg hspan) =
      ENNReal.ofReal (euclideanCovolume ξ M) := by
  let : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  let : IsScalarTower ℚ K E := IsScalarTower.of_compHom ℚ K E
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct (ξ := ξ)
  let : MeasurableSpace (CompletedVectorProduct K E) := borel _
  let : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
  rw [euclideanCovolume_eq_fundamentalDomain ξ M hfg hspan]
  symm
  apply ENNReal.ofReal_toReal
  change volume (ZSpan.fundamentalDomain (diagonalLatticeBasis M hfg hspan)) ≠ ⊤
  exact (ZSpan.fundamentalDomain_isBounded (diagonalLatticeBasis M hfg hspan)).measure_lt_top.ne

/-- Minkowski's theorem produces a vector of the original integral lattice in any actual
compact symmetric convex body of sufficient ordinary volume. -/
theorem exists_integral_nonzero_of_convex_volume
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [hξ : ξ.IsHermitian]
    (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) (hrank : 0 < Module.finrank K E)
    (B : Set (CompletedVectorProduct K E))
    (hcompact : letI := euclideanNormedAddCommGroup ξ; IsCompact B)
    (hconvex : Convex ℝ B) (hsymm : ∀ z ∈ B, -z ∈ B)
    (hvolume : ENNReal.ofReal (euclideanCovolume ξ M) *
      2 ^ (Module.finrank ℚ K * Module.finrank K E) ≤ euclideanVolume ξ B) :
    ∃ s : E, s ∈ M ∧ s ≠ 0 ∧ vectorDiagonalMap (K := K) (E := E) s ∈ B := by
  let : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  let : IsScalarTower ℚ K E := IsScalarTower.of_compHom ℚ K E
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct (ξ := ξ)
  let : MeasurableSpace (CompletedVectorProduct K E) := borel _
  let : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
  let := euclidean_discrete_diagonalLattice ξ M hfg hspan
  let := euclidean_isZLattice_diagonalLattice ξ M hfg hspan
  let : Nontrivial (CompletedVectorProduct K E) := Module.nontrivial_of_finrank_pos
    (by rw [vectorDiagonal_dimension]; exact Nat.mul_pos Module.finrank_pos hrank)
  have hd : IsAddFundamentalDomain (diagonalLattice M)
      (ZSpan.fundamentalDomain (diagonalLatticeBasis M hfg hspan)) volume := by
    rw [diagonalLattice_eq_integerSpan M hfg hspan]
    exact ZSpan.isAddFundamentalDomain _ volume
  have hv : volume (ZSpan.fundamentalDomain (diagonalLatticeBasis M hfg hspan)) *
      2 ^ Module.finrank ℝ (CompletedVectorProduct K E) ≤ volume B := by
    change euclideanVolume ξ (diagonalFundamentalDomain M hfg hspan) *
      2 ^ Module.finrank ℝ (CompletedVectorProduct K E) ≤ euclideanVolume ξ B
    rw [euclideanVolume_fundamentalDomain, vectorDiagonal_dimension]
    exact hvolume
  let : Countable M := (NumberFieldFullLattice.integerBasis M hfg).repr.injective.countable
  let f : M → (diagonalLattice M).toAddSubgroup :=
    fun m => ⟨vectorDiagonalMap (K := K) (E := E) (m : E), ⟨m, rfl⟩⟩
  let : Countable (diagonalLattice M).toAddSubgroup :=
    Function.Surjective.countable (f := f) (by
      intro z
      obtain ⟨m, hm⟩ := z.property
      exact ⟨m, Subtype.ext hm⟩)
  obtain ⟨z, hzne, hzB⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      (L := (diagonalLattice M).toAddSubgroup) hd hsymm hconvex hcompact hv
  obtain ⟨m, hm⟩ := z.property
  change vectorDiagonalMap (K := K) (E := E) (m : E) = (z : CompletedVectorProduct K E) at hm
  refine ⟨(m : E), m.property, ?_, ?_⟩
  · intro hmzero
    apply hzne
    apply Subtype.ext
    change (z : CompletedVectorProduct K E) = 0
    rw [← hm]
    rw [hmzero, map_zero]
  · rw [hm]
    exact hzB

end ArakelovGeometry.NumberFieldArithmeticMinkowski
