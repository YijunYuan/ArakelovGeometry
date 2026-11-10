/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
public import ArakelovGeometry.AdelicVectorBundle.Measurability.Density.Basic
import ArakelovGeometry.Analysis.NormedSpace.LinearMapBound
import ArakelovGeometry.Analysis.Tensor.CountableTensorFormula
import Mathlib.CategoryTheory.Category.Init

/-!
# Common countable density in finite field extensions

Adjoining a fixed finite field basis to the image of the common countable
base subfield produces one countable subfield dense at every extending place.
The proof uses the canonical finite coordinate sum on the actual completions.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

universe u v w wι

variable {K : Type u} [Field K] {L : Type w} [Field L] [Algebra K L]
  {ι : Type wι}

/-- One fixed subfield contains the image of the base subfield and every
element of a chosen finite extension basis. -/
def finiteExtensionDenseSubfield (b : Module.Basis ι K L) (K₀ : Subfield K) : Subfield L :=
  Subfield.closure
    (Set.range (fun a : K₀ => algebraMap K L (a : K)) ∪ Set.range b)

/-- The chosen extension subfield is countable. -/
theorem countable_finiteExtensionDenseSubfield (b : Module.Basis ι K L)
    (K₀ : Subfield K) [Countable K₀] [Finite ι] :
    Countable (finiteExtensionDenseSubfield b K₀) :=
  countable_subfield_closure _ ((Set.countable_range _).union (Set.countable_range b))

theorem algebraMap_mem_finiteExtensionDenseSubfield (b : Module.Basis ι K L)
    (K₀ : Subfield K) (a : K₀) :
    algebraMap K L (a : K) ∈ finiteExtensionDenseSubfield b K₀ :=
  Subfield.subset_closure (Or.inl (Set.mem_range_self a))

theorem basis_mem_finiteExtensionDenseSubfield (b : Module.Basis ι K L)
    (K₀ : Subfield K) (i : ι) : b i ∈ finiteExtensionDenseSubfield b K₀ :=
  Subfield.subset_closure (Or.inr (Set.mem_range_self i))

/-- The original rational basis span lies in the same chosen extension subfield. -/
theorem basisSubfieldMap_mem_finiteExtensionDenseSubfield (b : Module.Basis ι K L)
    (K₀ : Subfield K) [Fintype ι] (c : ι → K₀) :
    basisSubfieldMap b K₀ c ∈ finiteExtensionDenseSubfield b K₀ := by
  apply Subfield.sum_mem
  intro i _
  rw [Algebra.smul_def]
  exact Subfield.mul_mem _ (algebraMap_mem_finiteExtensionDenseSubfield b K₀ (c i))
    (basis_mem_finiteExtensionDenseSubfield b K₀ i)

/-- A dense base subfield, combined with a fixed finite field basis, gives
a dense rational set in each actual extending completion. -/
theorem denseRange_finiteExtension_basisSubfieldMap (b : Module.Basis ι K L)
    (K₀ : Subfield K) [Fintype ι] (w : AbsoluteValue L ℝ)
    (hK₀ : DenseRange (fun a : K₀ =>
      algebraMap K (w.under K).Completion (a : K))) :
    DenseRange (fun c : ι → K₀ => algebraMap L w.Completion (basisSubfieldMap b K₀ c)) := by
  let d := Fintype.linearCombination (w.under K).Completion
    (fun i => algebraMap L w.Completion (b i))
  have hs : Function.Surjective d :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination
      (w.under K).Completion _).mp
      (w.span_coe_basis_eq_top K b)
  have hc : Continuous d := (linearMapToNormedAddGroupHom d).continuous
  have hd : DenseRange (fun c : ι → K₀ =>
      fun i => algebraMap K (w.under K).Completion (c i : K)) :=
    DenseRange.piMap (fun _ => hK₀)
  have h := hs.denseRange.comp hd hc
  have he : (fun c : ι → K₀ =>
      d (fun i => algebraMap K (w.under K).Completion (c i : K))) =
      fun c => algebraMap L w.Completion (basisSubfieldMap b K₀ c) := by
    funext c
    simp only [d, Fintype.linearCombination_apply, basisSubfieldMap, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Algebra.smul_def, Algebra.smul_def]
    rw [map_mul, ← IsScalarTower.algebraMap_apply K (w.under K).Completion w.Completion,
      ← IsScalarTower.algebraMap_apply K L w.Completion]
  change DenseRange (fun c : ι → K₀ =>
    d (fun i => algebraMap K (w.under K).Completion (c i : K))) at h
  rw [he] at h
  exact h

/-- The single chosen extension subfield is dense in every completion where
the original base subfield is dense. -/
theorem denseRange_finiteExtensionDenseSubfield (b : Module.Basis ι K L)
    (K₀ : Subfield K) [Finite ι] (w : AbsoluteValue L ℝ)
    (hK₀ : DenseRange (fun a : K₀ =>
      algebraMap K (w.under K).Completion (a : K))) :
    DenseRange (fun a : finiteExtensionDenseSubfield b K₀ =>
      algebraMap L w.Completion (a : L)) := by
  let := Fintype.ofFinite ι
  apply Dense.mono (hd := denseRange_finiteExtension_basisSubfieldMap b K₀ w hK₀)
  rintro _ ⟨c, rfl⟩
  exact ⟨⟨basisSubfieldMap b K₀ c,
    basisSubfieldMap_mem_finiteExtensionDenseSubfield b K₀ c⟩, rfl⟩

variable {S : AdelicStructure.{u, v} K}

/-- Actual extending places inherit the density of the base subfield in
the same fixed extension subfield. -/
theorem AdelicStructure.isDenseSubfieldAt_finiteExtensionDenseSubfield
    [Algebra.IsAlgebraic K L] [Finite ι] (b : Module.Basis ι K L) (K₀ : Subfield K)
    (x : S.ParameterSpaceExtension L) (hK₀ : S.IsDenseSubfieldAt K₀ x.base) :
    (S.algebraicExtension L).IsDenseSubfieldAt (finiteExtensionDenseSubfield b K₀) x := by
  have hd : DenseRange (fun a : K₀ =>
      algebraMap K (x.abv.under K).Completion (a : K)) := by
    rw [x.restrict_eq]
    exact hK₀
  exact denseRange_finiteExtensionDenseSubfield b K₀ x.abv hd

/-- Finite algebraic extension preserves one common countable dense
subfield, with no restriction on the places or their valuations. -/
theorem AdelicStructure.HasCommonCountableDenseSubfield.algebraicExtension_of_finiteDimensional
    [FiniteDimensional K L] (hS : S.HasCommonCountableDenseSubfield) :
    (S.algebraicExtension L).HasCommonCountableDenseSubfield := by
  obtain ⟨K₀, hc, hd⟩ := hS
  let : Countable K₀ := hc
  let b := Module.finBasis K L
  refine ⟨finiteExtensionDenseSubfield b K₀, countable_finiteExtensionDenseSubfield b K₀, ?_⟩
  intro x
  change S.ParameterSpaceExtension L at x
  exact AdelicStructure.isDenseSubfieldAt_finiteExtensionDenseSubfield b K₀ x (hd x.base)

end ArakelovGeometry
