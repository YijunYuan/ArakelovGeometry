/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.ScalarLine
public import ArakelovGeometry.AdelicVectorBundle.Construction.Tensor.Hermitian
public import ArakelovGeometry.AdelicVectorBundle.Degree.Vector

import ArakelovGeometry.AdelicVectorBundle.NormFamily.Line
import ArakelovGeometry.AdelicVectorBundle.Tensor.Line
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Degrees of adelic lines

The line degree is the vector degree of a chosen actual rational generator.
The product formula proves independence of this choice. Duality and finite
tensor additivity use the exact completed norm formulas, including the empty
tensor family. This implements the line-degree cone of Section 4.3.1.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w w' wι

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- A rational generator of a line, chosen from its finite basis. -/
noncomputable def lineGenerator (V : AdelicVectorBundle S) [hV : V.IsLine] :
    {x : V // x ≠ 0} := by
  have hr : Module.finrank K V = 1 := hV.rank_eq_one
  let i : Fin (Module.finrank K V) := ⟨0, by omega⟩
  exact ⟨Module.finBasis K V i, (Module.finBasis K V).ne_zero i⟩

/-- The Arakelov degree of an adelic line over a proper curve. -/
noncomputable def lineDegree [S.IsProper] (V : AdelicVectorBundle S) [hV : V.IsLine] : ℝ :=
  V.toNormFamily.vectorDegree (V.lineGenerator)

/-- Every nonzero rational generator computes the same line degree. -/
theorem lineDegree_eq_vectorDegree [S.IsProper] (V : AdelicVectorBundle S)
    [hV : V.IsLine] (s : {x : V // x ≠ 0}) :
    V.lineDegree = V.toNormFamily.vectorDegree s :=
  V.toNormFamily.vectorDegree_eq_of_finrank_one hV.rank_eq_one _ s

/-- The degree formula for an arbitrary rational generator. -/
theorem lineDegree_eq_neg_integral [S.IsProper] (V : AdelicVectorBundle S)
    [hV : V.IsLine] (s : {x : V // x ≠ 0}) :
    V.lineDegree = -(∫ ω, V.toNormFamily.logNorm s.val ω ∂S.v) := by
  rw [lineDegree_eq_vectorDegree V s, NormFamily.vectorDegree_eq_neg_integral]

/-- A rational linear isomorphism preserving completed norms preserves line degree. -/
theorem lineDegree_eq_of_norm_rational_eq [S.IsProper]
    (V : AdelicVectorBundle.{w} S) (W : AdelicVectorBundle.{w'} S)
    [hV : V.IsLine] [hW : W.IsLine] (e : V ≃ₗ[K] W)
    (he : ∀ ω x, V.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) =
      W.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] e x)) :
    V.lineDegree = W.lineDegree := by
  let x := V.lineGenerator
  have hx : e x.val ≠ 0 := by
    intro h
    apply x.property
    exact e.injective (h.trans e.map_zero.symm)
  rw [lineDegree_eq_neg_integral V x,
    lineDegree_eq_neg_integral W ⟨e x.val, hx⟩]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω ↦ congrArg Real.log (he ω x.val)

/-- A line with a rational generator of norm one everywhere has degree zero. -/
theorem lineDegree_eq_zero_of_norm_eq_one [S.IsProper] (V : AdelicVectorBundle S)
    [hV : V.IsLine] (s : {x : V // x ≠ 0})
    (hs : ∀ ω, V.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] s.val) = 1) :
    V.lineDegree = 0 := by
  rw [lineDegree_eq_neg_integral V s]
  simp only [NormFamily.logNorm, hs, Real.log_one, integral_zero, neg_zero]

/-- The actual scalar adelic line has degree zero. -/
@[simp]
theorem lineDegree_scalarLine [S.IsProper] :
    (scalarLine S).lineDegree (hV := (scalarLine_isLine S)) = 0 := by
  apply lineDegree_eq_zero_of_norm_eq_one _ ⟨(1 : K), one_ne_zero⟩
  intro ω
  exact (scalarLine_norm_tmul_one S ω (1 : (S.ϕ ω).Completion)).trans (norm_one)

/-- Dualizing an adelic line negates its degree. -/
theorem lineDegree_dualLine [S.IsProper] (V : AdelicVectorBundle S) [hV : V.IsLine] :
    (V.dualLine).lineDegree (hV := (V.dualLine_isLine)) = -V.lineDegree := by
  let x := V.lineGenerator
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one K x.property
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    exact zero_ne_one hℓ
  rw [lineDegree_eq_neg_integral _ ⟨ℓ, hℓ0⟩, lineDegree_eq_neg_integral V x]
  change -(∫ ω, V.toNormFamily.dual.logNorm ℓ ω ∂S.v) = _
  simp only [V.toNormFamily.dual_logNorm_eq_neg hV.rank_eq_one hℓ, integral_neg]

variable {ι : Type wι} [Fintype ι]
  {G : ι → Type w} [∀ i, AddCommGroup (G i)] [∀ i, Module K (G i)]
  [∀ i, FiniteDimensional K (G i)]

/-- Finite tensor products of adelic lines have additive degree, including the empty family.
The bundle carries the actual equal projective, injective and mixed tensor norms. -/
theorem lineDegree_tensorLines [S.IsProper] (V : ι → AdelicVectorBundle S)
    [hV : ∀ i, (V i).IsLine] :
    (tensorLines V).lineDegree (hV := (tensorLines_isLine V)) = ∑ i, (V i).lineDegree
        (hV := (hV i)) := by
  classical
  let x := fun i ↦ ((V i).lineGenerator (hV := (hV i))).val
  have hx : ∀ i, x i ≠ 0 := fun i ↦ ((V i).lineGenerator (hV := (hV i))).property
  rw [lineDegree_eq_neg_integral _
    ⟨⨂ₜ[K] i, x i, NormFamily.tensor_generators_ne_zero (fun i ↦ (hV i).rank_eq_one) x hx⟩]
  change -(∫ ω, (NormFamily.mixedTensor (fun i ↦ (V i).toNormFamily)).logNorm
    (⨂ₜ[K] i, x i) ω ∂S.v) = _
  rw [NormFamily.mixedTensor_eq_injectiveTensor_of_finrank_one
    (fun i ↦ (V i).toNormFamily) (fun i ↦ (hV i).rank_eq_one)]
  simp_rw [NormFamily.injectiveTensor_logNorm_generators
    (fun i ↦ (V i).toNormFamily) (fun i ↦ (hV i).rank_eq_one) x hx]
  rw [integral_finsetSum _ (fun i _ ↦ (V i).integrable_logNorm (x i))]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact (lineDegree_eq_neg_integral (V i) (hV := (hV i)) ⟨x i, hx i⟩).symm

/-- Orthogonal tensor lines have the same additive degree, using their proved equality
with the actual mixed tensor bundle. -/
theorem lineDegree_orthogonalTensorLines [S.IsProper]
    (V : ι → AdelicVectorBundle S) [hV : ∀ i, (V i).IsLine]
    [hS : S.IsArchimedeanNormalized] :
    (orthogonalTensorLines V).lineDegree (hV := (orthogonalTensorLines_isLine V)) =
      ∑ i, (V i).lineDegree (hV := (hV i)) := by
  simp_rw [orthogonalTensorLines_eq_tensorLines]
  exact lineDegree_tensorLines V

end ArakelovGeometry.AdelicVectorBundle
