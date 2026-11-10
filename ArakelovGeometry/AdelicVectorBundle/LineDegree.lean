/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.BundleTensorLine
import ArakelovGeometry.AdelicVectorBundle.VectorDegree
import ArakelovGeometry.AdelicVectorBundle.ScalarLine
import ArakelovGeometry.AdelicVectorBundle.BundleHermitianTensor

/-!
# Degrees of adelic lines

The line degree is the vector degree of a chosen actual rational generator.
The product formula proves independence of this choice. Duality and finite
tensor additivity use the exact completed norm formulas, including the empty
tensor family. This implements the line-degree cone of Section 4.3.1.
-/

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w w' wι

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- A rational generator of a line, chosen from its finite basis. -/
noncomputable def lineGenerator (V : AdelicVectorBundle S E) (hV : V.IsLine) :
    {x : E // x ≠ 0} := by
  let i : Fin (Module.finrank K E) := ⟨0, by change Module.finrank K E = 1 at hV; omega⟩
  exact ⟨Module.finBasis K E i, (Module.finBasis K E).ne_zero i⟩

/-- The Arakelov degree of an adelic line over a proper curve. -/
noncomputable def lineDegree [S.IsProper] (V : AdelicVectorBundle S E) (hV : V.IsLine) : ℝ :=
  V.toNormFamily.vectorDegree V.isDominated V.isMeasurable (V.lineGenerator hV)

/-- Every nonzero rational generator computes the same line degree. -/
theorem lineDegree_eq_vectorDegree [S.IsProper] (V : AdelicVectorBundle S E)
    (hV : V.IsLine) (s : {x : E // x ≠ 0}) :
    V.lineDegree hV = V.toNormFamily.vectorDegree V.isDominated V.isMeasurable s :=
  V.toNormFamily.vectorDegree_eq_of_finrank_one V.isDominated V.isMeasurable hV _ s

/-- The degree formula for an arbitrary rational generator. -/
theorem lineDegree_eq_neg_integral [S.IsProper] (V : AdelicVectorBundle S E)
    (hV : V.IsLine) (s : {x : E // x ≠ 0}) :
    V.lineDegree hV = -(∫ ω, V.toNormFamily.logNorm s.val ω ∂S.v) := by
  rw [lineDegree_eq_vectorDegree V hV s, NormFamily.vectorDegree_eq_neg_integral]

/-- A rational linear isomorphism preserving completed norms preserves line degree. -/
theorem lineDegree_eq_of_norm_rational_eq [S.IsProper]
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hV : V.IsLine) (hW : W.IsLine) (e : E ≃ₗ[K] F)
    (he : ∀ ω x, V.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) =
      W.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] e x)) :
    V.lineDegree hV = W.lineDegree hW := by
  let x := V.lineGenerator hV
  have hx : e x.val ≠ 0 := by
    intro h
    apply x.property
    exact e.injective (h.trans e.map_zero.symm)
  rw [lineDegree_eq_neg_integral V hV x,
    lineDegree_eq_neg_integral W hW ⟨e x.val, hx⟩]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω ↦ congrArg Real.log (he ω x.val)

/-- A line with a rational generator of norm one everywhere has degree zero. -/
theorem lineDegree_eq_zero_of_norm_eq_one [S.IsProper] (V : AdelicVectorBundle S E)
    (hV : V.IsLine) (s : {x : E // x ≠ 0})
    (hs : ∀ ω, V.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] s.val) = 1) :
    V.lineDegree hV = 0 := by
  rw [lineDegree_eq_neg_integral V hV s]
  simp only [NormFamily.logNorm, hs, Real.log_one, integral_zero, neg_zero]

/-- The actual scalar adelic line has degree zero. -/
@[simp]
theorem lineDegree_scalarLine [S.IsProper] :
    (scalarLine S).lineDegree (scalarLine_isLine S) = 0 := by
  apply lineDegree_eq_zero_of_norm_eq_one _ _ ⟨1, one_ne_zero⟩
  intro ω
  simp only [scalarLine_norm_tmul_one, norm_one]

/-- Dualizing an adelic line negates its degree. -/
theorem lineDegree_dualLine [S.IsProper] (V : AdelicVectorBundle S E) (hV : V.IsLine) :
    (V.dualLine hV).lineDegree (V.dualLine_isLine hV) = -V.lineDegree hV := by
  let x := V.lineGenerator hV
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one K x.property
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    exact zero_ne_one hℓ
  rw [lineDegree_eq_neg_integral _ _ ⟨ℓ, hℓ0⟩, lineDegree_eq_neg_integral V hV x]
  change -(∫ ω, V.toNormFamily.dual.logNorm ℓ ω ∂S.v) = _
  simp only [V.toNormFamily.dual_logNorm_eq_neg hV hℓ, integral_neg]

variable {ι : Type wι} [Fintype ι]
  {G : ι → Type w} [∀ i, AddCommGroup (G i)] [∀ i, Module K (G i)]
  [∀ i, FiniteDimensional K (G i)]

/-- Finite tensor products of adelic lines have additive degree, including the empty family.
The bundle carries the actual equal projective, injective and mixed tensor norms. -/
theorem lineDegree_tensorLines [S.IsProper] (V : ∀ i, AdelicVectorBundle S (G i))
    (hV : ∀ i, (V i).IsLine) :
    (tensorLines V hV).lineDegree (tensorLines_isLine V hV) = ∑ i, (V i).lineDegree (hV i) := by
  classical
  let x := fun i ↦ ((V i).lineGenerator (hV i)).val
  have hx : ∀ i, x i ≠ 0 := fun i ↦ ((V i).lineGenerator (hV i)).property
  rw [lineDegree_eq_neg_integral _ _
    ⟨⨂ₜ[K] i, x i, NormFamily.tensor_generators_ne_zero hV x hx⟩]
  simp_rw [tensorLines_toNormFamily_eq_injectiveTensor,
    NormFamily.injectiveTensor_logNorm_generators _ hV x hx]
  rw [integral_finsetSum _ (fun i _ ↦ (V i).integrable_logNorm (x i))]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact (lineDegree_eq_neg_integral (V i) (hV i) ⟨x i, hx i⟩).symm

/-- Orthogonal tensor lines have the same additive degree, using their proved equality
with the actual mixed tensor bundle. -/
theorem lineDegree_orthogonalTensorLines [S.IsProper]
    (V : ∀ i, AdelicVectorBundle S (G i)) (hV : ∀ i, (V i).IsLine)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (orthogonalTensorLines V hV hS).lineDegree (orthogonalTensorLines_isLine V hV hS) =
      ∑ i, (V i).lineDegree (hV i) := by
  simp_rw [orthogonalTensorLines_eq_tensorLines]
  exact lineDegree_tensorLines V hV

end ArakelovGeometry.AdelicVectorBundle
