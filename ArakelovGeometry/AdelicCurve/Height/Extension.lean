/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Height.Affine
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.FiniteProjection

/-!
# Heights under algebraic extension

The extension measures preserve heights of base tuples, and finite embedding
projections identify the heights of conjugates, including in inseparable
extensions. These results use the existing extension theory of Sections 3.3–3.4.

Reference: Chen–Moriwaki, Definition 3.5.1 and Lemma 3.5.4.
-/

namespace ArakelovGeometry.AdelicStructure

open MeasureTheory

variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

theorem localHeight_algebraicExtension (a : ι → K) (x : ParameterSpaceExtension AS L) :
    (AS.algebraicExtension L).localHeight (fun i ↦ algebraMap K L (a i)) x =
      AS.localHeight a x.base := by
  unfold localHeight
  apply Finset.sup'_congr _ rfl
  intro i _
  change x.abv (algebraMap K L (a i)) = AS.ϕ x.base (a i)
  exact congrArg (fun w : AbsoluteValue K ℝ ↦ w (a i)) x.restrict_eq

/-- Algebraic extension preserves the height of every tuple over the base field. -/
theorem logHeight_algebraicExtension (a : ι → K) :
    (AS.algebraicExtension L).logHeight (fun i ↦ algebraMap K L (a i)) =
      AS.logHeight a := by
  change (∫ x, Real.log ((AS.algebraicExtension L).localHeight _ x)
    ∂Algebraic.measure AS L) = AS.logHeight a
  simp_rw [AS.localHeight_algebraicExtension L a]
  exact Algebraic.integral_comp_proj_measure AS L (AS.integrable_log_localHeight a)

theorem affineHeight_algebraicExtension (a : K) :
    (AS.algebraicExtension L).affineHeight (algebraMap K L a) = AS.affineHeight a := by
  have he : (fun i : Fin 2 ↦ algebraMap K L (![1, a] i)) = ![1, algebraMap K L a] := by
    funext i
    fin_cases i <;> simp
  simpa only [affineHeight, he] using AS.logHeight_algebraicExtension L ![1, a]

variable {L} {E : Type*} [Field E] [Algebra K E] [FiniteDimensional K E]

theorem localHeight_comp_finiteEmbedding (i : E →ₐ[K] L) (a : ι → E)
    (x : ParameterSpaceExtension AS L) :
    (AS.algebraicExtension L).localHeight (fun j ↦ i (a j)) x =
      (AS.finiteExtension E).localHeight a (Algebraic.projFiniteAlong AS i x) := by
  unfold localHeight
  apply Finset.sup'_congr _ rfl
  intro j _
  change x.abv (i (a j)) =
    ParameterSpaceFinExtension.ϕ AS E (Algebraic.projFiniteAlong AS i x) (a j)
  rw [Algebraic.projFiniteAlong_ϕ]
  rfl

/-- A finite base-field embedding into an algebraic extension preserves tuple heights.
This uses the prescribed marginal of the extension measure, without separability. -/
theorem logHeight_comp_finiteEmbedding (i : E →ₐ[K] L) (a : ι → E) :
    (AS.algebraicExtension L).logHeight (fun j ↦ i (a j)) =
      (AS.finiteExtension E).logHeight a := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) :=
    Algebraic.projectiveMeasurableSpace AS L
  have hm := ((AS.finiteExtension E).measurable_localHeight a).log
  have hmap := Algebraic.map_measure_projFiniteAlong AS i
  change (∫ x, Real.log ((AS.algebraicExtension L).localHeight _ x)
    ∂Algebraic.measure AS L) = _
  simp_rw [AS.localHeight_comp_finiteEmbedding i a]
  rw [← integral_map (Algebraic.measurable_projFiniteAlong AS i).aemeasurable
    hm.aestronglyMeasurable, hmap]
  rfl

theorem affineHeight_comp_finiteEmbedding (i : E →ₐ[K] L) (a : E) :
    (AS.algebraicExtension L).affineHeight (i a) = (AS.finiteExtension E).affineHeight a := by
  have he : (fun j : Fin 2 ↦ i (![1, a] j)) = ![1, i a] := by
    funext j
    fin_cases j <;> simp
  simpa only [affineHeight, he] using AS.logHeight_comp_finiteEmbedding i ![1, a]

/-- Chen–Moriwaki, Lemma 3.5.4, in the stronger form for any finite extension:
conjugate tuples have the same height in an algebraic extension containing them. -/
theorem logHeight_comp_aut (i : E →ₐ[K] L) (σ : E ≃ₐ[K] E) (a : ι → E) :
    (AS.algebraicExtension L).logHeight (fun j ↦ i (σ (a j))) =
      (AS.algebraicExtension L).logHeight (fun j ↦ i (a j)) := by
  exact (AS.logHeight_comp_finiteEmbedding (i.comp σ.toAlgHom) a).trans
    (AS.logHeight_comp_finiteEmbedding i a).symm

/-- Affine conjugate-height invariance, including finite inseparable normal extensions. -/
theorem affineHeight_comp_aut (i : E →ₐ[K] L) (σ : E ≃ₐ[K] E) (a : E) :
    (AS.algebraicExtension L).affineHeight (i (σ a)) =
      (AS.algebraicExtension L).affineHeight (i a) := by
  exact (AS.affineHeight_comp_finiteEmbedding (i.comp σ.toAlgHom) a).trans
    (AS.affineHeight_comp_finiteEmbedding i a).symm

variable [AS.toAdelicCurve.IsProper]

/-- The height over the chosen algebraic closure in Chen–Moriwaki, Definition 3.5.1. -/
noncomputable def absoluteHeight
    (x : Projectivization (AlgebraicClosure K) (ι → AlgebraicClosure K)) : ℝ :=
  letI := Algebraic.isProper_algebraicExtension AS (AlgebraicClosure K)
  (AS.algebraicExtension (AlgebraicClosure K)).projectiveHeight x

theorem absoluteHeight_mk {a : ι → AlgebraicClosure K} (ha : a ≠ 0) :
    AS.absoluteHeight (Projectivization.mk (AlgebraicClosure K) a ha) =
      (AS.algebraicExtension (AlgebraicClosure K)).logHeight a := rfl

theorem absoluteHeight_nonneg
    (x : Projectivization (AlgebraicClosure K) (ι → AlgebraicClosure K)) :
    0 ≤ AS.absoluteHeight x := by
  let := Algebraic.isProper_algebraicExtension AS (AlgebraicClosure K)
  exact (AS.algebraicExtension (AlgebraicClosure K)).projectiveHeight_nonneg x

/-- Base-field affine height agrees with the source height on the algebraic closure. -/
theorem absoluteHeight_mk_one (a : K) :
    AS.absoluteHeight (Projectivization.mk (AlgebraicClosure K)
      ![1, algebraMap K (AlgebraicClosure K) a] (by
        intro h
        have := congrFun h 0
        simp at this)) = AS.affineHeight a := by
  rw [AS.absoluteHeight_mk]
  exact AS.affineHeight_algebraicExtension (AlgebraicClosure K) a

end ArakelovGeometry.AdelicStructure
