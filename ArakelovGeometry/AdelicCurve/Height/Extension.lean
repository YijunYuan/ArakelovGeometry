/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Height.Affine
import ArakelovGeometry.AdelicCurve.Height.Polynomial
import ArakelovGeometry.AdelicCurve.Basic
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

open MeasureTheory Polynomial

variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The archimedean exponent of an extension place is the exponent of its restriction. -/
theorem κ_algebraicExtension (x : ParameterSpaceExtension AS L) :
    (AS.algebraicExtension L).κ x = AS.κ x.base := by
  have hna : IsNonarchimedean ((AS.algebraicExtension L).ϕ x) ↔
      IsNonarchimedean (AS.ϕ x.base) := by
    change IsNonarchimedean x.abv ↔ _
    rw [← x.restrict_eq]
    exact (AbsoluteValue.isNonarchimedean_restriction_iff x.abv).symm
  by_cases h : IsNonarchimedean (AS.ϕ x.base)
  · rw [(AS.κ_eq_zero_iff x.base).mpr h,
      ((AS.algebraicExtension L).κ_eq_zero_iff x).mpr (hna.mpr h)]
  · have hx : x ∈ (AS.algebraicExtension L).Ωinf := fun he ↦ h (hna.mp he)
    have hb : x.base ∈ AS.Ωinf := h
    have he := congrArg (fun w : AbsoluteValue K ℝ ↦ w 2) x.restrict_eq
    change x.abv (algebraMap K L 2) = AS.ϕ x.base 2 at he
    rw [map_ofNat] at he
    have hL := (AS.algebraicExtension L).κ_def hx 2
    have hK := AS.κ_def hb 2
    norm_num [Rat.AbsoluteValue.real_eq_abs] at hL hK
    apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
    exact hL.symm.trans (he.trans hK)

/-- The finite integrated archimedean exponent is unchanged by algebraic extension. -/
theorem integral_κ_algebraicExtension :
    (∫ x, (AS.algebraicExtension L).κ x ∂(AS.algebraicExtension L).v) =
      ∫ ω, AS.κ ω ∂AS.v := by
  change (∫ x, (AS.algebraicExtension L).κ x ∂Algebraic.measure AS L) = _
  simp_rw [AS.κ_algebraicExtension L]
  exact Algebraic.integral_comp_proj_measure AS L AS.integrable_κ

theorem heightArchimedeanConstant_algebraicExtension :
    (AS.algebraicExtension L).heightArchimedeanConstant = AS.heightArchimedeanConstant :=
  AS.integral_κ_algebraicExtension L

/-- The archimedean locus is exactly the inverse image of the base locus. -/
theorem Ωinf_algebraicExtension :
    (AS.algebraicExtension L).Ωinf = ParameterSpaceExtension.proj ⁻¹' AS.Ωinf := by
  ext x
  change ¬ IsNonarchimedean x.abv ↔ ¬ IsNonarchimedean (AS.ϕ x.base)
  rw [← x.restrict_eq, AbsoluteValue.isNonarchimedean_restriction_iff]

/-- Algebraic extension preserves archimedean mass, including infinite mass. -/
theorem v_Ωinf_algebraicExtension :
    (AS.algebraicExtension L).v (AS.algebraicExtension L).Ωinf = AS.v AS.Ωinf := by
  rw [AS.Ωinf_algebraicExtension L]
  change Algebraic.measure AS L (ParameterSpaceExtension.proj ⁻¹' AS.Ωinf) = _
  rw [← Measure.map_apply (Algebraic.measurable_proj_projective AS L)
    AS.measurableSet_Ωinf, Algebraic.map_measure_proj AS L]

/-- The local coefficient estimate expressed using the exponent of the original base. -/
theorem polynomialLocalHeight_mul_le_algebraicExtension (p q : L[X])
    (x : ParameterSpaceExtension AS L) :
    (AS.algebraicExtension L).polynomialLocalHeight (p * q) x ≤
      (min (p.natDegree + 1) (q.natDegree + 1) : ℕ) ^ AS.κ x.base *
        (AS.algebraicExtension L).polynomialLocalHeight p x *
        (AS.algebraicExtension L).polynomialLocalHeight q x := by
  simpa only [AS.κ_algebraicExtension L] using
    (AS.algebraicExtension L).polynomialLocalHeight_mul_le p q x

/-- The finite-error bound uses the integrated exponent of the original base curve. -/
theorem polynomialHeight_mul_le_algebraicExtension {p q : L[X]} (hp : p ≠ 0)
    (hq : q ≠ 0) :
    (AS.algebraicExtension L).polynomialHeight (p * q) ≤
      (AS.algebraicExtension L).polynomialHeight p +
        (AS.algebraicExtension L).polynomialHeight q +
        Real.log (min (p.natDegree + 1) (q.natDegree + 1) : ℕ) *
          AS.heightArchimedeanConstant := by
  simpa only [AS.heightArchimedeanConstant_algebraicExtension L] using
    (AS.algebraicExtension L).polynomialHeight_mul_le hp hq

/-- The real form of Lemma 3.5.5, under its finite-mass interpretation. -/
theorem polynomialHeight_mul_le_measure_Ωinf_algebraicExtension {p q : L[X]}
    (hp : p ≠ 0) (hq : q ≠ 0) (hfin : AS.v AS.Ωinf ≠ ⊤) :
    (AS.algebraicExtension L).polynomialHeight (p * q) ≤
      (AS.algebraicExtension L).polynomialHeight p +
        (AS.algebraicExtension L).polynomialHeight q +
        Real.log (min (p.natDegree + 1) (q.natDegree + 1) : ℕ) *
          (AS.v AS.Ωinf).toReal := by
  have hfin' : (AS.algebraicExtension L).v (AS.algebraicExtension L).Ωinf ≠ ⊤ := by
    simpa only [AS.v_Ωinf_algebraicExtension L] using hfin
  simpa only [AS.v_Ωinf_algebraicExtension L] using
    (AS.algebraicExtension L).polynomialHeight_mul_le_measure_Ωinf hp hq hfin'

/-- A split polynomial has height bounded by its root heights and the base error constant. -/
theorem polynomialHeight_prod_X_sub_C_le_algebraicExtension (l : List L) (hl : l ≠ []) :
    (AS.algebraicExtension L).polynomialHeight (l.map (fun a ↦ (X - C a : L[X]))).prod ≤
      (l.map (AS.algebraicExtension L).affineHeight).sum +
        (l.length - 1 : ℕ) * Real.log 2 * AS.heightArchimedeanConstant := by
  simpa only [AS.heightArchimedeanConstant_algebraicExtension L] using
    (AS.algebraicExtension L).polynomialHeight_prod_X_sub_C_le l hl

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

variable [AS.IsProper]

/-- Chen–Moriwaki, Lemma 3.5.5, with the original base measure and without a
finite-mass assumption. Specialize `L` to the algebraic closure for the printed statement. -/
theorem ofReal_polynomialHeight_mul_le_measure_Ωinf_algebraicExtension {p q : L[X]}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    ENNReal.ofReal ((AS.algebraicExtension L).polynomialHeight (p * q)) ≤
      ENNReal.ofReal ((AS.algebraicExtension L).polynomialHeight p) +
        ENNReal.ofReal ((AS.algebraicExtension L).polynomialHeight q) +
        ENNReal.ofReal (Real.log (min (p.natDegree + 1) (q.natDegree + 1) : ℕ)) *
          AS.v AS.Ωinf := by
  let := Algebraic.isProper_algebraicExtension AS L
  simpa only [AS.v_Ωinf_algebraicExtension L] using
    (AS.algebraicExtension L).ofReal_polynomialHeight_mul_le_measure_Ωinf hp hq

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
