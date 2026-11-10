/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Equiv
public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Integrable
public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.TowerCylinder
public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.TowerIntegral
/-!
# Compatibility of algebraic extensions

Finite descent and cylinder marginal identities imply equality of the direct
and iterated fibre probabilities. This proves Chen–Moriwaki, Theorem 3.4.12,
with pointwise nonnegative integration and almost everywhere signed integration.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure.Algebraic
open MeasureTheory
open scoped ENNReal
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (AS : AdelicStructure K) [Algebra.IsAlgebraic K L]
variable (F : IntermediateField K L)
/-- Direct and iterated fibre probabilities agree, by their finite-stage marginals. -/
theorem towerFibreMeasure_eq (ω : AS.Ω) :
    towerFibreMeasure AS F ω = fibreMeasure AS L ω := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  let μ : Measure (ParameterSpaceExtension AS L) := towerFibreMeasure AS F ω
  let ν : Measure (ParameterSpaceExtension AS L) := fibreMeasure AS L ω
  have : IsProbabilityMeasure μ := isProbabilityMeasure_towerFibreMeasure AS F ω
  change μ = ν
  apply totalMeasure_ext AS L
  intro H
  apply Measure.ext_of_lintegral
  intro g hg
  have hp := measurable_projFinite_projective AS L H
  have h1 := lintegral_map (μ := μ) hg hp
  have h2 := lintegral_map (μ := ν) hg hp
  have h3 := lintegral_towerFibreMeasure AS F (hg.comp hp) ω
  have h4 := lintegral_fibreMeasure AS L (hg.comp hp) ω
  exact h1.trans (h3.trans ((fibreLIntegral_tower_projFinite AS F H g ω).trans
    ((congrFun (fibreLIntegral_comp_projFinite AS L H g) ω).symm.trans
      (h4.symm.trans h2.symm))))

/-- Nonnegative measurable fibre integration is transitive in every algebraic tower. -/
theorem fibreLIntegral_tower
    {g : ((AS.algebraicExtension F).algebraicExtension L).Ω → ℝ≥0∞}
    (hg : Measurable g) :
    fibreLIntegral AS F (fibreLIntegral (AS.algebraicExtension F) L g) =
      fibreLIntegral AS L (fun y ↦ g ((towerMeasurableEquiv AS F).symm y)) := by
  funext ω
  let f : (AS.algebraicExtension L).Ω → ℝ≥0∞ :=
    fun y ↦ g ((towerMeasurableEquiv AS F).symm y)
  have hf : Measurable f := hg.comp (towerMeasurableEquiv AS F).symm.measurable
  have hi := lintegral_towerFibreMeasure AS F hf ω
  rw [towerFibreMeasure_eq AS F ω, lintegral_fibreMeasure AS L hf] at hi
  have hcomp : (fun z : ((AS.algebraicExtension F).algebraicExtension L).Ω ↦
      f (towerMeasurableEquiv AS F z)) = g := by
    funext z
    exact congrArg g ((towerMeasurableEquiv AS F).symm_apply_apply z)
  have hh := congrArg
    (fun h : ((AS.algebraicExtension F).algebraicExtension L).Ω → ℝ≥0∞ ↦
      fibreLIntegral AS F (fibreLIntegral (AS.algebraicExtension F) L h) ω) hcomp
  exact hh.symm.trans hi.symm

/-- The canonical tower identification transports the iterated extension measure. -/
theorem map_measure_towerMeasurableEquiv :
    Measure.map (towerMeasurableEquiv AS F) ((AS.algebraicExtension F).algebraicExtension L).v =
      (AS.algebraicExtension L).v := by
  apply Measure.ext_of_lintegral
  intro f hf
  let g : ((AS.algebraicExtension F).algebraicExtension L).Ω → ℝ≥0∞ :=
    fun z ↦ f (towerMeasurableEquiv AS F z)
  have hg : Measurable g := hf.comp (towerMeasurableEquiv AS F).measurable
  have h1 := lintegral_map (μ := ((AS.algebraicExtension F).algebraicExtension L).v)
    hf (towerMeasurableEquiv AS F).measurable
  have h2 := lintegral_measure (AS.algebraicExtension F) L hg
  have h3 := lintegral_measure AS F
    (measurable_fibreLIntegral (AS.algebraicExtension F) L hg)
  have h4 : (∫⁻ ω, fibreLIntegral AS F
      (fibreLIntegral (AS.algebraicExtension F) L g) ω ∂AS.v) =
      ∫⁻ ω, fibreLIntegral AS L f ω ∂AS.v := by
    apply lintegral_congr
    intro ω
    have ht := lintegral_towerFibreMeasure AS F hf ω
    have heq := congrArg (fun μ : Measure (AS.algebraicExtension L).Ω ↦ ∫⁻ x, f x ∂μ)
      (towerFibreMeasure_eq AS F ω)
    exact ht.symm.trans (heq.trans (lintegral_fibreMeasure AS L hf ω))
  exact h1.trans (h2.trans (h3.trans (h4.trans (lintegral_measure AS L hf).symm)))

/-- The canonical equivalence between iterated and direct algebraic adelic extensions. -/
noncomputable def towerEquiv :
    (AS ⊗[K] F) ⊗[F] L ≃ AS ⊗[K] L where
  toMeasurableEquiv := towerMeasurableEquiv AS F
  ϕ_comp _ := rfl
  map_v := map_measure_towerMeasurableEquiv AS F

/-- Signed tower integration holds almost everywhere for measurable integrable functions. -/
theorem fibreIntegral_tower_of_measurable
    {g : ((AS.algebraicExtension F).algebraicExtension L).Ω → ℝ}
    (hg : Measurable g)
    (hi : Integrable g ((AS.algebraicExtension F).algebraicExtension L).v) :
    fibreIntegral AS F (fibreIntegral (AS.algebraicExtension F) L g) =ᵐ[AS.v]
      fibreIntegral AS L (fun y ↦ g ((towerMeasurableEquiv AS F).symm y)) := by
  let e := towerMeasurableEquiv AS F
  let f : (AS.algebraicExtension L).Ω → ℝ := fun y ↦ g (e.symm y)
  have hf : Measurable f := hg.comp e.symm.measurable
  have he : MeasurePreserving e ((AS.algebraicExtension F).algebraicExtension L).v
      (AS.algebraicExtension L).v := ⟨e.measurable, map_measure_towerMeasurableEquiv AS F⟩
  have heinv := MeasurePreserving.symm e he
  have hfi : Integrable f (AS.algebraicExtension L).v :=
    (heinv.integrable_comp hg.aestronglyMeasurable).mpr hi
  filter_upwards [integrable_fibreMeasure_ae AS L hf hfi] with ω hω
  have hQ : Integrable f (towerFibreMeasure AS F ω) := by
    rw [towerFibreMeasure_eq AS F ω]
    exact hω
  have hs := integral_towerFibreMeasure AS F hf ω hQ
  have hd := integral_fibreMeasure AS L hf ω
  have hm := congrArg (fun μ : Measure (AS.algebraicExtension L).Ω ↦ ∫ x, f x ∂μ)
    (towerFibreMeasure_eq AS F ω)
  have hcomp : (fun z : ((AS.algebraicExtension F).algebraicExtension L).Ω ↦
      f (towerMeasurableEquiv AS F z)) = g := by
    funext z
    exact congrArg g (e.symm_apply_apply z)
  have hh := congrArg
    (fun h : ((AS.algebraicExtension F).algebraicExtension L).Ω → ℝ ↦
      fibreIntegral AS F (fibreIntegral (AS.algebraicExtension F) L h) ω) hcomp
  exact hh.symm.trans (hs.symm.trans (hm.trans hd))

/-- Signed tower integration holds almost everywhere for every integrable representative. -/
theorem fibreIntegral_tower
    {g : ((AS.algebraicExtension F).algebraicExtension L).Ω → ℝ}
    (hi : Integrable g ((AS.algebraicExtension F).algebraicExtension L).v) :
    fibreIntegral AS F (fibreIntegral (AS.algebraicExtension F) L g) =ᵐ[AS.v]
      fibreIntegral AS L (fun y ↦ g ((towerMeasurableEquiv AS F).symm y)) := by
  obtain ⟨g', hg', hgg'⟩ := exists_measurable_representative (AS.algebraicExtension F) L hi
  have hi' := hi.congr hgg'
  have hclean := fibreIntegral_tower_of_measurable AS F hg' hi'
  have hleft := fibreIntegral_congr_ae AS F
    (fibreIntegral_congr_ae (AS.algebraicExtension F) L hgg')
  have he : MeasurePreserving (towerMeasurableEquiv AS F)
      ((AS.algebraicExtension F).algebraicExtension L).v (AS.algebraicExtension L).v :=
    ⟨(towerMeasurableEquiv AS F).measurable, map_measure_towerMeasurableEquiv AS F⟩
  have heinv := MeasurePreserving.symm (towerMeasurableEquiv AS F) he
  have hright := fibreIntegral_congr_ae AS L (heinv.quasiMeasurePreserving.ae_eq_comp hgg')
  exact hleft.trans (hclean.trans hright.symm)



end ArakelovGeometry.AdelicStructure.Algebraic

namespace ArakelovGeometry
open AdelicStructure MeasureTheory
open scoped ENNReal AdelicStructure
universe u v w
variable {K : Type u} [Field K] (AS : AdelicStructure.{u, v} K)
variable (M : Type w) [Field M] [Algebra K M]
/-- Chen--Moriwaki, Theorem 3.4.12: algebraic extension of adelic structures is transitive:
for a tower `K ⊆ L₁ ⊆ L₂` of algebraic extensions, `(S ⊗_K L₁) ⊗_{L₁} L₂` and `S ⊗_K L₂` are
canonically equivalent, compatibly with the projections to the base (formulae (3.22),
(3.23)). The fibre identity is pointwise for measurable nonnegative functions, as in
the proof on PDF pages 213–214. For globally integrable real functions it holds almost
everywhere, by Proposition 3.4.9. The signed integral in the source is defined only on
its integrability domain (PDF pages 210–211); totalizing it does not give an identity
for arbitrary real functions. -/
theorem exists_equiv_algebraicExtension_algebraicExtension [Algebra.IsAlgebraic K M]
    (F : IntermediateField K M) :
    ∃ e : (AS ⊗[K] F) ⊗[F] M ≃ AS ⊗[K] M,
      (∀ x, ParameterSpaceExtension.proj (ParameterSpaceExtension.proj x) =
        ParameterSpaceExtension.proj (e.toMeasurableEquiv x)) ∧
      (∀ g : ((AS.algebraicExtension F).algebraicExtension M).Ω → ℝ≥0∞,
        Measurable[((AS.algebraicExtension F).algebraicExtension M).A] g →
        Algebraic.fibreLIntegral AS F
            (Algebraic.fibreLIntegral (AS.algebraicExtension F) M g) =
          Algebraic.fibreLIntegral AS M
            (fun y ↦ g (e.toMeasurableEquiv.symm y))) ∧
      ∀ g : ((AS.algebraicExtension F).algebraicExtension M).Ω → ℝ,
        Integrable[((AS.algebraicExtension F).algebraicExtension M).A] g
          ((AS.algebraicExtension F).algebraicExtension M).v →
        Algebraic.fibreIntegral AS F
            (Algebraic.fibreIntegral (AS.algebraicExtension F) M g) =ᵐ[AS.v]
          Algebraic.fibreIntegral AS M
            (fun y ↦ g (e.toMeasurableEquiv.symm y)) := by
  refine ⟨Algebraic.towerEquiv AS F, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro g hg
    exact Algebraic.fibreLIntegral_tower AS F hg
  · intro g hg
    exact Algebraic.fibreIntegral_tower AS F hg

end ArakelovGeometry
