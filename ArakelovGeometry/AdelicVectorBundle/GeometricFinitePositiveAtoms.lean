/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.FiniteProjection
public import ArakelovGeometry.AdelicCurve.Extension.Finite.Probability
public import ArakelovGeometry.AdelicVectorBundle.GeometricScalarExtensionMeasurable

/-!
# Positive atoms at genuine finite algebraic stages

Finite projective fibre probabilities have positive singleton masses, including
inseparable finite extensions. This supplies the finite-stage positive-atomic
hypothesis needed for geometric native regularity over an algebraic closure.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace ArakelovGeometry.AdelicStructure.Algebraic

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] (S : AdelicStructure K)

/-- The genuine algebraic fibre probability has positive mass at every point
when the field extension is finite, without a separability assumption. -/
theorem fibreProbabilityMeasure_singleton_pos_of_finiteDimensional
    (ω : S.Ω) (x : BaseFiber L ω) :
    0 < fibreProbabilityMeasure S L ω {x} := by
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  let f := projFiniteFiberAlong S (AlgHom.id K L) ω
  have hf : Function.Injective f := by
    intro y z h
    apply Subtype.ext
    apply ParameterSpaceExtension.ext S L
    · exact congrArg (fun t => t.val.base) h
    · have ha := congrArg (fun t => ParameterSpaceFinExtension.ϕ S L t.val) h
      simp only [f, projFiniteFiberAlong, projFiniteAlong_ϕ] at ha
      ext a
      exact congrArg (fun v : AbsoluteValue L ℝ => v a) ha
  have hs : MeasurableSet ({f x} : Set (ParameterSpaceFinExtension.BaseFiber L ω)) :=
    ParameterSpaceExtension.measurableSet_extensionFiber S (separableClosure K L) ω {f x}
  have hp : f ⁻¹' {f x} = {x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hf.eq_iff]
  have hm := map_fibreProbabilityMeasure_projFiniteFiberAlong S (AlgHom.id K L) ω
  have he := congrArg (fun μ => μ {f x}) hm
  rw [Measure.map_apply (measurable_projFiniteFiberAlong S (AlgHom.id K L) ω) hs, hp] at he
  rw [he]
  change 0 < ParameterSpaceExtension.fibreProbabilityMeasure S (separableClosure K L) ω {f x}
  rw [ParameterSpaceExtension.fibreProbabilityMeasure_singleton]
  exact ParameterSpaceExtension.fibreWeight_pos S (separableClosure K L) ω (f x)

/-- Strictly positive measurable base atoms stay strictly positive at every
actual finite algebraic extension place, including inseparable stages. -/
theorem singleton_pos_algebraicExtension_of_finiteDimensional
    [MeasurableSingletonClass S.Ω] (hpos : ∀ ω : S.Ω, 0 < S.v {ω})
    (x : ParameterSpaceExtension S L) : 0 < measure S L {x} := by
  classical
  let : MeasurableSpace (ParameterSpaceExtension S L) := projectiveMeasurableSpace S L
  let : @MeasurableSingletonClass (ParameterSpaceExtension S L)
      (projectiveMeasurableSpace S L) :=
    AdelicStructure.measurableSingletonClass_algebraicExtension_of_finiteDimensional
      (S := S) (L := L)
  have hA : @MeasurableSet (ParameterSpaceExtension S L)
      (projectiveMeasurableSpace S L) {x} := measurableSet_singleton x
  change 0 < measure S L {x}
  rw [measure_apply S L hA]
  let w := fibreProbabilityMeasure S L x.base {⟨x, rfl⟩}
  have hw : 0 < w := fibreProbabilityMeasure_singleton_pos_of_finiteDimensional
    S x.base ⟨x, rfl⟩
  have hg : fibreLIntegral S L (Set.indicator {x} fun _ => (1 : ℝ≥0∞)) =
      Set.indicator {x.base} (fun _ => w) := by
    funext ω
    by_cases h : ω = x.base
    · subst ω
      let : MeasurableSpace (BaseFiber L x.base) := fibreMeasurableSpace L x.base
      rw [Set.indicator_of_mem (Set.mem_singleton x.base)]
      change (∫⁻ y : BaseFiber L x.base,
        Set.indicator {x} (fun _ => (1 : ℝ≥0∞)) y.val
        ∂fibreProbabilityMeasure S L x.base) = w
      have hf : (fun y : BaseFiber L x.base =>
          Set.indicator {x} (fun _ => (1 : ℝ≥0∞)) y.val) =
          Set.indicator ({⟨x, rfl⟩} : Set (BaseFiber L x.base)) (fun _ => (1 : ℝ≥0∞)) := by
        funext y
        by_cases hy : y.val = x
        · rw [Set.indicator_of_mem (Set.mem_singleton_iff.mpr hy),
            Set.indicator_of_mem (Set.mem_singleton_iff.mpr (Subtype.ext hy))]
        · rw [Set.indicator_of_notMem (by simpa only [Set.mem_singleton_iff] using hy),
            Set.indicator_of_notMem (by
              intro he
              exact hy (congrArg Subtype.val (Set.mem_singleton_iff.mp he))) ]
      have hs : MeasurableSet ({⟨x, rfl⟩} : Set (BaseFiber L x.base)) := by
        convert hA.preimage (measurable_subtype_val_baseFiber S L x.base) using 1
        ext y
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff]
      rw [hf, lintegral_indicator_const hs, one_mul]
    · let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
      rw [Set.indicator_of_notMem (by simpa only [Set.mem_singleton_iff] using h)]
      change (∫⁻ y : BaseFiber L ω,
        Set.indicator {x} (fun _ => (1 : ℝ≥0∞)) y.val
        ∂fibreProbabilityMeasure S L ω) = 0
      have hf : (fun y : BaseFiber L ω =>
          Set.indicator {x} (fun _ => (1 : ℝ≥0∞)) y.val) = 0 := by
        funext y
        apply Set.indicator_of_notMem
        intro hy
        apply h
        exact y.property.symm.trans
          (congrArg (fun z : ParameterSpaceExtension S L => z.base)
            (Set.mem_singleton_iff.mp hy))
      rw [hf]
      change (∫⁻ _ : BaseFiber L ω, (0 : ℝ≥0∞)
        ∂fibreProbabilityMeasure S L ω) = 0
      exact lintegral_zero
  rw [hg, lintegral_indicator_const (measurableSet_singleton x.base)]
  have hb := hpos x.base
  positivity

end ArakelovGeometry.AdelicStructure.Algebraic
