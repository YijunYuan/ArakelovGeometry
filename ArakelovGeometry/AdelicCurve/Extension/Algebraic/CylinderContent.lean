/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Basic
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.SetAlgebra

/-!
# Cylinder functions and content

Finite-stage cylinder functions and their integral, the cylinder set algebra,
and the content used to construct the fibre probability in Proposition 3.4.6.
-/

namespace ArakelovGeometry.AdelicStructure.Algebraic

open MeasureTheory AbsoluteValue
open scoped ENNReal

universe u v w

variable {K : Type u} [Field K] (AS : AdelicStructure.{u, v} K)
variable (L : Type w) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- A real-valued cylinder function on `Ω_L`, i.e. a function descending to a finite
subextension. This is the global vector space `V_L` from Remark 3.4.7. -/
structure DescendsToFinite (f : ParameterSpaceExtension AS L → ℝ) : Type (max u v w) where
  /-- A finite subextension through which the function factors. -/
  F : FiniteIntermediateField K L
  /-- The descended function on the finite-stage space of Definition 3.4.1. -/
  g : ParameterSpaceFinExtension AS F → ℝ
  /-- The factorization through `π_{L/F}`. -/
  eq_comp : f = g ∘ projFinite AS F

/-- The vector space of real-valued cylinder functions on `Ω_L`. -/
abbrev CylinderFunctions :=
  Σ f : ParameterSpaceExtension AS L → ℝ, DescendsToFinite AS L f

variable {AS L} in
omit [Algebra.IsAlgebraic K L] in
/-- Remark 3.4.7: the cylinder functions `V_L` are closed under addition. -/
theorem DescendsToFinite.nonempty_add {f g : ParameterSpaceExtension AS L → ℝ}
    (hf : DescendsToFinite AS L f) (hg : DescendsToFinite AS L g) :
    Nonempty (DescendsToFinite AS L (f + g)) := by
  refine ⟨⟨FiniteIntermediateField.sup hf.F hg.F, fun x ↦
    hf.g (projFiniteOfLE AS (FiniteIntermediateField.left_le_sup hf.F hg.F) x) +
      hg.g (projFiniteOfLE AS (FiniteIntermediateField.right_le_sup hf.F hg.F) x), ?_⟩⟩
  ext x
  simp only [hf.eq_comp, hg.eq_comp, Pi.add_apply, Function.comp_apply,
    projFiniteOfLE_projFinite]

variable {AS L} in
omit [Algebra.IsAlgebraic K L] in
/-- Remark 3.4.7: the cylinder functions `V_L` are closed under scalar multiplication. -/
theorem DescendsToFinite.nonempty_smul (c : ℝ) {f : ParameterSpaceExtension AS L → ℝ}
    (hf : DescendsToFinite AS L f) : Nonempty (DescendsToFinite AS L (c • f)) := by
  refine ⟨⟨hf.F, fun x ↦ c * hf.g x, ?_⟩⟩
  ext x
  simp only [hf.eq_comp, Pi.smul_apply, Function.comp_apply, smul_eq_mul]

variable {AS L} in
/-- A real-valued fibre cylinder function on `M_{L,ω}`, descending to a finite fibre. This is
the definition-level counterpart of `V_{L,ω}` in §3.4.2. -/
structure DescendsToFiniteFiber (ω : AS.Ω)
    (f : BaseFiber L ω → ℝ) :
    Type (max u v w) where
  /-- A finite subextension through which the fibre function factors. -/
  F : FiniteIntermediateField K L
  /-- The descended function on the finite-stage fibre. -/
  g : FiniteBaseFiber L F ω → ℝ
  /-- The factorization through the fibre projection. -/
  eq_comp : f = g ∘ projFiniteFiber F ω

/-- The fibre cylinder functions `V_{L,ω}`. -/
abbrev FibreCylinderFunctions (ω : AS.Ω) :=
  Σ f : BaseFiber L ω → ℝ,
    DescendsToFiniteFiber ω f

variable {AS L} in
omit [Algebra.IsAlgebraic K L] in
/-- Chen--Moriwaki, Proposition 3.4.6: the fibre cylinder functions `V_{L,ω}` are closed
under addition. -/
theorem DescendsToFiniteFiber.nonempty_add {ω : AS.Ω} {f g : BaseFiber L ω → ℝ}
    (hf : DescendsToFiniteFiber ω f) (hg : DescendsToFiniteFiber ω g) :
    Nonempty (DescendsToFiniteFiber ω (f + g)) := by
  refine ⟨⟨FiniteIntermediateField.sup hf.F hg.F, fun x ↦
    hf.g (projFiniteFiberOfLE (FiniteIntermediateField.left_le_sup hf.F hg.F) ω x) +
      hg.g (projFiniteFiberOfLE (FiniteIntermediateField.right_le_sup hf.F hg.F) ω x), ?_⟩⟩
  ext x
  simp only [hf.eq_comp, hg.eq_comp, Pi.add_apply, Function.comp_apply,
    projFiniteFiberOfLE_projFiniteFiber]

variable {AS L} in
omit [Algebra.IsAlgebraic K L] in
/-- Chen--Moriwaki, Proposition 3.4.6: the fibre cylinder functions `V_{L,ω}` are closed
under multiplication; `V_{L,ω}` is an `ℝ`-algebra of functions. -/
theorem DescendsToFiniteFiber.nonempty_mul {ω : AS.Ω} {f g : BaseFiber L ω → ℝ}
    (hf : DescendsToFiniteFiber ω f) (hg : DescendsToFiniteFiber ω g) :
    Nonempty (DescendsToFiniteFiber ω (f * g)) := by
  refine ⟨⟨FiniteIntermediateField.sup hf.F hg.F, fun x ↦
    hf.g (projFiniteFiberOfLE (FiniteIntermediateField.left_le_sup hf.F hg.F) ω x) *
      hg.g (projFiniteFiberOfLE (FiniteIntermediateField.right_le_sup hf.F hg.F) ω x), ?_⟩⟩
  ext x
  simp only [hf.eq_comp, hg.eq_comp, Pi.mul_apply, Function.comp_apply,
    projFiniteFiberOfLE_projFiniteFiber]

variable {AS L} in
omit [Algebra.IsAlgebraic K L] in
/-- Chen--Moriwaki, Proposition 3.4.6: the fibre cylinder functions `V_{L,ω}` are closed
under scalar multiplication. -/
theorem DescendsToFiniteFiber.nonempty_smul (c : ℝ) {ω : AS.Ω} {f : BaseFiber L ω → ℝ}
    (hf : DescendsToFiniteFiber ω f) : Nonempty (DescendsToFiniteFiber ω (c • f)) := by
  refine ⟨⟨hf.F, fun x ↦ c * hf.g x, ?_⟩⟩
  ext x
  simp only [hf.eq_comp, Pi.smul_apply, Function.comp_apply, smul_eq_mul]

variable {AS L} in
/-- The fibre integral of a cylinder function, computed at a finite stage through which it
descends; this is the operator `I_{L/K,ω}` of formula (3.17). -/
noncomputable def fibreCylinderIntegral {ω : AS.Ω} {f : BaseFiber L ω → ℝ}
    (d : DescendsToFiniteFiber ω f) : ℝ :=
  ∫ y, d.g y ∂ParameterSpaceFinExtension.fibreProbabilityMeasure AS d.F ω

variable {AS L} in
/-- Chen--Moriwaki, Proposition 3.4.6 (well-definedness of `I_{L/K,ω}`): the fibre integral
of a cylinder function does not depend on the finite stage through which it descends. -/
theorem fibreCylinderIntegral_congr {ω : AS.Ω} {f : BaseFiber L ω → ℝ}
    (d₁ d₂ : DescendsToFiniteFiber ω f) :
    fibreCylinderIntegral d₁ = fibreCylinderIntegral d₂ := by
  let H := FiniteIntermediateField.sup d₁.F d₂.F
  let := ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K H.1) ω
  have hint (d : DescendsToFiniteFiber ω f) (h : d.F.1 ≤ H.1) :
      fibreCylinderIntegral d = ∫ y, d.g (projFiniteFiberOfLE h ω y)
        ∂ParameterSpaceFinExtension.fibreProbabilityMeasure AS H ω := by
    let := ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K d.F.1) ω
    rw [fibreCylinderIntegral,
      ← map_finiteFibreProbabilityMeasure_projFiniteFiberOfLE AS L ω h]
    exact integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable d.g).aestronglyMeasurable
  rw [hint d₁ (FiniteIntermediateField.left_le_sup d₁.F d₂.F),
    hint d₂ (FiniteIntermediateField.right_le_sup d₁.F d₂.F)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  obtain ⟨x, rfl⟩ := surjective_projFiniteFiber AS L H ω y
  simp only [H, projFiniteFiberOfLE_projFiniteFiber]
  exact (congrFun d₁.eq_comp x).symm.trans (congrFun d₂.eq_comp x)

/-- The sets represented at a finite stage of an algebraic fibre. -/
def fibreCylinders (ω : AS.Ω) : Set (Set (BaseFiber L ω)) :=
  {A | ∃ (F : FiniteIntermediateField K L) (B : Set (FiniteBaseFiber L F ω)),
    projFiniteFiber F ω ⁻¹' B = A}

omit [Algebra.IsAlgebraic K L] in
/-- Finite-stage cylinders form an algebra of sets. -/
theorem isSetAlgebra_fibreCylinders (ω : AS.Ω) :
    IsSetAlgebra (fibreCylinders AS L ω) := by
  constructor
  · exact ⟨FiniteIntermediateField.bot, ∅, rfl⟩
  · rintro A ⟨F, B, rfl⟩
    exact ⟨F, Bᶜ, rfl⟩
  · rintro A B ⟨F, C, rfl⟩ ⟨G, D, rfl⟩
    refine ⟨FiniteIntermediateField.sup F G,
      (projFiniteFiberOfLE (FiniteIntermediateField.left_le_sup F G) ω ⁻¹' C) ∪
      (projFiniteFiberOfLE (FiniteIntermediateField.right_le_sup F G) ω ⁻¹' D), ?_⟩
    ext x
    simp only [Set.mem_preimage, Set.mem_union, projFiniteFiberOfLE_projFiniteFiber]

omit [Algebra.IsAlgebraic K L] in
/-- The prescribed fibre σ-algebra is generated by the finite-stage cylinders. -/
theorem fibreMeasurableSpace_eq_generateFrom (ω : AS.Ω) :
    fibreMeasurableSpace L ω = MeasurableSpace.generateFrom (fibreCylinders AS L ω) := by
  apply le_antisymm
  · refine iSup_le fun F ↦ ?_
    rintro A ⟨B, _, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom ⟨F, B, rfl⟩
  · apply MeasurableSpace.generateFrom_le
    rintro A ⟨F, B, rfl⟩
    exact le_iSup (fun F : FiniteIntermediateField K L ↦
      MeasurableSpace.comap (projFiniteFiber F ω) inferInstance) F
        _ ⟨B, measurableSet_finiteBaseFiber AS L F ω B, rfl⟩

omit [Algebra.IsAlgebraic K L] in
/-- Finite-stage fibre projections are measurable for the cylinder σ-algebra. -/
theorem measurable_projFiniteFiber (ω : AS.Ω) (F : FiniteIntermediateField K L) :
    Measurable[fibreMeasurableSpace L ω] (projFiniteFiber F ω) :=
  Measurable.of_comap_le (le_iSup (fun F : FiniteIntermediateField K L ↦
    MeasurableSpace.comap (projFiniteFiber F ω) inferInstance) F)

/-- The cylinder content on the fibre `M_{L,ω}`: the infimum of the prescribed finite-stage
fibre measures over cylinder supersets. On a cylinder set `(π_{L/F,ω})⁻¹(B)` it takes the
prescribed value `P_{F,ω}(B)`; this is the additive set function extended by Carathéodory's
theorem in the proof of Proposition 3.4.6. -/
noncomputable def fibreCylinderContent (ω : AS.Ω) (A : Set (BaseFiber L ω)) : ℝ≥0∞ :=
  ⨅ (F : FiniteIntermediateField K L) (B : Set (FiniteBaseFiber L F ω))
    (_ : A ⊆ projFiniteFiber F ω ⁻¹' B),
    ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω B

omit [Algebra.IsAlgebraic K L] in
/-- The empty cylinder has zero content. -/
theorem fibreCylinderContent_empty (ω : AS.Ω) : fibreCylinderContent AS L ω ∅ = 0 := by
  apply le_antisymm _ zero_le
  exact iInf_le_of_le FiniteIntermediateField.bot
    (iInf_le_of_le ∅ (iInf_le_of_le (Set.empty_subset _) (by simp)))

/-- Inclusion of cylinders implies the corresponding inequality of finite-stage masses. -/
theorem finiteFibreProbabilityMeasure_le_of_preimage_subset (ω : AS.Ω)
    (F G : FiniteIntermediateField K L) (B : Set (FiniteBaseFiber L F ω))
    (C : Set (FiniteBaseFiber L G ω))
    (hBC : projFiniteFiber F ω ⁻¹' B ⊆ projFiniteFiber G ω ⁻¹' C) :
    ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω B ≤
      ParameterSpaceFinExtension.fibreProbabilityMeasure AS G ω C := by
  let H := FiniteIntermediateField.sup F G
  let qF := projFiniteFiberOfLE (FiniteIntermediateField.left_le_sup F G) ω
  let qG := projFiniteFiberOfLE (FiniteIntermediateField.right_le_sup F G) ω
  have hsub : qF ⁻¹' B ⊆ qG ⁻¹' C := by
    intro y hy
    obtain ⟨x, rfl⟩ := surjective_projFiniteFiber AS L H ω y
    exact hBC (by simpa [qF, H, projFiniteFiberOfLE_projFiniteFiber] using hy)
  let := ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K H.1) ω
  have hF := congrArg (fun μ : Measure (FiniteBaseFiber L F ω) ↦ μ B)
    (map_finiteFibreProbabilityMeasure_projFiniteFiberOfLE AS L ω
      (FiniteIntermediateField.left_le_sup F G))
  have hG := congrArg (fun μ : Measure (FiniteBaseFiber L G ω) ↦ μ C)
    (map_finiteFibreProbabilityMeasure_projFiniteFiberOfLE AS L ω
      (FiniteIntermediateField.right_le_sup F G))
  rw [Measure.map_apply (measurable_of_countable _)
    (measurableSet_finiteBaseFiber AS L F ω B)] at hF
  rw [Measure.map_apply (measurable_of_countable _)
    (measurableSet_finiteBaseFiber AS L G ω C)] at hG
  rw [← hF, ← hG]
  exact measure_mono hsub

/-- The cylinder content agrees with each prescribed finite-stage probability. -/
theorem fibreCylinderContent_preimage (ω : AS.Ω) (F : FiniteIntermediateField K L)
    (B : Set (FiniteBaseFiber L F ω)) :
    fibreCylinderContent AS L ω (projFiniteFiber F ω ⁻¹' B) =
      ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω B := by
  apply le_antisymm
  · exact iInf_le_of_le F (iInf_le_of_le B (iInf_le_of_le (Set.Subset.refl _) le_rfl))
  · exact le_iInf fun G ↦ le_iInf fun C ↦ le_iInf fun hBC ↦
      finiteFibreProbabilityMeasure_le_of_preimage_subset AS L ω F G B C hBC

/-- Cylinder content is additive on disjoint cylinders. -/
theorem fibreCylinderContent_union (ω : AS.Ω) {A B : Set (BaseFiber L ω)}
    (hA : A ∈ fibreCylinders AS L ω) (hB : B ∈ fibreCylinders AS L ω)
    (hdisj : Disjoint A B) :
    fibreCylinderContent AS L ω (A ∪ B) =
      fibreCylinderContent AS L ω A + fibreCylinderContent AS L ω B := by
  obtain ⟨F, C, rfl⟩ := hA
  obtain ⟨G, D, rfl⟩ := hB
  let H := FiniteIntermediateField.sup F G
  let C' := projFiniteFiberOfLE (FiniteIntermediateField.left_le_sup F G) ω ⁻¹' C
  let D' := projFiniteFiberOfLE (FiniteIntermediateField.right_le_sup F G) ω ⁻¹' D
  have hC : projFiniteFiber H ω ⁻¹' C' = projFiniteFiber F ω ⁻¹' C := by
    ext x
    simp only [C', H, Set.mem_preimage, projFiniteFiberOfLE_projFiniteFiber]
  have hD : projFiniteFiber H ω ⁻¹' D' = projFiniteFiber G ω ⁻¹' D := by
    ext x
    simp only [D', H, Set.mem_preimage, projFiniteFiberOfLE_projFiniteFiber]
  have hCD : Disjoint C' D' := by
    rw [Set.disjoint_left] at hdisj ⊢
    intro y hyC hyD
    obtain ⟨x, rfl⟩ := surjective_projFiniteFiber AS L H ω y
    exact hdisj ((Set.ext_iff.mp hC x).mp hyC) ((Set.ext_iff.mp hD x).mp hyD)
  rw [← hC, ← hD, ← Set.preimage_union]
  simp only [fibreCylinderContent_preimage]
  exact measure_union hCD (measurableSet_finiteBaseFiber AS L H ω D')

/-- The cylinder content, restricted to the cylinder algebra, is additive. -/
noncomputable def fibreCylinderAddContent (ω : AS.Ω) :
    AddContent ℝ≥0∞ (fibreCylinders AS L ω) :=
  (isSetAlgebra_fibreCylinders AS L ω).isSetRing.addContent_of_union
    (fibreCylinderContent AS L ω) (fibreCylinderContent_empty AS L ω)
    (fibreCylinderContent_union AS L ω)

/-- Compactness gives countable subadditivity of the cylinder content on cylinders. -/
theorem fibreCylinderAddContent_isSigmaSubadditive (ω : AS.Ω) :
    (fibreCylinderAddContent AS L ω).IsSigmaSubadditive := by
  intro f hf huf
  have hc : IsCompact (⋃ i, f i) := by
    obtain ⟨F, B, hB⟩ := huf
    rw [← hB]
    exact isCompact_fibreCylinder AS L F ω B
  have ho (i : ℕ) : IsOpen (f i) := by
    obtain ⟨F, B, hB⟩ := hf i
    rw [← hB]
    exact (isClopen_fibreCylinder AS L F ω B).isOpen
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover f ho (by rfl)
  have heq : (⋃ i, f i) = ⋃ i ∈ t, f i :=
    le_antisymm ht (Set.iUnion₂_subset fun i _ ↦ Set.subset_iUnion f i)
  calc
    (fibreCylinderAddContent AS L ω) (⋃ i, f i) =
        (fibreCylinderAddContent AS L ω) (⋃ i ∈ t, f i) := congrArg _ heq
    _ ≤ ∑ i ∈ t, (fibreCylinderAddContent AS L ω) (f i) :=
      addContent_biUnion_le (isSetAlgebra_fibreCylinders AS L ω).isSetRing (fun i _ ↦ hf i)
    _ ≤ ∑' i, (fibreCylinderAddContent AS L ω) (f i) := ENNReal.sum_le_tsum t

/-- The outer measure generated by the cylinder envelope is the extension of its content. -/
theorem fibreCylinderOuterMeasure_eq_induced (ω : AS.Ω) :
    OuterMeasure.ofFunction (fibreCylinderContent AS L ω) (fibreCylinderContent_empty AS L ω) =
      inducedOuterMeasure
        (fun A (_ : A ∈ fibreCylinders AS L ω) ↦ fibreCylinderAddContent AS L ω A)
        (isSetAlgebra_fibreCylinders AS L ω).empty_mem addContent_empty := by
  apply le_antisymm
  · apply le_inducedOuterMeasure.mpr
    intro A _
    exact OuterMeasure.ofFunction_le A
  · apply OuterMeasure.le_ofFunction.mpr
    intro A
    refine le_iInf fun F ↦ le_iInf fun B ↦ le_iInf fun hAB ↦ ?_
    calc
      _ ≤ inducedOuterMeasure
          (fun A (_ : A ∈ fibreCylinders AS L ω) ↦ fibreCylinderAddContent AS L ω A)
          (isSetAlgebra_fibreCylinders AS L ω).empty_mem addContent_empty
          (projFiniteFiber F ω ⁻¹' B) := measure_mono hAB
      _ ≤ fibreCylinderAddContent AS L ω (projFiniteFiber F ω ⁻¹' B) :=
        le_inducedOuterMeasure.mp le_rfl _ ⟨F, B, rfl⟩
      _ = _ := fibreCylinderContent_preimage AS L ω F B

/-- The outer measure has the prescribed mass on each finite-stage cylinder. -/
theorem fibreCylinderOuterMeasure_preimage (ω : AS.Ω) (F : FiniteIntermediateField K L)
    (B : Set (FiniteBaseFiber L F ω)) :
    OuterMeasure.ofFunction (fibreCylinderContent AS L ω) (fibreCylinderContent_empty AS L ω)
        (projFiniteFiber F ω ⁻¹' B) =
      ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω B := by
  rw [fibreCylinderOuterMeasure_eq_induced AS L ω,
    AddContent.inducedOuterMeasure_eq
      (isSetAlgebra_fibreCylinders AS L ω).isSetRing.isSetSemiring
      (fibreCylinderAddContent AS L ω) (fibreCylinderAddContent_isSigmaSubadditive AS L ω)
      ⟨F, B, rfl⟩]
  exact fibreCylinderContent_preimage AS L ω F B

/-- The fibre σ-algebra consists of Carathéodory-measurable sets for the cylinder content. -/
theorem fibreMeasurableSpace_le_caratheodory (ω : AS.Ω) :
    fibreMeasurableSpace L ω ≤
      (OuterMeasure.ofFunction (fibreCylinderContent AS L ω)
        (fibreCylinderContent_empty AS L ω)).caratheodory := by
  rw [fibreMeasurableSpace_eq_generateFrom AS L ω, fibreCylinderOuterMeasure_eq_induced AS L ω]
  intro A hA
  exact AddContent.isCaratheodory_inducedOuterMeasure
    (isSetAlgebra_fibreCylinders AS L ω).isSetRing.isSetSemiring
    (fibreCylinderAddContent AS L ω) A hA

end ArakelovGeometry.AdelicStructure.Algebraic
