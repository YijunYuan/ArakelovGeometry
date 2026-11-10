/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Tower
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionTower

/-!
# Actual places and measures in compatible external algebraic towers

The middle field is an external field with compatible algebra maps, rather than
an intermediate-field subtype. No measurability or measure identity is assumed.
-/

namespace ArakelovGeometry.AdelicStructure.Algebraic
open MeasureTheory
open scoped ENNReal
noncomputable section
variable {K L M : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic L M] [Algebra.IsAlgebraic K M]
  (S : AdelicStructure K)

/-- The actual inverse place restricts its final absolute value along the given
middle-field embedding. -/
def compatibleTowerPlaceInverse (y : ParameterSpaceExtension S M) :
    ParameterSpaceExtension (S.algebraicExtension L) M where
  base := {
    base := y.base
    abv := y.abv.pullback (algebraMap L M)
    restrict_eq := by
      ext a
      change y.abv (algebraMap L M (algebraMap K L a)) = S.ϕ y.base a
      rw [← IsScalarTower.algebraMap_apply K L M]
      exact congrArg (fun v : AbsoluteValue K ℝ ↦ v a) y.restrict_eq }
  abv := y.abv
  restrict_eq := rfl

/-- The existing actual tower-place map is an equivalence for arbitrary
compatible external fields, with both projective sigma algebras. -/
def compatibleTowerMeasurableEquiv :
    ((S.algebraicExtension L).algebraicExtension M).Ω ≃ᵐ (S.algebraicExtension M).Ω := by
  letI : MeasurableSpace (ParameterSpaceExtension (S.algebraicExtension L) M) :=
    projectiveMeasurableSpace (S.algebraicExtension L) M
  letI : MeasurableSpace (ParameterSpaceExtension S M) := projectiveMeasurableSpace S M
  change ParameterSpaceExtension (S.algebraicExtension L) M ≃ᵐ
    ParameterSpaceExtension S M
  exact {
    toFun := scalarExtensionTowerPlace
    invFun := compatibleTowerPlaceInverse S
    left_inv x := by
      apply ParameterSpaceExtension.ext (S.algebraicExtension L) M
      · exact ParameterSpaceExtension.ext S L rfl x.restrict_eq
      · rfl
    right_inv y := ParameterSpaceExtension.ext S M rfl rfl
    measurable_toFun := by
      apply Measurable.of_comap_le
      change MeasurableSpace.comap _ (projectiveMeasurableSpace S M) ≤
        projectiveMeasurableSpace (S.algebraicExtension L) M
      rw [projectiveMeasurableSpace_eq, projectiveMeasurableSpace_eq]
      change MeasurableSpace.comap _ (_ ⊔ ⨆ a : M, _) ≤ _
      rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
      refine sup_le ?_ (iSup_le fun a ↦ ?_)
      · rw [MeasurableSpace.comap_comp]
        exact ((measurable_proj_projective S L).comp
          (ParameterSpaceExtension.measurable_proj (S.algebraicExtension L) M)).comap_le
      · rw [MeasurableSpace.comap_comp]
        exact (ParameterSpaceExtension.measurable_eval (S.algebraicExtension L) M a).comap_le
    measurable_invFun := by
      apply Measurable.of_comap_le
      change MeasurableSpace.comap _ (projectiveMeasurableSpace (S.algebraicExtension L) M) ≤
        projectiveMeasurableSpace S M
      rw [projectiveMeasurableSpace_eq, projectiveMeasurableSpace_eq]
      change MeasurableSpace.comap _ (_ ⊔ ⨆ a : M, _) ≤ _
      rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
      refine sup_le ?_ (iSup_le fun a ↦ ?_)
      · rw [MeasurableSpace.comap_comp]
        change MeasurableSpace.comap (fun y : ParameterSpaceExtension S M ↦
          ((compatibleTowerPlaceInverse S y).base : ParameterSpaceExtension S L))
          (projectiveMeasurableSpace S L) ≤ _
        dsimp only [compatibleTowerPlaceInverse]
        rw [projectiveMeasurableSpace_eq]
        change MeasurableSpace.comap _ (_ ⊔ ⨆ a : L, _) ≤ _
        erw [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
        refine sup_le ?_ (iSup_le fun a ↦ ?_)
        · erw [MeasurableSpace.comap_comp]
          exact (ParameterSpaceExtension.measurable_proj S M).comap_le
        · erw [MeasurableSpace.comap_comp]
          exact (ParameterSpaceExtension.measurable_eval S M (algebraMap L M a)).comap_le
      · rw [MeasurableSpace.comap_comp]
        exact (ParameterSpaceExtension.measurable_eval S M a).comap_le }

/-- The forward map is exactly the accepted actual scalar-extension tower place. -/
@[simp] theorem compatibleTowerMeasurableEquiv_apply
    (x : ParameterSpaceExtension (S.algebraicExtension L) M) :
    compatibleTowerMeasurableEquiv (L := L) (M := M) S x = scalarExtensionTowerPlace x := rfl

/-- The final absolute value is unchanged. -/
@[simp] theorem compatibleTowerMeasurableEquiv_abv
    (x : ParameterSpaceExtension (S.algebraicExtension L) M) :
    (compatibleTowerMeasurableEquiv (L := L) (M := M) S x).abv = x.abv := rfl

/-- The actual map commutes with projection to the original curve. -/
@[simp] theorem compatibleTowerMeasurableEquiv_proj
    (x : ParameterSpaceExtension (S.algebraicExtension L) M) :
    (compatibleTowerMeasurableEquiv (L := L) (M := M) S x).base = x.base.base := rfl

omit [Algebra.IsAlgebraic K L] in
/-- A finite subextension lies in a finite stage above an external middle field. -/
theorem exists_finite_compatible_upper_stage
    (H : IntermediateField K M) [FiniteDimensional K H] :
    ∃ N : IntermediateField L M, Module.Finite L N ∧
      ∃ i : H →ₐ[K] N, ∀ a : H, (i a : M) = a := by
  classical
  let b := Module.finBasis K H
  let s : Set M := Set.range (fun j ↦ (b j : M))
  let N := IntermediateField.adjoin L s
  have hs : s.Finite := Set.finite_range _
  let : Finite s := hs.to_subtype
  have hN : FiniteDimensional L N :=
    IntermediateField.finiteDimensional_adjoin (fun a _ ↦ Algebra.IsIntegral.isIntegral a)
  have hn (a : H) : (a : M) ∈ N := by
    have hb (j) : (b j : M) ∈ N := IntermediateField.subset_adjoin L s ⟨j, rfl⟩
    have hh := (N.restrictScalars K).toSubmodule.sum_mem
      (fun j (_ : j ∈ Finset.univ) ↦
        (N.restrictScalars K).toSubmodule.smul_mem (b.repr a j) (hb j))
    have hsum : ∑ j, b.repr a j • (b j : M) = (a : M) := by
      exact_mod_cast b.sum_repr a
    rw [hsum] at hh
    exact hh
  let i : H →ₐ[K] N := {
    toFun a := ⟨a.val, hn a⟩
    map_zero' := rfl
    map_one' := rfl
    map_add' _ _ := rfl
    map_mul' _ _ := rfl
    commutes' a := by apply Subtype.ext; rfl }
  exact ⟨N, hN, i, fun _ ↦ rfl⟩

/-- Successive algebraic fibre integration agrees with the finite marginal on every cylinder. -/
theorem fibreLIntegral_compatibleTower_projFinite
    (H : FiniteIntermediateField K M)
    (g : ParameterSpaceFinExtension S H → ℝ≥0∞) (ω : S.Ω) :
    fibreLIntegral S L
      (fibreLIntegral (S.algebraicExtension L) M
        (fun z ↦ g (projFinite S H (compatibleTowerMeasurableEquiv (L := L) (M := M) S z)))) ω =
      ParameterSpaceFinExtension.fibreLIntegral S H g ω := by
  classical
  obtain ⟨N, hN, i, hi⟩ := exists_finite_compatible_upper_stage (L := L) H.1
  let : FiniteDimensional L N := hN
  let : FiniteDimensional K i.fieldRange := i.equivFieldRange.toLinearEquiv.finiteDimensional
  obtain ⟨A, hA, E, hE, hrange, hgen, hdim, hsep⟩ :=
    IntermediateField.exists_finite_descent (B := L) i.fieldRange
  let : FiniteDimensional K A := hA
  let : FiniteDimensional A E := hE
  let : FiniteDimensional K E := Module.Finite.trans A E
  let j : H →ₐ[K] E := {
    toFun a := ⟨i a, hrange ⟨a, rfl⟩⟩
    map_zero' := by apply Subtype.ext; exact i.map_zero
    map_one' := by apply Subtype.ext; exact i.map_one
    map_add' a b := by apply Subtype.ext; exact i.map_add a b
    map_mul' a b := by apply Subtype.ext; exact i.map_mul a b
    commutes' a := by apply Subtype.ext; exact i.commutes a }
  let q (x : ParameterSpaceFinExtension S E) :=
    projFiniteAlong S j (ParameterSpaceFinExtension.measurableEquivFull S E x)
  let h (x : ParameterSpaceFinExtension (S.finiteExtension A) E) :=
    g (q (ParameterSpaceFinExtension.towerMeasurableEquiv S E A x))
  have hinner (y : ParameterSpaceExtension S L) :
      fibreLIntegral (S.algebraicExtension L) M
          (fun z ↦ g (projFinite S H (compatibleTowerMeasurableEquiv (L := L) (M := M) S z))) y =
        ParameterSpaceFinExtension.fibreLIntegral (S.finiteExtension A) E h
          (projFiniteAlong S A.val y) := by
    let x := projFiniteAlong S A.val y
    have hxy : ((S.algebraicExtension L).ϕ y).restriction A =
        (S.finiteExtension A).ϕ x :=
      (projFiniteAlong_ϕ S A.val y).symm
    let p := ParameterSpaceFinExtension.baseChangeFiber
      (S.finiteExtension A) (S.algebraicExtension L) E x y hxy
    have hp := ParameterSpaceFinExtension.lintegral_baseChangeFiber
      (S.finiteExtension A) (S.algebraicExtension L) E x y hxy hgen hsep
      (fun z ↦ h z.val)
    have hn := lintegral_projFiniteFiberAlong (S.algebraicExtension L) N.val y
      (fun z ↦ h (p z).val)
    change _ = ∫⁻ v, h v.val ∂ParameterSpaceFinExtension.fibreProbabilityMeasure
      (S.finiteExtension A) E x
    erw [← hp, ← hn]
    apply lintegral_congr
    intro z
    apply congrArg g
    apply (ParameterSpaceFinExtension.measurableEquivFull S H).injective
    apply ParameterSpaceExtension.ext S H
    · change z.val.base.base = y.base
      exact congrArg (fun t : ParameterSpaceExtension S L ↦ t.base) z.property
    · change _ = ParameterSpaceFinExtension.ϕ S H
        (q (ParameterSpaceFinExtension.towerMeasurableEquiv S E A
          (p (projFiniteFiberAlong (S.algebraicExtension L) N.val y z)).val))
      dsimp only [q]
      rw [projFiniteAlong_ϕ]
      change _ = (ParameterSpaceFinExtension.ϕ S E
        (ParameterSpaceFinExtension.towerMeasurableEquiv S E A
          (p (projFiniteFiberAlong (S.algebraicExtension L) N.val y z)).val)).pullback j.toRingHom
      rw [ParameterSpaceFinExtension.towerMeasurableEquiv_ϕ]
      dsimp only [p]
      erw [ParameterSpaceFinExtension.baseChangeFiber_ϕ]
      change _ = ((ParameterSpaceFinExtension.ϕ (S.algebraicExtension L) N
        (projFiniteAlong (S.algebraicExtension L) N.val z.val)).restriction E).pullback j.toRingHom
      rw [projFiniteAlong_ϕ]
      have hleft : ParameterSpaceFinExtension.ϕ S H
          (projFinite S H (compatibleTowerMeasurableEquiv (L := L) (M := M) S z.val)) =
          (compatibleTowerMeasurableEquiv (L := L) (M := M) S z.val).abv.restriction H :=
        ParameterSpaceFinExtension.extendAbsoluteValue_restriction H _
      change ParameterSpaceFinExtension.ϕ S H
        (projFinite S H (compatibleTowerMeasurableEquiv (L := L) (M := M) S z.val)) = _
      rw [hleft]
      ext a
      exact congrArg z.val.abv (hi a).symm
  rw [show (fibreLIntegral (S.algebraicExtension L) M
      (fun z ↦ g (projFinite S H (compatibleTowerMeasurableEquiv (L := L) (M := M) S z)))) =
      (fun y ↦ ParameterSpaceFinExtension.fibreLIntegral (S.finiteExtension A) E h
        (projFiniteAlong S A.val y)) from funext hinner]
  erw [fibreLIntegral_comp_projFiniteAlong, ParameterSpaceFinExtension.fibreLIntegral_tower]
  have hcomp : h ∘ (ParameterSpaceFinExtension.towerMeasurableEquiv S E A).symm =
      fun z ↦ g (q z) := by
    funext z
    exact congrArg (fun t ↦ g (q t))
      ((ParameterSpaceFinExtension.towerMeasurableEquiv S E A).apply_symm_apply z)
  rw [hcomp]
  have hn := ParameterSpaceFinExtension.lintegral_homFiber S j ω (fun z ↦ g z.val)
  convert hn using 1
  · apply lintegral_congr
    intro z
    apply congrArg g
    apply (ParameterSpaceFinExtension.measurableEquivFull S H).injective
    apply ParameterSpaceExtension.ext S H
    · exact z.property
    · dsimp only [q]
      change ParameterSpaceFinExtension.ϕ S H
        (projFiniteAlong S j (ParameterSpaceFinExtension.measurableEquivFull S E z.val)) = _
      rw [projFiniteAlong_ϕ]
      exact (ParameterSpaceFinExtension.homFiber_ϕ S j ω z).symm
  · rfl

/-- The measure obtained by integrating the upper fibre probabilities over a lower fibre. -/
noncomputable def compatibleTowerFibreMeasure (ω : S.Ω) :
    Measure (S.algebraicExtension M).Ω :=
  (fibreMeasure S L ω).bind (fun x ↦
    Measure.map (compatibleTowerMeasurableEquiv (L := L) (M := M) S)
      (fibreMeasure (S.algebraicExtension L) M x))

/-- The upper fibre probabilities, after identifying parameter spaces, depend measurably
on the intermediate parameter. -/
theorem measurable_compatibleTowerFibreKernel :
    Measurable (fun x ↦ Measure.map (compatibleTowerMeasurableEquiv (L := L) (M := M) S)
      (fibreMeasure (S.algebraicExtension L) M x)) :=
  (Measure.measurable_map _ (compatibleTowerMeasurableEquiv (L := L) (M := M) S).measurable).comp
    (measurable_fibreMeasure (S.algebraicExtension L) M)

/-- Iterating probability measures along the measurable fibre family gives a probability. -/
instance isProbabilityMeasure_compatibleTowerFibreMeasure (ω : S.Ω) :
    IsProbabilityMeasure (compatibleTowerFibreMeasure (L := L) (M := M) S ω) := by
  have hp (x : (S.algebraicExtension L).Ω) :
      IsProbabilityMeasure (Measure.map (compatibleTowerMeasurableEquiv (L := L) (M := M) S)
        (fibreMeasure (S.algebraicExtension L) M x)) :=
    Measure.isProbabilityMeasure_map
      (compatibleTowerMeasurableEquiv (L := L) (M := M) S).measurable.aemeasurable
  constructor
  rw [compatibleTowerFibreMeasure, Measure.bind_apply MeasurableSet.univ
    (measurable_compatibleTowerFibreKernel (L := L) (M := M) S).aemeasurable]
  simp

/-- Integration against the iterated probability is iterated nonnegative fibre integration. -/
theorem lintegral_compatibleTowerFibreMeasure {f : (S.algebraicExtension M).Ω → ℝ≥0∞}
    (hf : Measurable f) (ω : S.Ω) :
    ∫⁻ x, f x ∂compatibleTowerFibreMeasure (L := L) (M := M) S ω =
      fibreLIntegral S L
        (fibreLIntegral (S.algebraicExtension L) M
          (fun z ↦ f (compatibleTowerMeasurableEquiv (L := L) (M := M) S z))) ω := by
  rw [compatibleTowerFibreMeasure, Measure.lintegral_bind
    (measurable_compatibleTowerFibreKernel (L := L) (M := M) S).aemeasurable hf.aemeasurable]
  let g : ((S.algebraicExtension L).algebraicExtension M).Ω → ℝ≥0∞ :=
    fun z ↦ f (compatibleTowerMeasurableEquiv (L := L) (M := M) S z)
  have hg : Measurable g := hf.comp (compatibleTowerMeasurableEquiv (L := L) (M := M) S).measurable
  calc
    _ = ∫⁻ x, fibreLIntegral (S.algebraicExtension L) M g x ∂fibreMeasure S L ω := by
      apply lintegral_congr
      intro x
      have hi := lintegral_map (μ := fibreMeasure (S.algebraicExtension L) M x)
        hf (compatibleTowerMeasurableEquiv (L := L) (M := M) S).measurable
      exact hi.trans (lintegral_fibreMeasure (S.algebraicExtension L) M hg x)
    _ = _ := lintegral_fibreMeasure S L
      (measurable_fibreLIntegral (S.algebraicExtension L) M hg) ω


/-- Direct and iterated fibre probabilities agree, by their finite-stage marginals. -/
theorem compatibleTowerFibreMeasure_eq (ω : S.Ω) :
    compatibleTowerFibreMeasure (L := L) (M := M) S ω = fibreMeasure S M ω := by
  let : MeasurableSpace (ParameterSpaceExtension S M) := projectiveMeasurableSpace S M
  let μ : Measure (ParameterSpaceExtension S M) := compatibleTowerFibreMeasure (L := L) (M := M) S ω
  let ν : Measure (ParameterSpaceExtension S M) := fibreMeasure S M ω
  have : IsProbabilityMeasure μ :=
    isProbabilityMeasure_compatibleTowerFibreMeasure (L := L) (M := M) S ω
  change μ = ν
  apply totalMeasure_ext S M
  intro H
  apply Measure.ext_of_lintegral
  intro g hg
  have hp := measurable_projFinite_projective S M H
  have h1 := lintegral_map (μ := μ) hg hp
  have h2 := lintegral_map (μ := ν) hg hp
  have h3 := lintegral_compatibleTowerFibreMeasure (L := L) (M := M) S (hg.comp hp) ω
  have h4 := lintegral_fibreMeasure S M (hg.comp hp) ω
  have hcyl := fibreLIntegral_compatibleTower_projFinite (L := L) (M := M) S H g ω
  exact h1.trans (h3.trans (hcyl.trans
    ((congrFun (fibreLIntegral_comp_projFinite S M H g) ω).symm.trans
      (h4.symm.trans h2.symm))))

/-- The canonical tower identification transports the iterated extension measure. -/
theorem map_measure_compatibleTowerMeasurableEquiv :
    Measure.map (compatibleTowerMeasurableEquiv (L := L) (M := M) S)
      ((S.algebraicExtension L).algebraicExtension M).v =
      (S.algebraicExtension M).v := by
  apply Measure.ext_of_lintegral
  intro f hf
  let g : ((S.algebraicExtension L).algebraicExtension M).Ω → ℝ≥0∞ :=
    fun z ↦ f (compatibleTowerMeasurableEquiv (L := L) (M := M) S z)
  have hg : Measurable g := hf.comp (compatibleTowerMeasurableEquiv (L := L) (M := M) S).measurable
  have h1 := lintegral_map (μ := ((S.algebraicExtension L).algebraicExtension M).v)
    hf (compatibleTowerMeasurableEquiv (L := L) (M := M) S).measurable
  have h2 := lintegral_measure (S.algebraicExtension L) M hg
  have h3 := lintegral_measure S L
    (measurable_fibreLIntegral (S.algebraicExtension L) M hg)
  have h4 : (∫⁻ ω, fibreLIntegral S L
      (fibreLIntegral (S.algebraicExtension L) M g) ω ∂S.v) =
      ∫⁻ ω, fibreLIntegral S M f ω ∂S.v := by
    apply lintegral_congr
    intro ω
    have ht := lintegral_compatibleTowerFibreMeasure (L := L) (M := M) S hf ω
    have heq := congrArg (fun μ : Measure (S.algebraicExtension M).Ω ↦ ∫⁻ x, f x ∂μ)
      (compatibleTowerFibreMeasure_eq (L := L) (M := M) S ω)
    exact ht.symm.trans (heq.trans (lintegral_fibreMeasure S M hf ω))
  exact h1.trans (h2.trans (h3.trans (h4.trans (lintegral_measure S M hf).symm)))

/-- The genuine tower identification preserves the actual total measures. -/
theorem measurePreserving_compatibleTowerMeasurableEquiv :
    MeasurePreserving (compatibleTowerMeasurableEquiv (L := L) (M := M) S)
      ((S.algebraicExtension L).algebraicExtension M).v (S.algebraicExtension M).v :=
  ⟨(compatibleTowerMeasurableEquiv (L := L) (M := M) S).measurable,
    map_measure_compatibleTowerMeasurableEquiv (L := L) (M := M) S⟩

/-- Real integrals commute with the actual compatible tower map. -/
theorem integral_comp_compatibleTowerMeasurableEquiv
    (f : (S.algebraicExtension M).Ω → ℝ) :
    (∫ x, f (compatibleTowerMeasurableEquiv (L := L) (M := M) S x)
      ∂((S.algebraicExtension L).algebraicExtension M).v) =
      ∫ y, f y ∂(S.algebraicExtension M).v :=
  (measurePreserving_compatibleTowerMeasurableEquiv (L := L) (M := M) S).integral_comp
    (compatibleTowerMeasurableEquiv (L := L) (M := M) S).measurableEmbedding f


end

end ArakelovGeometry.AdelicStructure.Algebraic
