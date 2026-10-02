/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Extension.Finite.Construction
import ArakelovGeometry.AdelicCurve.Equiv

/-!
# Compatibility of finite extensions

Canonical measurable identifications and multiplicativity of local separable degrees
give transitivity of finite extension of adelic structures, including inseparable towers.
This is Chen–Moriwaki, Proposition 3.4.4.
-/

open MeasureTheory

namespace ArakelovGeometry.AdelicStructure.ParameterSpaceExtension
variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L]
variable (F : Type*) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]

/-- Restriction of a parameter along an arbitrary tower of field embeddings. -/
def restrictScalars (x : ParameterSpaceExtension AS L) : ParameterSpaceExtension AS F where
  base := x.base
  abv := x.abv.restriction F
  restrict_eq := by
    ext a
    change x.abv (algebraMap F L (algebraMap K F a)) = AS.ϕ x.base a
    rw [← IsScalarTower.algebraMap_apply K F L]
    exact congrArg (fun v : AbsoluteValue K ℝ ↦ v a) x.restrict_eq

/-- Restriction along a field tower is measurable for the evaluation sigma algebras. -/
theorem measurable_restrictScalars : Measurable (restrictScalars AS L F) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap _ (_ ⊔ ⨆ a : F, _) ≤ _
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
  refine sup_le ?_ (iSup_le fun a ↦ ?_)
  · rw [MeasurableSpace.comap_comp]
    exact (measurable_proj AS L).comap_le
  · rw [MeasurableSpace.comap_comp]
    exact (measurable_eval AS L (algebraMap F L a)).comap_le

end ArakelovGeometry.AdelicStructure.ParameterSpaceExtension

namespace ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension
open MeasureTheory
open scoped ENNReal
variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Nonnegative fibre integration for a finite extension uses its separable part. -/
noncomputable def fibreLIntegral (f : ParameterSpaceFinExtension AS L → ℝ≥0∞) : AS.Ω → ℝ≥0∞ :=
  ParameterSpaceExtension.fibreLIntegral AS (separableClosure K L) f

/-- Integration on a finite fibre is the weighted sum of its values. -/
theorem fibreIntegral_eq_sum (f : ParameterSpaceFinExtension AS L → ℝ) (ω : AS.Ω)
    [Fintype (BaseFiber (AS := AS) L ω)] :
    fibreIntegral AS L f ω =
      ∑ x, (ParameterSpaceExtension.fibreWeight AS (separableClosure K L) ω x).toReal * f x.val :=
  ParameterSpaceExtension.fibreIntegral_eq_sum AS (separableClosure K L) f ω

/-- Nonnegative integration on a finite fibre is its weighted sum. -/
theorem fibreLIntegral_eq_sum (f : ParameterSpaceFinExtension AS L → ℝ≥0∞) (ω : AS.Ω)
    [Fintype (BaseFiber (AS := AS) L ω)] :
    fibreLIntegral AS L f ω =
      ∑ x, ParameterSpaceExtension.fibreWeight AS (separableClosure K L) ω x * f x.val :=
  ParameterSpaceExtension.fibreLIntegral_eq_sum AS (separableClosure K L) f ω

/-- Real fibre integration for a finite extension preserves measurability. -/
theorem measurable_fibreIntegral {f : ParameterSpaceFinExtension AS L → ℝ}
    (hf : Measurable f) : Measurable (fibreIntegral AS L f) :=
  ParameterSpaceExtension.measurable_fibreIntegral AS (separableClosure K L) hf

/-- Nonnegative fibre integration for a finite extension preserves measurability. -/
theorem measurable_fibreLIntegral {f : ParameterSpaceFinExtension AS L → ℝ≥0∞}
    (hf : Measurable f) : Measurable (fibreLIntegral AS L f) :=
  ParameterSpaceExtension.measurable_fibreLIntegral AS (separableClosure K L) hf

/-- Nonnegative disintegration for a finite, possibly inseparable extension. -/
theorem lintegral_measure {f : ParameterSpaceFinExtension AS L → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x, f x ∂(AS.finiteExtension L).v = ∫⁻ ω, fibreLIntegral AS L f ω ∂AS.v :=
  ParameterSpaceExtension.lintegral_inducedMeasure AS (separableClosure K L) hf

end ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension


namespace ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension
variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The finite parameter space is measurably equivalent to the full space of
extending absolute values. -/
noncomputable def measurableEquivFull :
    ParameterSpaceFinExtension AS L ≃ᵐ ParameterSpaceExtension AS L where
  toFun x := {
    base := x.base
    abv := ϕ AS L x
    restrict_eq := by
      ext a
      change extendAbsoluteValue x.abv (algebraMap K L a) = AS.ϕ x.base a
      rw [IsScalarTower.algebraMap_apply K (separableClosure K L) L]
      exact (extendAbsoluteValue_coe x.abv (algebraMap K (separableClosure K L) a)).trans
        (congrArg (fun v : AbsoluteValue K ℝ ↦ v a) x.restrict_eq) }
  invFun y := ParameterSpaceExtension.restrict AS L y (separableClosure K L)
  left_inv x := by
    refine ParameterSpaceExtension.ext AS (separableClosure K L) ?_ ?_
    · rfl
    · exact restriction_extendAbsoluteValue x.abv
  right_inv y := by
    refine ParameterSpaceExtension.ext AS L ?_ ?_
    · rfl
    · exact extendAbsoluteValue_restriction L y.abv
  measurable_toFun := by
    apply Measurable.of_comap_le
    change MeasurableSpace.comap _ (_ ⊔ ⨆ a : L, _) ≤ _
    rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
    refine sup_le ?_ (iSup_le fun a ↦ ?_)
    · rw [MeasurableSpace.comap_comp]
      exact (ParameterSpaceExtension.measurable_proj AS (separableClosure K L)).comap_le
    · rw [MeasurableSpace.comap_comp]
      apply Measurable.comap_le
      change Measurable fun x : ParameterSpaceFinExtension AS L ↦ ϕ AS L x a
      simp_rw [ϕ, extendAbsoluteValue_apply]
      exact (ParameterSpaceExtension.measurable_eval AS (separableClosure K L) _).pow_const _
  measurable_invFun := ParameterSpaceExtension.measurable_restrict AS L (separableClosure K L)

end ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension


namespace ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension
open MeasureTheory
variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
/-- Composing extension places gives a measurable equivalence before the final
restriction to the separable part. -/
noncomputable def fullTowerEquiv (F : Type*) [Field F] [Algebra K F]
    [Algebra F L] [IsScalarTower K F L] [FiniteDimensional K F] [FiniteDimensional F L] :
    ParameterSpaceExtension (AS.finiteExtension F) L ≃ᵐ ParameterSpaceExtension AS L where
  toFun x := {
    base := x.base.base
    abv := x.abv
    restrict_eq := by
      ext a
      change x.abv (algebraMap K L a) = AS.ϕ x.base.base a
      rw [IsScalarTower.algebraMap_apply K F L]
      exact (congrArg (fun v : AbsoluteValue F ℝ ↦ v (algebraMap K F a))
        x.restrict_eq).trans
        (congrArg (fun v : AbsoluteValue K ℝ ↦ v a)
          (measurableEquivFull AS F x.base).restrict_eq) }
  invFun y := {
    base := (measurableEquivFull AS F).symm (ParameterSpaceExtension.restrictScalars AS L F y)
    abv := y.abv
    restrict_eq := by
      have h := congrArg ParameterSpaceExtension.abv
        ((measurableEquivFull AS F).apply_symm_apply
          (ParameterSpaceExtension.restrictScalars AS L F y))
      exact h.symm }
  left_inv x := by
    refine ParameterSpaceExtension.ext (AS.finiteExtension F) L ?_ rfl
    apply (measurableEquivFull AS F).symm_apply_eq.mpr
    refine ParameterSpaceExtension.ext AS F ?_ ?_
    · rfl
    · exact x.restrict_eq
  right_inv y := by
    refine ParameterSpaceExtension.ext AS L ?_ rfl
    rfl
  measurable_toFun := by
    apply Measurable.of_comap_le
    change MeasurableSpace.comap _ (_ ⊔ ⨆ a : L, _) ≤ _
    rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
    refine sup_le ?_ (iSup_le fun a ↦ ?_)
    · rw [MeasurableSpace.comap_comp]
      exact ((ParameterSpaceExtension.measurable_proj AS (separableClosure K F)).comp
        (ParameterSpaceExtension.measurable_proj (AS.finiteExtension F) L)).comap_le
    · rw [MeasurableSpace.comap_comp]
      exact (ParameterSpaceExtension.measurable_eval (AS.finiteExtension F) L a).comap_le
  measurable_invFun := by
    apply Measurable.of_comap_le
    change MeasurableSpace.comap _ (_ ⊔ ⨆ a : L, _) ≤ _
    rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
    refine sup_le ?_ (iSup_le fun a ↦ ?_)
    · rw [MeasurableSpace.comap_comp]
      exact ((measurableEquivFull AS F).symm.measurable.comp
        (ParameterSpaceExtension.measurable_restrictScalars AS L F)).comap_le
    · rw [MeasurableSpace.comap_comp]
      exact (ParameterSpaceExtension.measurable_eval AS L a).comap_le

/-- The canonical measurable equivalence between successive and direct finite parameters. -/
noncomputable def towerMeasurableEquiv (F : Type*) [Field F] [Algebra K F]
    [Algebra F L] [IsScalarTower K F L] [FiniteDimensional K F] [FiniteDimensional F L] :
    ParameterSpaceFinExtension (AS.finiteExtension F) L ≃ᵐ ParameterSpaceFinExtension AS L :=
  ((measurableEquivFull (AS.finiteExtension F) L).trans (fullTowerEquiv AS L F)).trans
    (measurableEquivFull AS L).symm

end ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension


namespace AbsoluteValue

/-- Separable local degrees multiply in a finite tower. -/
theorem localFinSepDegree_mul {K L : Type*} [Field K] [Field L]
    [instKL : Algebra K L] [FiniteDimensional K L] (w : AbsoluteValue L ℝ)
    (F : Type*) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [FiniteDimensional F L] :
    Field.finSepDegree ((w.restriction F).restriction K).Completion
        (w.restriction F).Completion *
      Field.finSepDegree (w.restriction F).Completion w.Completion =
        Field.finSepDegree (w.restriction K).Completion w.Completion := by
  have heq : instKL = Algebra.compHom L (algebraMap K F) :=
    Algebra.algebra_ext _ _ (fun a ↦ IsScalarTower.algebraMap_apply K F L a)
  subst instKL
  let : Algebra K L := Algebra.compHom L (algebraMap K F)
  let B := (w.restriction K).Completion
  let D := (w.restriction F).Completion
  let : Algebra B D := algebraCompletion (w.restriction F) K
  have : IsScalarTower B D w.Completion := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    refine UniformSpace.Completion.induction_on x ?_ ?_
    · exact isClosed_eq (isometry_algebraMap_completion w K).continuous
        ((isometry_algebraMap_completion w F).continuous.comp
          (isometry_algebraMap_completion (w.restriction F) K).continuous)
    · intro a
      change (algebraMap (w.restriction K).Completion w.Completion)
            (a : (w.restriction K).Completion) =
          (algebraMap (w.restriction F).Completion w.Completion)
            ((algebraMap ((w.restriction F).restriction K).Completion
              (w.restriction F).Completion)
              ((show WithAbs ((w.restriction F).restriction K) from a) :
                ((w.restriction F).restriction K).Completion))
      rw [algebraMap_completion_def, algebraMap_completion_def, algebraMap_completion_def]
      erw [UniformSpace.Completion.mapRingHom_coe, UniformSpace.Completion.mapRingHom_coe,
        UniformSpace.Completion.mapRingHom_coe]
      rfl
  have : FiniteDimensional D w.Completion := finiteDimensional_completion w F
  exact Field.finSepDegree_mul_finSepDegree_of_isAlgebraic B D w.Completion
end AbsoluteValue

namespace ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension
open MeasureTheory
open scoped ENNReal
variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

@[simp]
theorem towerMeasurableEquiv_proj (F : Type*) [Field F] [Algebra K F]
    [Algebra F L] [IsScalarTower K F L] [FiniteDimensional K F] [FiniteDimensional F L]
    (x : ParameterSpaceFinExtension (AS.finiteExtension F) L) :
    ParameterSpaceExtension.proj (towerMeasurableEquiv AS L F x) =
      ParameterSpaceExtension.proj (ParameterSpaceExtension.proj x) := rfl

@[simp]
theorem towerMeasurableEquiv_ϕ (F : Type*) [Field F] [Algebra K F]
    [Algebra F L] [IsScalarTower K F L] [FiniteDimensional K F] [FiniteDimensional F L]
    (x : ParameterSpaceFinExtension (AS.finiteExtension F) L) :
    ϕ AS L (towerMeasurableEquiv AS L F x) = ϕ (AS.finiteExtension F) L x :=
  extendAbsoluteValue_restriction L (ϕ (AS.finiteExtension F) L x)

/-- A direct finite fibre is the disjoint union of the successive finite fibres. -/
noncomputable def towerFiberEquiv (F : Type*) [Field F] [Algebra K F]
    [Algebra F L] [IsScalarTower K F L] [FiniteDimensional K F] [FiniteDimensional F L] (ω : AS.Ω) :
    (Σ x : BaseFiber (AS := AS) F ω,
      BaseFiber (AS := AS.finiteExtension F) L x.val) ≃ BaseFiber (AS := AS) L ω :=
  (Equiv.sigmaSubtypeFiberEquivSubtype
    (ParameterSpaceExtension.proj (AS := AS.finiteExtension F)
      (L := separableClosure F L))
    (p := fun y ↦ y.base.base = ω) (q := fun x ↦ x.base = ω)
    (fun _ ↦ Iff.rfl)).trans
    ((towerMeasurableEquiv AS L F).toEquiv.subtypeEquiv (fun _ ↦ Iff.rfl))

/-- The weight of a direct place is the product of its two successive weights. -/
theorem tower_fibreWeight (F : Type*) [Field F] [Algebra K F]
    [Algebra F L] [IsScalarTower K F L] [FiniteDimensional K F] [FiniteDimensional F L] (ω : AS.Ω)
    (x : BaseFiber (AS := AS) F ω) (y : BaseFiber (AS := AS.finiteExtension F) L x.val) :
    ParameterSpaceExtension.fibreWeight AS (separableClosure K F) ω x *
      ParameterSpaceExtension.fibreWeight (AS.finiteExtension F)
        (separableClosure F L) x.val y =
      ParameterSpaceExtension.fibreWeight AS (separableClosure K L) ω
        (towerFiberEquiv AS L F ω ⟨x, y⟩) := by
  let w := ϕ (AS.finiteExtension F) L y.val
  have hw : w.restriction F = ϕ AS F x.val := by
    exact (measurableEquivFull (AS.finiteExtension F) L y.val).restrict_eq.trans
      (congrArg (ϕ AS F) y.property)
  rw [fibreWeight_eq_finSepDegree AS F ω x,
    fibreWeight_eq_finSepDegree (AS.finiteExtension F) L x.val y,
    fibreWeight_eq_finSepDegree AS L ω]
  change (_ / (Field.finSepDegree K F : ℝ≥0∞)) *
      (_ / (Field.finSepDegree F L : ℝ≥0∞)) =
    (Field.finSepDegree ((ϕ AS L (towerMeasurableEquiv AS L F y.val)).restriction K).Completion
      (ϕ AS L (towerMeasurableEquiv AS L F y.val)).Completion : ℝ≥0∞) /
        (Field.finSepDegree K L : ℝ≥0∞)
  rw [towerMeasurableEquiv_ϕ, ← hw]
  rw [← ENNReal.mul_div_mul_comm (Or.inr (by simp)) (Or.inl (by simp))]
  rw [← Nat.cast_mul, AbsoluteValue.localFinSepDegree_mul w F, ← Nat.cast_mul,
    Field.finSepDegree_mul_finSepDegree_of_isAlgebraic K F L]

end ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension


namespace ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension
open MeasureTheory
open scoped ENNReal
variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Real fibre integration is transitive through finite extensions. -/
theorem fibreIntegral_tower (F : Type*) [Field F] [Algebra K F]
    [Algebra F L] [IsScalarTower K F L] [FiniteDimensional K F] [FiniteDimensional F L]
    (g : ParameterSpaceFinExtension (AS.finiteExtension F) L → ℝ) (ω : AS.Ω) :
    fibreIntegral AS F (fibreIntegral (AS.finiteExtension F) L g) ω =
      fibreIntegral AS L (g ∘ (towerMeasurableEquiv AS L F).symm) ω := by
  classical
  let : ∀ ω : AS.Ω, Fintype (BaseFiber (AS := AS) F ω) :=
    fun ω ↦ @Fintype.ofFinite _ (ParameterSpaceExtension.finite_extensionFiber AS _ ω)
  let : ∀ x : ParameterSpaceFinExtension AS F,
      Fintype (BaseFiber (AS := AS.finiteExtension F) L x) :=
    fun x ↦ @Fintype.ofFinite _
      (ParameterSpaceExtension.finite_extensionFiber
        (AS.finiteExtension F) (separableClosure F L) x)
  let : Fintype (BaseFiber (AS := AS) L ω) :=
    @Fintype.ofFinite _ (ParameterSpaceExtension.finite_extensionFiber AS _ ω)
  erw [fibreIntegral_eq_sum AS F, fibreIntegral_eq_sum AS L,
    ← (towerFiberEquiv AS L F ω).sum_comp, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x hx
  erw [fibreIntegral_eq_sum (AS.finiteExtension F) L, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← tower_fibreWeight AS L F ω x y, ENNReal.toReal_mul]
  change _ * (_ * g y.val) = (_ * _) *
    g ((towerMeasurableEquiv AS L F).symm (towerMeasurableEquiv AS L F y.val))
  rw [(towerMeasurableEquiv AS L F).symm_apply_apply, mul_assoc]
end ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension


namespace ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension
open MeasureTheory
open scoped ENNReal
variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Nonnegative fibre integration is transitive through finite extensions. -/
theorem fibreLIntegral_tower (F : Type*) [Field F] [Algebra K F]
    [Algebra F L] [IsScalarTower K F L] [FiniteDimensional K F] [FiniteDimensional F L]
    (g : ParameterSpaceFinExtension (AS.finiteExtension F) L → ℝ≥0∞) (ω : AS.Ω) :
    fibreLIntegral AS F (fibreLIntegral (AS.finiteExtension F) L g) ω =
      fibreLIntegral AS L (g ∘ (towerMeasurableEquiv AS L F).symm) ω := by
  classical
  let : ∀ ω : AS.Ω, Fintype (BaseFiber (AS := AS) F ω) :=
    fun ω ↦ @Fintype.ofFinite _ (ParameterSpaceExtension.finite_extensionFiber AS _ ω)
  let : ∀ x : ParameterSpaceFinExtension AS F,
      Fintype (BaseFiber (AS := AS.finiteExtension F) L x) :=
    fun x ↦ @Fintype.ofFinite _
      (ParameterSpaceExtension.finite_extensionFiber
        (AS.finiteExtension F) (separableClosure F L) x)
  let : Fintype (BaseFiber (AS := AS) L ω) :=
    @Fintype.ofFinite _ (ParameterSpaceExtension.finite_extensionFiber AS _ ω)
  erw [fibreLIntegral_eq_sum AS F, fibreLIntegral_eq_sum AS L,
    ← (towerFiberEquiv AS L F ω).sum_comp, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x hx
  erw [fibreLIntegral_eq_sum (AS.finiteExtension F) L, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← tower_fibreWeight AS L F ω x y]
  change _ * (_ * g y.val) = (_ * _) *
    g ((towerMeasurableEquiv AS L F).symm (towerMeasurableEquiv AS L F y.val))
  rw [(towerMeasurableEquiv AS L F).symm_apply_apply, mul_assoc]
end ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension


namespace ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension
open MeasureTheory
open scoped ENNReal
variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The canonical finite tower identification preserves the induced measure. -/
theorem map_towerMeasurableEquiv (F : Type*) [Field F] [Algebra K F]
    [Algebra F L] [IsScalarTower K F L] [FiniteDimensional K F] [FiniteDimensional F L] :
    Measure.map (towerMeasurableEquiv AS L F)
      ((AS.finiteExtension F).finiteExtension L).v = (AS.finiteExtension L).v := by
  apply Measure.ext_of_lintegral
  intro f hf
  erw [lintegral_map hf (towerMeasurableEquiv AS L F).measurable]
  erw [lintegral_measure (AS.finiteExtension F) L
      (hf.comp (towerMeasurableEquiv AS L F).measurable),
    lintegral_measure AS L hf,
    lintegral_measure AS F (measurable_fibreLIntegral (AS.finiteExtension F) L
      (hf.comp (towerMeasurableEquiv AS L F).measurable))]
  apply lintegral_congr
  intro ω
  change fibreLIntegral AS F
      (fibreLIntegral (AS.finiteExtension F) L (f ∘ towerMeasurableEquiv AS L F)) ω =
    fibreLIntegral AS L f ω
  rw [fibreLIntegral_tower]
  congr 1
  funext x
  exact congrArg f ((towerMeasurableEquiv AS L F).apply_symm_apply x)

/-- Successive and direct finite extensions are canonically equivalent adelic structures. -/
noncomputable def towerEquiv (F : Type*) [Field F] [Algebra K F]
    [Algebra F L] [IsScalarTower K F L] [FiniteDimensional K F] [FiniteDimensional F L] :
    AdelicStructure.Equiv ((AS.finiteExtension F).finiteExtension L) (AS.finiteExtension L) where
  toMeasurableEquiv := towerMeasurableEquiv AS L F
  ϕ_comp := towerMeasurableEquiv_ϕ AS L F
  map_v := map_towerMeasurableEquiv AS L F
end ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension


namespace ArakelovGeometry
open AdelicStructure
variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (M : Type*) [Field M] [Algebra K M]

/-- Chen–Moriwaki, Proposition 3.4.4: finite extension is transitive, preserving
the base projection and every real fibre integral. -/
theorem exists_equiv_finiteExtension_finiteExtension [FiniteDimensional K M]
    (F : IntermediateField K M) :
    ∃ e : AdelicStructure.Equiv
        ((AS.finiteExtension F).finiteExtension M) (AS.finiteExtension M),
      (∀ x, ParameterSpaceExtension.proj (ParameterSpaceExtension.proj x) =
        ParameterSpaceExtension.proj (e.toMeasurableEquiv x)) ∧
      ∀ g : ((AS.finiteExtension F).finiteExtension M).Ω → ℝ,
        ParameterSpaceFinExtension.fibreIntegral AS F
            (ParameterSpaceFinExtension.fibreIntegral (AS.finiteExtension F) M g) =
          ParameterSpaceFinExtension.fibreIntegral AS M
            (fun y ↦ g (e.toMeasurableEquiv.symm y)) := by
  refine ⟨ParameterSpaceFinExtension.towerEquiv AS M F, ?_, ?_⟩
  · intro x
    exact (ParameterSpaceFinExtension.towerMeasurableEquiv_proj AS M F x).symm
  · intro g
    funext ω
    exact ParameterSpaceFinExtension.fibreIntegral_tower AS M F g ω
end ArakelovGeometry
