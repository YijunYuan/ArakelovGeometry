/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.FiniteTower

/-!
# Fibre probabilities under descended base change

Finite field descent preserving the separable degree preserves the probability
distribution of extending absolute values. Embedding counts give the comparison
without a choice of local tensor-product factors.
-/

namespace ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension
open MeasureTheory
open scoped ENNReal
variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- A finite fibre is the finite set of all extending absolute values. -/
noncomputable def fibreEquivAbsoluteValues (ω : AS.Ω) :
    BaseFiber (AS := AS) L ω ≃ {w : AbsoluteValue L ℝ // w.restriction K = AS.ϕ ω} where
  toFun x := ⟨ϕ AS L x.val,
    (measurableEquivFull AS L x.val).restrict_eq.trans (congrArg AS.ϕ x.property)⟩
  invFun w := ⟨(measurableEquivFull AS L).symm ⟨ω, w.val, w.property⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply (measurableEquivFull AS L).injective
    rw [(measurableEquivFull AS L).apply_symm_apply]
    exact ParameterSpaceExtension.ext AS L x.property.symm rfl
  right_inv w := by
    apply Subtype.ext
    exact congrArg ParameterSpaceExtension.abv
      ((measurableEquivFull AS L).apply_symm_apply ⟨ω, w.val, w.property⟩)

theorem lintegral_fibreProbabilityMeasure_eq_sum_localFinSepDegree
    (ω : AS.Ω) (f : BaseFiber (AS := AS) L ω → ℝ≥0∞)
    [Fintype {w : AbsoluteValue L ℝ // w.restriction K = AS.ϕ ω}] :
    ∫⁻ x, f x ∂fibreProbabilityMeasure AS L ω =
      (Field.finSepDegree K L : ℝ≥0∞)⁻¹ *
        ∑ w : {w : AbsoluteValue L ℝ // w.restriction K = AS.ϕ ω},
          (Field.finSepDegree (w.val.restriction K).Completion w.val.Completion : ℝ≥0∞) *
            f ((fibreEquivAbsoluteValues AS L ω).symm w) := by
  classical
  let : Fintype (BaseFiber (AS := AS) L ω) :=
    Fintype.ofEquiv _ (fibreEquivAbsoluteValues AS L ω).symm
  unfold fibreProbabilityMeasure ParameterSpaceExtension.fibreProbabilityMeasure
  rw [lintegral_sum_measure, tsum_fintype]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rw [← (fibreEquivAbsoluteValues AS L ω).symm.sum_comp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [fibreWeight_eq_finSepDegree]
  have hval : ϕ AS L ((fibreEquivAbsoluteValues AS L ω).symm w).val = w.val :=
    congrArg Subtype.val ((fibreEquivAbsoluteValues AS L ω).apply_symm_apply w)
  rw [hval]
  simp only [div_eq_mul_inv]
  ac_rfl

end ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension

namespace ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension
open MeasureTheory
open scoped ENNReal
variable {A B N : Type*} [Field A] [Field B] [Field N]
variable [Algebra A B] [Algebra A N] [Algebra B N] [IsScalarTower A B N]
variable [FiniteDimensional B N] (S : AdelicStructure A) (T : AdelicStructure B)
variable (E : IntermediateField A N) [FiniteDimensional A E]
variable (x : S.Ω) (y : T.Ω) (hxy : (T.ϕ y).restriction A = S.ϕ x)

/-- Restrict a finite extension place along a change of its base field. -/
noncomputable def baseChangeFiber :
    BaseFiber (AS := T) N y → BaseFiber (AS := S) E x :=
  fun w ↦ (fibreEquivAbsoluteValues S E x).symm
    ⟨((fibreEquivAbsoluteValues T N y) w).val.restriction E, by
      ext a
      change ((fibreEquivAbsoluteValues T N y) w).val (algebraMap A N a) = S.ϕ x a
      rw [IsScalarTower.algebraMap_apply A B N]
      exact (congrArg (fun v : AbsoluteValue B ℝ ↦ v (algebraMap A B a))
        ((fibreEquivAbsoluteValues T N y) w).property).trans
          (congrArg (fun v : AbsoluteValue A ℝ ↦ v a) hxy)⟩

@[simp]
theorem baseChangeFiber_ϕ (w : BaseFiber (AS := T) N y) :
    ϕ S E (baseChangeFiber S T E x y hxy w).val =
      (ϕ T N w.val).restriction E := by
  exact congrArg Subtype.val
    ((fibreEquivAbsoluteValues S E x).apply_symm_apply _)

end ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension

namespace ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension
open MeasureTheory
open scoped ENNReal
variable {A B N : Type*} [Field A] [Field B] [Field N]
variable [Algebra A B] [Algebra A N] [Algebra B N] [IsScalarTower A B N]
variable [FiniteDimensional B N] (S : AdelicStructure A) (T : AdelicStructure B)
variable (E : IntermediateField A N) [FiniteDimensional A E]
variable (x : S.Ω) (y : T.Ω) (hxy : (T.ϕ y).restriction A = S.ϕ x)

/-- Restriction preserves finite fibre probabilities under descended base change. -/
theorem map_fibreProbabilityMeasure_baseChangeFiber
    (hgen : IntermediateField.adjoin B (E : Set N) = ⊤)
    (hsep : Field.finSepDegree A E = Field.finSepDegree B N) :
    Measure.map (baseChangeFiber S T E x y hxy) (fibreProbabilityMeasure T N y) =
      fibreProbabilityMeasure S E x := by
  classical
  let : Finite (BaseFiber (AS := T) N y) :=
    ParameterSpaceExtension.finite_extensionFiber T (separableClosure B N) y
  let : Finite (BaseFiber (AS := S) E x) :=
    ParameterSpaceExtension.finite_extensionFiber S (separableClosure A E) x
  let : Fintype (BaseFiber (AS := T) N y) := Fintype.ofFinite _
  let : Fintype (BaseFiber (AS := S) E x) := Fintype.ofFinite _
  let : Fintype {w : AbsoluteValue N ℝ // w.restriction B = T.ϕ y} :=
    Fintype.ofEquiv (BaseFiber (AS := T) N y) (fibreEquivAbsoluteValues T N y)
  let : Fintype {v : AbsoluteValue E ℝ // v.restriction A = S.ϕ x} :=
    Fintype.ofEquiv (BaseFiber (AS := S) E x) (fibreEquivAbsoluteValues S E x)
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_of_countable _),
    lintegral_fibreProbabilityMeasure_eq_sum_localFinSepDegree,
    lintegral_fibreProbabilityMeasure_eq_sum_localFinSepDegree, ← hsep]
  congr 1
  let φ (v : AbsoluteValue E ℝ) : ℝ≥0∞ :=
    if hv : v.restriction A = S.ϕ x then
      f ((fibreEquivAbsoluteValues S E x).symm ⟨v, hv⟩) else 0
  have hφ (z : BaseFiber (AS := S) E x) : φ (ϕ S E z.val) = f z := by
    dsimp only [φ]
    have hz : (ϕ S E z.val).restriction A = S.ϕ x :=
      ((fibreEquivAbsoluteValues S E x) z).property
    rw [dif_pos hz]
    exact congrArg f ((fibreEquivAbsoluteValues S E x).symm_apply_apply z)
  have h := AbsoluteValue.sum_localFinSepDegree_nsmul_baseChange E hgen hsep
    (T.ϕ y) (S.ϕ x) hxy φ
  simp only [nsmul_eq_mul] at h
  convert h using 1
  · apply Finset.sum_congr rfl
    intro w hw
    congr 1
    have hw' : ϕ T N ((fibreEquivAbsoluteValues T N y).symm w).val = w.val :=
      congrArg Subtype.val ((fibreEquivAbsoluteValues T N y).apply_symm_apply w)
    rw [← hw', ← baseChangeFiber_ϕ S T E x y hxy, hφ]
  · apply Finset.sum_congr rfl
    intro v hv
    congr 1
    dsimp only [φ]
    rw [dif_pos v.property]


/-- Nonnegative fibre integrals are unchanged under a descended base change. -/
theorem lintegral_baseChangeFiber
    (hgen : IntermediateField.adjoin B (E : Set N) = ⊤)
    (hsep : Field.finSepDegree A E = Field.finSepDegree B N)
    (f : BaseFiber (AS := S) E x → ℝ≥0∞) :
    (∫⁻ w, f (baseChangeFiber S T E x y hxy w) ∂fibreProbabilityMeasure T N y) =
      ∫⁻ v, f v ∂fibreProbabilityMeasure S E x := by
  let : Finite (BaseFiber (AS := T) N y) :=
    ParameterSpaceExtension.finite_extensionFiber T (separableClosure B N) y
  let : Finite (BaseFiber (AS := S) E x) :=
    ParameterSpaceExtension.finite_extensionFiber S (separableClosure A E) x
  rw [← lintegral_map (measurable_of_countable f)
    (measurable_of_countable (baseChangeFiber S T E x y hxy)),
    map_fibreProbabilityMeasure_baseChangeFiber S T E x y hxy hgen hsep]

end ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension

namespace ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension
open MeasureTheory
open scoped ENNReal
variable {K E N : Type*} [Field K] [Field E] [Field N]
variable [Algebra K E] [Algebra K N] [FiniteDimensional K E] [FiniteDimensional K N]
variable (AS : AdelicStructure K) (i : E →ₐ[K] N) (ω : AS.Ω)

/-- Pull back a finite place along a field embedding over the base. -/
noncomputable def homFiber : BaseFiber (AS := AS) N ω → BaseFiber (AS := AS) E ω :=
  fun w ↦ (fibreEquivAbsoluteValues AS E ω).symm
    ⟨((fibreEquivAbsoluteValues AS N ω) w).val.pullback i.toRingHom, by
      ext a
      change ((fibreEquivAbsoluteValues AS N ω) w).val (i (algebraMap K E a)) = AS.ϕ ω a
      rw [i.commutes]
      exact congrArg (fun v : AbsoluteValue K ℝ ↦ v a)
        ((fibreEquivAbsoluteValues AS N ω) w).property⟩

@[simp]
theorem homFiber_ϕ (w : BaseFiber (AS := AS) N ω) :
    ϕ AS E (homFiber AS i ω w).val = (ϕ AS N w.val).pullback i.toRingHom :=
  congrArg Subtype.val ((fibreEquivAbsoluteValues AS E ω).apply_symm_apply _)

/-- Finite fibre probabilities are natural under every base-field embedding. -/
theorem map_fibreProbabilityMeasure_homFiber :
    Measure.map (homFiber AS i ω) (fibreProbabilityMeasure AS N ω) =
      fibreProbabilityMeasure AS E ω := by
  classical
  let : Finite (BaseFiber (AS := AS) N ω) :=
    ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K N) ω
  let : Finite (BaseFiber (AS := AS) E ω) :=
    ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K E) ω
  let : Fintype (BaseFiber (AS := AS) N ω) := Fintype.ofFinite _
  let : Fintype (BaseFiber (AS := AS) E ω) := Fintype.ofFinite _
  let : Fintype {w : AbsoluteValue N ℝ // w.restriction K = AS.ϕ ω} :=
    Fintype.ofEquiv (BaseFiber (AS := AS) N ω) (fibreEquivAbsoluteValues AS N ω)
  let : Fintype {v : AbsoluteValue E ℝ // v.restriction K = AS.ϕ ω} :=
    Fintype.ofEquiv (BaseFiber (AS := AS) E ω) (fibreEquivAbsoluteValues AS E ω)
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_of_countable _),
    lintegral_fibreProbabilityMeasure_eq_sum_localFinSepDegree,
    lintegral_fibreProbabilityMeasure_eq_sum_localFinSepDegree]
  rw [← ENNReal.div_eq_inv_mul, ← ENNReal.div_eq_inv_mul]
  apply (ENNReal.div_eq_div_iff (by exact_mod_cast (NeZero.ne (Field.finSepDegree K E)))
    (by simp) (by exact_mod_cast (NeZero.ne (Field.finSepDegree K N))) (by simp)).mpr
  let φ (v : AbsoluteValue E ℝ) : ℝ≥0∞ :=
    if hv : v.restriction K = AS.ϕ ω then
      f ((fibreEquivAbsoluteValues AS E ω).symm ⟨v, hv⟩) else 0
  have hφ (z : BaseFiber (AS := AS) E ω) : φ (ϕ AS E z.val) = f z := by
    dsimp only [φ]
    have hz : (ϕ AS E z.val).restriction K = AS.ϕ ω :=
      ((fibreEquivAbsoluteValues AS E ω) z).property
    rw [dif_pos hz]
    exact congrArg f ((fibreEquivAbsoluteValues AS E ω).symm_apply_apply z)
  have h := AbsoluteValue.finSepDegree_nsmul_sum_localFinSepDegree_pullback i (AS.ϕ ω) φ
  simp only [nsmul_eq_mul] at h
  convert h using 1
  · congr 1
    apply Finset.sum_congr rfl
    intro w hw
    congr 1
    have hw' : ϕ AS N ((fibreEquivAbsoluteValues AS N ω).symm w).val = w.val :=
      congrArg Subtype.val ((fibreEquivAbsoluteValues AS N ω).apply_symm_apply w)
    rw [← hw', ← homFiber_ϕ AS i ω, hφ]
  · congr 1
    apply Finset.sum_congr rfl
    intro v hv
    congr 1
    dsimp only [φ]
    rw [dif_pos v.property]

/-- Pullback along a field embedding preserves every nonnegative finite fibre integral. -/
theorem lintegral_homFiber (f : BaseFiber (AS := AS) E ω → ℝ≥0∞) :
    (∫⁻ w, f (homFiber AS i ω w) ∂fibreProbabilityMeasure AS N ω) =
      ∫⁻ v, f v ∂fibreProbabilityMeasure AS E ω := by
  let : Finite (BaseFiber (AS := AS) N ω) :=
    ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K N) ω
  let : Finite (BaseFiber (AS := AS) E ω) :=
    ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K E) ω
  rw [← lintegral_map (measurable_of_countable f) (measurable_of_countable (homFiber AS i ω)),
    map_fibreProbabilityMeasure_homFiber AS i ω]

end ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension
