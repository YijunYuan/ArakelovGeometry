/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.GeometricAlgebraicScalarBundle
public import ArakelovGeometry.AdelicVectorBundle.LogarithmicMinimaBasis
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionBundle
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDiscreteBundle

/-!
# Actual absolute logarithmic minima

The definitions use the actual ordinary algebraic-closure norm family under
an explicit disjunction of the three available regularity alternatives.
Source indices are `1 ≤ i ≤ finrank K E`; index zero and indices above rank
are auxiliary extended-real conventions. Algebraic invariance and slope
comparisons are separate obligations.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry

universe u v w wL
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

namespace AdelicVectorBundle

/-- An actual ordinary scalar bundle from the explicit three regularity
alternatives. Its norm family is always the prescribed ordinary extension. -/
def ordinaryScalarExtension (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    AdelicVectorBundle (S.algebraicExtension L) (L ⊗[K] E) where
  toNormFamily := V.toNormFamily.scalarExtension
  isMeasurable := by
    rcases hreg with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
    · exact (V.scalarExtension (L := L) h hN).isMeasurable
    · let := hc
      let := hd
      exact (V.scalarExtensionOfCountableDiscreteBase (L := L) hN).isMeasurable
    · let := hm
      exact (V.toNormFamily.algebraicScalarBundleOfPositiveAtoms V.isDominated hp hf).isMeasurable
  dual_isMeasurable := by
    rcases hreg with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
    · exact (V.scalarExtension (L := L) h hN).dual_isMeasurable
    · let := hc
      let := hd
      exact (V.scalarExtensionOfCountableDiscreteBase (L := L) hN).dual_isMeasurable
    · let := hm
      exact (V.toNormFamily.algebraicScalarBundleOfPositiveAtoms
        V.isDominated hp hf).dual_isMeasurable
  isDominated := (NormFamily.IsDominated.scalarExtension_isStronglyDominated
    V.toNormFamily V.isDominated (S.v_Ωinf_lt_top_of_isRCLike hN)).isDominated

@[simp]
theorem ordinaryScalarExtension_toNormFamily (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.ordinaryScalarExtension (L := L) hreg hN).toNormFamily =
      V.toNormFamily.scalarExtension := rfl

end AdelicVectorBundle
namespace NormFamily

/-- The actual nonzero rational scalar section, using faithful base change. -/
def scalarExtensionNonzeroVector (s : {x : E // x ≠ 0}) :
    {x : L ⊗[K] E // x ≠ 0} :=
  ⟨(1 : L) ⊗ₜ[K] s.val, by
    intro hz
    apply s.property
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := K) (B := L) E
    change (1 : L) ⊗ₜ[K] s.val = (1 : L) ⊗ₜ[K] (0 : E)
    simpa only [TensorProduct.tmul_zero] using hz⟩

/-- The degree comparison for the actual scalar norm family. The target
regularity hypotheses are exactly those needed to define its vector degree. -/
theorem vectorDegree_le_scalarExtension (ξ : NormFamily S E)
    (hd : ξ.IsDominated) (hm : ξ.IsMeasurable)
    (hdL : (ξ.scalarExtension (L := L)).IsDominated)
    (hmL : (ξ.scalarExtension (L := L)).IsMeasurable) (s : {x : E // x ≠ 0}) :
    ξ.vectorDegree hd hm s ≤
      (ξ.scalarExtension (L := L)).vectorDegree hdL hmL
        (scalarExtensionNonzeroVector (L := L) s) := by
  have hi := hd.integrable_logNorm hm s.val
  have hiL := hdL.integrable_logNorm hmL (scalarExtensionNonzeroVector (L := L) s).val
  have hp : Integrable (fun x : (S.algebraicExtension L).Ω => ξ.logNorm s.val x.base)
      (S.algebraicExtension L).v :=
    AdelicStructure.Algebraic.integrable_comp_proj_measure S L hi
  have hle (x : (S.algebraicExtension L).Ω) :
      (ξ.scalarExtension (L := L)).logNorm (scalarExtensionNonzeroVector (L := L) s).val x ≤
        ξ.logNorm s.val x.base := by
    apply Real.log_le_log
      ((ξ.scalarExtension (L := L)).norm_rational_pos x
        (scalarExtensionNonzeroVector (L := L) s).property)
    exact ξ.scalarExtension_norm_one_tmul_le x s.val
  have h := integral_mono hiL hp hle
  have he : (∫ x : (S.algebraicExtension L).Ω, ξ.logNorm s.val x.base
      ∂(S.algebraicExtension L).v) = ∫ ω, ξ.logNorm s.val ω ∂S.v :=
    AdelicStructure.Algebraic.integral_comp_proj_measure S L hi
  rw [he] at h
  rw [vectorDegree_eq_neg_integral, vectorDegree_eq_neg_integral]
  exact neg_le_neg h

end NormFamily
namespace AdelicVectorBundle

/-- Coherence with the existing common-density ordinary scalar bundle. -/
theorem ordinaryScalarExtension_eq_common (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hc : S.HasCommonCountableDenseSubfield) :
    V.ordinaryScalarExtension (L := L) hreg hN = V.scalarExtension hc hN := rfl

/-- Coherence with the existing countable-discrete ordinary scalar bundle. -/
theorem ordinaryScalarExtension_eq_discrete [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]
    (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.ordinaryScalarExtension (L := L) hreg hN =
      V.scalarExtensionOfCountableDiscreteBase hN := rfl

/-- Coherence with the genuine all-finite positive-atomic scalar bundle. -/
theorem ordinaryScalarExtension_eq_positiveAtoms [MeasurableSingletonClass S.Ω]
    (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hp : ∀ ω, 0 < S.v {ω}) (hf : ∀ ω, ω ∈ S.Ωfin) :
    V.ordinaryScalarExtension (L := L) hreg hN =
      V.toNormFamily.algebraicScalarBundleOfPositiveAtoms V.isDominated hp hf := rfl

/-- Actual rational sections gain degree in every produced regularity branch. -/
theorem vectorDegree_le_ordinaryScalarExtension (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (s : {x : E // x ≠ 0}) :
    V.vectorDegree s ≤ (V.ordinaryScalarExtension (L := L) hreg hN).vectorDegree
      (NormFamily.scalarExtensionNonzeroVector (L := L) s) :=
  V.toNormFamily.vectorDegree_le_scalarExtension V.isDominated V.isMeasurable
    (V.ordinaryScalarExtension hreg hN).isDominated
    (V.ordinaryScalarExtension hreg hN).isMeasurable s

omit [FiniteDimensional K E] [Algebra.IsAlgebraic K L] in
private theorem originalSections_linearIndependent {ι : Type*} {s : ι → E}
    (hs : LinearIndependent K s) :
    LinearIndependent L (fun j => (1 : L) ⊗ₜ[K] s j) := by
  classical
  let I : Set E := hs.linearIndepOn_id.extend (Set.subset_univ _)
  let b : Module.Basis I K E := Module.Basis.extend hs.linearIndepOn_id
  let f (j : ι) : I :=
    ⟨s j, hs.linearIndepOn_id.subset_extend _ (Set.mem_range_self j)⟩
  have hf : Function.Injective f := fun i j h => hs.injective (congrArg Subtype.val h)
  have he : (b.baseChange L) ∘ f = (fun j => (1 : L) ⊗ₜ[K] s j) := by
    funext j
    rw [Function.comp_apply, Module.Basis.baseChange_apply]
    change (1 : L) ⊗ₜ[K] b (f j) = (1 : L) ⊗ₜ[K] s j
    exact congrArg (fun x : E => (1 : L) ⊗ₜ[K] x)
      (Module.Basis.extend_apply_self hs.linearIndepOn_id (f j))
  rw [← he]
  exact (b.baseChange L).linearIndependent.comp f hf

/-- All extended-real minima increase under actual algebraic scalar extension.
No supremum attainment or finiteness is used. -/
theorem logarithmicMinimum_le_ordinaryScalarExtension (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (i : ℕ) :
    V.logarithmicMinimum i ≤
      (V.ordinaryScalarExtension (L := L) hreg hN).logarithmicMinimum i := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  obtain ⟨s, hs, hd⟩ := (V.le_finrank_degreeThresholdSpan_iff i t).mp ht
  apply coe_le_logarithmicMinimum_of_linearIndependent
    (V.ordinaryScalarExtension (L := L) hreg hN)
    (fun j => NormFamily.scalarExtensionNonzeroVector (L := L) (s j))
  · exact originalSections_linearIndependent hs
  · intro j
    exact (hd j).trans (V.vectorDegree_le_ordinaryScalarExtension hreg hN (s j))


/-- Source Definition 4.3.69's absolute minimum uses the actual ordinary
closure bundle. Natural indices outside the source range are auxiliary. -/
def absoluteLogarithmicMinimum (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (i : ℕ) : EReal :=
  (V.ordinaryScalarExtension (L := AlgebraicClosure K) hreg hN).logarithmicMinimum i

/-- The actual first absolute minimum, with value bottom in rank zero. -/
def absoluteMaximalLogarithmicMinimum (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) : EReal :=
  V.absoluteLogarithmicMinimum hreg hN 1

/-- The actual last absolute minimum. Base change preserves its rank index,
and rank zero has the source value top. -/
def absoluteMinimalLogarithmicMinimum (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) : EReal :=
  V.absoluteLogarithmicMinimum hreg hN (Module.finrank K E)

/-- The inequality clause of source Proposition 4.3.71, extended to the
auxiliary natural indices. Absolute invariance is a separate assertion. -/
theorem logarithmicMinimum_le_absoluteLogarithmicMinimum (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (i : ℕ) : V.logarithmicMinimum i ≤ V.absoluteLogarithmicMinimum hreg hN i :=
  V.logarithmicMinimum_le_ordinaryScalarExtension (L := AlgebraicClosure K) hreg hN i

/-- The actual first ordinary minimum is at most its absolute version. -/
theorem maximalLogarithmicMinimum_le_absoluteMaximalLogarithmicMinimum
    (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.maximalLogarithmicMinimum ≤ V.absoluteMaximalLogarithmicMinimum hreg hN :=
  V.logarithmicMinimum_le_absoluteLogarithmicMinimum hreg hN 1

/-- The last comparison retains the source top convention in rank zero. -/
theorem minimalLogarithmicMinimum_le_absoluteMinimalLogarithmicMinimum
    (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.minimalLogarithmicMinimum ≤ V.absoluteMinimalLogarithmicMinimum hreg hN :=
  V.logarithmicMinimum_le_absoluteLogarithmicMinimum hreg hN (Module.finrank K E)

/-- Extended absolute minima decrease with their index. -/
theorem absoluteLogarithmicMinimum_antitone (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    Antitone (V.absoluteLogarithmicMinimum hreg hN) :=
  logarithmicMinimum_antitone
    (V.ordinaryScalarExtension (L := AlgebraicClosure K) hreg hN)

/-- Index zero is an auxiliary empty-family convention, distinct from the
source's valid positive indices. -/
theorem absoluteLogarithmicMinimum_zero (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.absoluteLogarithmicMinimum hreg hN 0 = ⊤ :=
  logarithmicMinimum_zero (V.ordinaryScalarExtension (L := AlgebraicClosure K) hreg hN)

/-- Auxiliary indices above original rank have empty threshold cuts. -/
theorem absoluteLogarithmicMinimum_eq_bot_of_finrank_lt (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    {i : ℕ} (hi : Module.finrank K E < i) :
    V.absoluteLogarithmicMinimum hreg hN i = ⊥ := by
  apply logarithmicMinimum_eq_bot_of_finrank_lt
    (V.ordinaryScalarExtension (L := AlgebraicClosure K) hreg hN)
  simpa only [Module.finrank_baseChange] using hi

/-- Source absolute first-minimum convention for the actual zero bundle. -/
theorem absoluteMaximalLogarithmicMinimum_eq_bot_of_finrank_eq_zero
    (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : Module.finrank K E = 0) :
    V.absoluteMaximalLogarithmicMinimum hreg hN = ⊥ :=
  V.absoluteLogarithmicMinimum_eq_bot_of_finrank_lt hreg hN (by omega)

/-- Source absolute last-minimum convention for the actual zero bundle. -/
theorem absoluteMinimalLogarithmicMinimum_eq_top_of_finrank_eq_zero
    (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
      (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : Module.finrank K E = 0) :
    V.absoluteMinimalLogarithmicMinimum hreg hN = ⊤ := by
  unfold absoluteMinimalLogarithmicMinimum
  rw [hr, V.absoluteLogarithmicMinimum_zero hreg hN]

end AdelicVectorBundle
end ArakelovGeometry
