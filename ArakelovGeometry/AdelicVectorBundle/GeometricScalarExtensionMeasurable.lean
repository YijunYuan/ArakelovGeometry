/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.GeometricScalarExtensionExceptions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Actual finite scalar measurability on positive atomic bases

Finite actual extension fibres produce measurable singletons. The one produced
countable base exceptional set lifts to a countable set, where arbitrary norm
values can replace measurable coordinate values. No whole original or extending
parameter space is assumed countable or discrete.
-/

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] {S : AdelicStructure K}

namespace AdelicStructure.ParameterSpaceExtension

/-- Finite fibres with their actual evaluation sigma-algebra make extending
singletons measurable over any base with measurable singletons. -/
theorem measurableSingletonClass_of_finiteDimensional
    [MeasurableSingletonClass S.Ω] :
    MeasurableSingletonClass (S.ParameterSpaceExtension L) := by
  constructor
  intro x
  let : Finite (AdelicStructure.ExtensionFiber S L x.base) :=
    finite_extensionFiber S L x.base
  have hs : MeasurableSet {y : S.ParameterSpaceExtension L | y.proj = x.base} :=
    (measurable_proj S L) (measurableSet_singleton x.base)
  let u : AdelicStructure.ExtensionFiber S L x.base := ⟨x, rfl⟩
  have hu : MeasurableSet ({u} : Set (AdelicStructure.ExtensionFiber S L x.base)) :=
    (Set.toFinite _).measurableSet
  have hm := hs.subtype_image hu
  have himg :
      (Subtype.val : AdelicStructure.ExtensionFiber S L x.base → S.ParameterSpaceExtension L) ''
        ({u} : Set (AdelicStructure.ExtensionFiber S L x.base)) = {x} := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : t = u := ht
      subst t
      exact rfl
    · intro hy
      have hy' : y = x := hy
      subst y
      exact ⟨u, rfl, rfl⟩
  exact (congrArg (fun A : Set (S.ParameterSpaceExtension L) => MeasurableSet A) himg).mp hm

/-- A countable base set has countable actual preimage under finite extension;
the base and entire extension parameter spaces may both be uncountable. -/
theorem countable_preimage_proj_of_finiteDimensional (T : Set S.Ω) (hT : T.Countable) :
    ((proj (AS := S) (L := L)) ⁻¹' T).Countable := by
  have he : proj (AS := S) (L := L) ⁻¹' T =
      ⋃ ω ∈ T, {x : S.ParameterSpaceExtension L | proj x = ω} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨proj x, h, rfl⟩, fun ⟨ω, hω, hx⟩ => hx ▸ hω⟩
  rw [he]
  apply hT.biUnion
  intro ω _
  have hf : {x : S.ParameterSpaceExtension L | proj x = ω}.Finite :=
    Set.finite_coe_iff.mp (finite_extensionFiber S L ω)
  exact hf.countable

end AdelicStructure.ParameterSpaceExtension

/-- The actual projective algebraic-extension sigma-algebra has measurable
singletons at finite extensions, without assuming a countable base. -/
theorem AdelicStructure.measurableSingletonClass_algebraicExtension_of_finiteDimensional
    [MeasurableSingletonClass S.Ω] :
    MeasurableSingletonClass (S.algebraicExtension L).Ω := by
  change @MeasurableSingletonClass (S.ParameterSpaceExtension L)
    (AdelicStructure.Algebraic.projectiveMeasurableSpace S L)
  rw [AdelicStructure.Algebraic.projectiveMeasurableSpace_eq]
  exact ParameterSpaceExtension.measurableSingletonClass_of_finiteDimensional
    (S := S) (L := L)

namespace NormFamily
variable {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ι : Type*} [Finite ι]

/-- Domination and positive base atoms produce measurability of the actual
ordinary finite scalar extension. Original ultrametricity and countability
of the ground field or parameter spaces are not hypotheses. -/
theorem IsDominated.scalarExtension_isMeasurable_of_positive_atoms
    [MeasurableSingletonClass S.Ω] (ξ : NormFamily S E) (b : Module.Basis ι K E)
    (hξ : ξ.IsDominated) (hpos : ∀ ω : S.Ω, 0 < S.v {ω})
    (hfin : S.v S.Ωinf < ⊤) :
    (ξ.scalarExtension (L := L)).IsMeasurable := by
  let := Fintype.ofFinite ι
  let := AdelicStructure.measurableSingletonClass_algebraicExtension_of_finiteDimensional
    (S := S) (L := L)
  obtain ⟨H, _, _, hc, _, _, he⟩ :=
    IsDominated.exists_scalarExtension_coordinate_exceptions_of_positive_atoms ξ b hξ hpos hfin
  have ht := AdelicStructure.ParameterSpaceExtension.countable_preimage_proj_of_finiteDimensional
    (L := L) (Function.support H) hc
  intro z
  apply Measurable.measurable_of_countable_ne
    (ofBasisMixed_isMeasurable (S := S.algebraicExtension L) (b.baseChange L) z)
  apply ht.mono
  intro x hx
  by_contra h
  exact hx (he L x h ((1 : x.abv.Completion) ⊗ₜ[L] z)).symm

/-- Every dominated original family on the actual geometric projective line
has measurable finite scalar extensions, for every constant field. -/
theorem IsDominated.functionField_scalarExtension_isMeasurable
    {k L : Type*} [Field k] [Field L] [Algebra (RatFunc k) L]
    [FiniteDimensional (RatFunc k) L] {E : Type*} [AddCommGroup E]
    [Module (RatFunc k) E] [FiniteDimensional (RatFunc k) E]
    (ξ : NormFamily (AdelicStructure.functionFieldAdelicStructure k) E)
    (hξ : ξ.IsDominated) : (ξ.scalarExtension (L := L)).IsMeasurable := by
  apply IsDominated.scalarExtension_isMeasurable_of_positive_atoms ξ
    (Module.finBasis (RatFunc k) E) hξ AdelicStructure.functionField_singleton_pos
  rw [AdelicStructure.functionField_Ωinf_eq_empty, measure_empty]
  exact ENNReal.zero_lt_top

/-- The actual dual of the finite scalar extension is measurable from the
same produced exceptional set and the actual dual-distance contraction. -/
theorem IsDominated.scalarExtension_dual_isMeasurable_of_positive_atoms
    [MeasurableSingletonClass S.Ω] (ξ : NormFamily S E) (b : Module.Basis ι K E)
    (hξ : ξ.IsDominated) (hpos : ∀ ω : S.Ω, 0 < S.v {ω})
    (hfin : S.v S.Ωinf < ⊤) :
    (ξ.scalarExtension (L := L)).dual.IsMeasurable := by
  classical
  let := Fintype.ofFinite ι
  let := AdelicStructure.measurableSingletonClass_algebraicExtension_of_finiteDimensional
    (S := S) (L := L)
  obtain ⟨H, _, _, hc, _, hb, _⟩ :=
    IsDominated.exists_scalarExtension_coordinate_exceptions_of_positive_atoms ξ b hξ hpos hfin
  have ht := AdelicStructure.ParameterSpaceExtension.countable_preimage_proj_of_finiteDimensional
    (L := L) (Function.support H) hc
  let q := ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)
  intro z
  apply Measurable.measurable_of_countable_ne
    (ofBasisMixed_dual_isMeasurable (S := S.algebraicExtension L) (b.baseChange L) z)
  apply ht.mono
  intro x hx
  by_contra h
  have hd : (ξ.scalarExtension (L := L)).dual.localDist q.dual x = 0 :=
    le_antisymm
      (((ξ.scalarExtension (L := L)).localDist_dual_le q x).trans
        ((hb L x).trans_eq (Function.notMem_support.mp h)))
      ((ξ.scalarExtension (L := L)).dual.localDist_nonneg q.dual x)
  have he := ((ξ.scalarExtension (L := L)).dual.localDist_eq_zero_iff q.dual x).mp hd
  exact hx (congrArg (fun n => n ((1 : x.abv.Completion) ⊗ₜ[L] z)) he).symm

/-- Genuine geometric finite extensions have measurable actual dual norms,
for every original dominated family and every constant field. -/
theorem IsDominated.functionField_scalarExtension_dual_isMeasurable
    {k L : Type*} [Field k] [Field L] [Algebra (RatFunc k) L]
    [FiniteDimensional (RatFunc k) L] {E : Type*} [AddCommGroup E]
    [Module (RatFunc k) E] [FiniteDimensional (RatFunc k) E]
    (ξ : NormFamily (AdelicStructure.functionFieldAdelicStructure k) E)
    (hξ : ξ.IsDominated) : (ξ.scalarExtension (L := L)).dual.IsMeasurable := by
  apply IsDominated.scalarExtension_dual_isMeasurable_of_positive_atoms ξ
    (Module.finBasis (RatFunc k) E) hξ AdelicStructure.functionField_singleton_pos
  rw [AdelicStructure.functionField_Ωinf_eq_empty, measure_empty]
  exact ENNReal.zero_lt_top

end NormFamily
end ArakelovGeometry
