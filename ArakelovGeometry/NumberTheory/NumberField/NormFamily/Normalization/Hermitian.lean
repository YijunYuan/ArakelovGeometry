/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Strong
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Hermitian.Basic
public import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Normalization.Basic
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Rational
import ArakelovGeometry.Analysis.AbsoluteValue.NormalizedCompletion
import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Normalization.ReverseDomination

/-!
# Actual strong domination and Hermitian number-field normalization

Both curves have their actual usual Archimedean completed fields. Strong
domination is compared through genuine bidual isometries. Hermitianity is
transported and reflected through the actual completed parallelogram law.
-/

@[expose] public section

open NumberField
open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

open AdelicStructure

variable {K : Type*} [Field K] [NumberField K]
  {E : Type*} [AddCommGroup E] [Module K E]

namespace AdelicStructure

/-- Every actual old infinite representative has the usual value at two. -/
theorem numberFieldPlace_apply_two_of_mem_inf (ω : AbsoluteValue.Place K)
    (hω : ω ∈ (numberFieldAdelicStructure K).Ωinf) : placeRep ω (2 : K) = 2 := by
  change ¬ IsNonarchimedean (placeRep ω) at hω
  rcases place_trichotomy ω with ht | ⟨v, hv⟩ | ⟨w, hw⟩
  · have hn := (NumberField.isNonarchimedean_congr (placeRep_equiv ω)).mp
      (ht.symm ▸ AbsoluteValue.isNonarchimedeanPlace_trivialPlace)
    exact False.elim (hω hn)
  · have hn : IsNonarchimedean (placeRep ω) := by
      rw [hv, placeRep_mk_finitePlace]
      exact NumberField.finitePlace_isNonarchimedean v
    exact False.elim (hω hn)
  · rw [hw, placeRep_mk_infinitePlace]
    exact infinitePlace_apply_two w

/-- The actual old Archimedean completed fields carry their usual norm. -/
theorem numberFieldArchimedeanCompletions :
    ∀ ω ∈ (numberFieldAdelicStructure K).Ωinf,
      IsRCLikeNormedField ((numberFieldAdelicStructure K).ϕ ω).Completion := by
  intro ω hω
  apply isRCLikeNormedField_of_norm_two
  have hn := (numberFieldAdelicStructure K).norm_algebraMap_eq_absValue ω (2 : K)
  have hm : algebraMap K ((numberFieldAdelicStructure K).ϕ ω).Completion (2 : K) =
      (2 : ((numberFieldAdelicStructure K).ϕ ω).Completion) := map_ofNat _ 2
  exact (congrArg Norm.norm hm).symm.trans
    (hn.trans (numberFieldPlace_apply_two_of_mem_inf ω hω))

/-- The actual infinite locus is unchanged at every nontrivial class. -/
theorem normalizedPlace_mem_inf_iff
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) :
    ω ∈ (normalizedNumberFieldAdelicStructure K).Ωinf ↔
      ω.val ∈ (numberFieldAdelicStructure K).Ωinf := by
  change ¬ IsNonarchimedean (normalizedPlaceValue ω) ↔ ¬ IsNonarchimedean (placeRep ω.val)
  exact not_congr (NumberField.isNonarchimedean_congr (normalizedPlaceValue_isEquiv_placeRep ω))

/-- The actual normalized Archimedean completed fields also carry their usual norm. -/
theorem normalizedNumberFieldArchimedeanCompletions :
    ∀ ω ∈ (normalizedNumberFieldAdelicStructure K).Ωinf,
      IsRCLikeNormedField ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion := by
  intro ω hω
  apply isRCLikeNormedField_of_norm_two
  have hvalue : (normalizedNumberFieldAdelicStructure K).ϕ ω (2 : K) = 2 := by
    change normalizedPlaceValue ω (2 : K) = 2
    exact (normalizedPlace_value_eq_of_not_mem_fin ω hω (2 : K)).trans
      (numberFieldPlace_apply_two_of_mem_inf ω.val ((normalizedPlace_mem_inf_iff ω).mp hω))
  have hn := (normalizedNumberFieldAdelicStructure K).norm_algebraMap_eq_absValue ω (2 : K)
  have hm : algebraMap K ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion (2 : K) =
      (2 : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion) := map_ofNat _ 2
  exact (congrArg Norm.norm hm).symm.trans (hn.trans hvalue)

end AdelicStructure

namespace NormFamily

variable (ξ : NormFamily (numberFieldAdelicStructure K) E) (hξ : ξ.IsUltrametric)

/-- Actual Hermitianity is preserved and reflected on the canonical completed fibres. -/
theorem numberFieldNormalize_isHermitian_iff :
    (ξ.numberFieldNormalize hξ).IsHermitian normalizedNumberFieldArchimedeanCompletions ↔
      ξ.IsHermitian numberFieldArchimedeanCompletions := by
  constructor
  · intro hnew
    have hp := isHermitian_iff_parallelogram.mp hnew
    apply isHermitian_iff_parallelogram.mpr
    refine ⟨hξ, ?_⟩
    intro ω hω x y
    have hnt : ω ≠ AbsoluteValue.trivialPlace K := by
      intro he
      have hn := (NumberField.isNonarchimedean_congr (placeRep_equiv ω)).mp
        (he.symm ▸ AbsoluteValue.isNonarchimedeanPlace_trivialPlace)
      exact hω hn
    let v : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K} := ⟨ω, hnt⟩
    have hv : v ∈ (normalizedNumberFieldAdelicStructure K).Ωinf :=
      (normalizedPlace_mem_inf_iff v).mpr hω
    have he := hp.2 v hv (normalizedNormFamilyTensorEquiv v x)
      (normalizedNormFamilyTensorEquiv v y)
    erw [← (normalizedNormFamilyTensorEquiv v).map_add x y,
      ← (normalizedNormFamilyTensorEquiv v).map_sub x y] at he
    erw [ξ.numberFieldNormalize_norm_map_inf hξ v hv (x + y),
      ξ.numberFieldNormalize_norm_map_inf hξ v hv (x - y),
      ξ.numberFieldNormalize_norm_map_inf hξ v hv x,
      ξ.numberFieldNormalize_norm_map_inf hξ v hv y] at he
    exact he
  · intro hold
    have hp := isHermitian_iff_parallelogram.mp hold
    apply isHermitian_iff_parallelogram.mpr
    refine ⟨ξ.numberFieldNormalize_isUltrametric hξ, ?_⟩
    intro ω hω x y
    obtain ⟨a, rfl⟩ := (normalizedNormFamilyTensorEquiv ω).surjective x
    obtain ⟨b, rfl⟩ := (normalizedNormFamilyTensorEquiv ω).surjective y
    erw [← (normalizedNormFamilyTensorEquiv ω).map_add a b,
      ← (normalizedNormFamilyTensorEquiv ω).map_sub a b]
    erw [ξ.numberFieldNormalize_norm_map_inf hξ ω hω (a + b),
      ξ.numberFieldNormalize_norm_map_inf hξ ω hω (a - b),
      ξ.numberFieldNormalize_norm_map_inf hξ ω hω a,
      ξ.numberFieldNormalize_norm_map_inf hξ ω hω b]
    exact hp.2 ω.val ((normalizedPlace_mem_inf_iff ω).mp hω) a b

/-- A Hermitian old family transports to a Hermitian actual normalized family. -/
theorem IsHermitian.numberFieldNormalize
    {ξ : NormFamily (numberFieldAdelicStructure K) E}
    (h : ξ.IsHermitian numberFieldArchimedeanCompletions) :
    (ξ.numberFieldNormalize h.1).IsHermitian normalizedNumberFieldArchimedeanCompletions :=
  (ξ.numberFieldNormalize_isHermitian_iff h.1).mpr h

variable [FiniteDimensional K E]

/-- Strong domination is equivalent under actual number-field normalization. -/
theorem numberFieldNormalize_isStronglyDominated_iff :
    (ξ.numberFieldNormalize hξ).IsStronglyDominated ↔ ξ.IsStronglyDominated :=
  ((ξ.numberFieldNormalize hξ).isStronglyDominated_iff_isDominated_of_ultrametric
    (ξ.numberFieldNormalize_isUltrametric hξ) normalizedNumberFieldArchimedeanCompletions).trans
      ((ξ.numberFieldNormalize_isDominated_iff hξ).trans
        (ξ.isStronglyDominated_iff_isDominated_of_ultrametric hξ
          numberFieldArchimedeanCompletions).symm)

/-- A strongly dominated old family has a strongly dominated normalized family. -/
theorem IsStronglyDominated.numberFieldNormalize
    {ξ : NormFamily (numberFieldAdelicStructure K) E} (hξ : ξ.IsUltrametric)
    (h : ξ.IsStronglyDominated) : (ξ.numberFieldNormalize hξ).IsStronglyDominated :=
  (ξ.numberFieldNormalize_isStronglyDominated_iff hξ).mpr h

end NormFamily

end ArakelovGeometry
