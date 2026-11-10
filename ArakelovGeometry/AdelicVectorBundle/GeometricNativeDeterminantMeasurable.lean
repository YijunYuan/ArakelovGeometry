/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.GeometricCoordinateDeterminant
import ArakelovGeometry.AdelicVectorBundle.GeometricNativeSubquotientMeasurable
import ArakelovGeometry.AdelicVectorBundle.DeterminantComparison
import ArakelovGeometry.AdelicVectorBundle.ExteriorDomination

/-!
# Actual native determinant regularity after finite geometric extension

Determinant distance vanishes wherever the original families agree. The
produced countable exceptional set transfers actual coordinate determinant
measurability to native subspaces of original dominated scalar extensions.
-/

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.NormFamily

variable {K E : Type*} [Field K] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Actual determinant regularity transfers across a countable set of changes
to the completed norms. The reference determinant is a proved input. -/
theorem determinant_isMeasurable_of_countable_localDist_zero
    [MeasurableSingletonClass S.Ω] (ξ η : NormFamily S E)
    (hη : η.determinant.IsMeasurable) (T : Set S.Ω) (hT : T.Countable)
    (he : ∀ ω ∉ T, ξ.localDist η ω = 0) : ξ.determinant.IsMeasurable := by
  intro z
  apply Measurable.measurable_of_countable_ne (hη z)
  apply hT.mono
  intro ω hω
  by_contra hn
  have hd := ξ.determinant_localDist_le η ω
  rw [he ω hn, mul_zero] at hd
  have hzero := le_antisymm hd (ξ.determinant.localDist_nonneg η.determinant ω)
  have hnorm := (ξ.determinant.localDist_eq_zero_iff η.determinant ω).mp hzero
  exact hω (congrArg
    (fun p ↦ p ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] z)) hnorm).symm

variable {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]

private theorem allFinite_nativeDeterminant_scalarExtension
    (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    ∀ x : (S.algebraicExtension L).Ω, x ∈ (S.algebraicExtension L).Ωfin := by
  intro x
  change IsNonarchimedean x.abv
  apply (AbsoluteValue.isNonarchimedean_restriction_iff (K := K) x.abv).mp
  rw [x.restrict_eq]
  exact hS x.base

/-- Every native finite-extension subspace has a measurable actual determinant
on an all-finite positive atomic curve, for any original dominated family. -/
theorem IsDominated.scalarExtension_restrict_determinant_isMeasurable_of_positive_atoms
    [MeasurableSingletonClass S.Ω] (ξ : NormFamily S E)
    (hξ : ξ.IsDominated) (hpos : ∀ ω : S.Ω, 0 < S.v {ω})
    (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) (B : Submodule L (L ⊗[K] E)) :
    ((ξ.scalarExtension (L := L)).restrict B).determinant.IsMeasurable := by
  let := AdelicStructure.measurableSingletonClass_algebraicExtension_of_finiteDimensional
    (S := S) (L := L)
  let b := Module.finBasis K E
  have hinf : S.Ωinf = ∅ := by
    ext ω
    exact ⟨fun h ↦ False.elim (h (hS ω)), fun h ↦ False.elim h⟩
  have hfin : S.v S.Ωinf < ⊤ := by rw [hinf, measure_empty]; exact ENNReal.zero_lt_top
  obtain ⟨H, _, _, hc, _, hb, _⟩ :=
    IsDominated.exists_scalarExtension_coordinate_exceptions_of_positive_atoms ξ b hξ hpos hfin
  have ht := AdelicStructure.ParameterSpaceExtension.countable_preimage_proj_of_finiteDimensional
    (L := L) (Function.support H) hc
  let q := ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)
  have hq : q = ofBasis (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L) := by
    ext x z
    exact ofBasisMixed_norm_of_finite (b.baseChange L) x
      (allFinite_nativeDeterminant_scalarExtension hS x) z
  have hm : (q.restrict B).determinant.IsMeasurable := by
    rw [hq]
    exact ofBasis_restrict_determinant_isMeasurable_of_all_finite
      (b.baseChange L) B (allFinite_nativeDeterminant_scalarExtension hS)
  apply determinant_isMeasurable_of_countable_localDist_zero _ _ hm _ ht
  intro x hx
  have hd := ((ξ.scalarExtension (L := L)).localDist_restrict_le q B x).trans (hb L x)
  exact le_antisymm (hd.trans_eq (Function.notMem_support.mp hx))
    (((ξ.scalarExtension (L := L)).restrict B).localDist_nonneg (q.restrict B) x)

/-- The genuine determinant-line dual is measurable by the produced line
regularity, with no regularity hypothesis on the original family. -/
theorem IsDominated.scalarExtension_restrict_determinant_dual_isMeasurable_of_positive_atoms
    [MeasurableSingletonClass S.Ω] (ξ : NormFamily S E)
    (hξ : ξ.IsDominated) (hpos : ∀ ω : S.Ω, 0 < S.v {ω})
    (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) (B : Submodule L (L ⊗[K] E)) :
    ((ξ.scalarExtension (L := L)).restrict B).determinant.dual.IsMeasurable :=
  (IsDominated.scalarExtension_restrict_determinant_isMeasurable_of_positive_atoms
    ξ hξ hpos hS B).dual_of_finrank_one (determinant_finrank (K := L) (E := B))

/-- Every literal native relative quotient has a measurable actual determinant.
The comparison uses the original dominated family on the completed quotient. -/
theorem IsDominated.scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms
    [MeasurableSingletonClass S.Ω] (ξ : NormFamily S E)
    (hξ : ξ.IsDominated) (hpos : ∀ ω : S.Ω, 0 < S.v {ω})
    (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    (((ξ.scalarExtension (L := L)).restrict B).quotient U).determinant.IsMeasurable := by
  let := AdelicStructure.measurableSingletonClass_algebraicExtension_of_finiteDimensional
    (S := S) (L := L)
  let b := Module.finBasis K E
  have hinf : S.Ωinf = ∅ := by
    ext ω
    exact ⟨fun h ↦ False.elim (h (hS ω)), fun h ↦ False.elim h⟩
  have hfin : S.v S.Ωinf < ⊤ := by rw [hinf, measure_empty]; exact ENNReal.zero_lt_top
  obtain ⟨H, _, _, hc, _, hb, _⟩ :=
    IsDominated.exists_scalarExtension_coordinate_exceptions_of_positive_atoms ξ b hξ hpos hfin
  have ht := AdelicStructure.ParameterSpaceExtension.countable_preimage_proj_of_finiteDimensional
    (L := L) (Function.support H) hc
  let q := ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)
  have hq : q = ofBasis (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L) := by
    ext x z
    exact ofBasisMixed_norm_of_finite (b.baseChange L) x
      (allFinite_nativeDeterminant_scalarExtension hS x) z
  have hm : ((q.restrict B).quotient U).determinant.IsMeasurable := by
    rw [hq]
    exact ofBasis_restrict_quotient_determinant_isMeasurable_of_all_finite
      (b.baseChange L) B U (allFinite_nativeDeterminant_scalarExtension hS)
  apply determinant_isMeasurable_of_countable_localDist_zero _ _ hm _ ht
  intro x hx
  have hd := (((ξ.scalarExtension (L := L)).restrict B).localDist_quotient_le
    (q.restrict B) U x).trans
      (((ξ.scalarExtension (L := L)).localDist_restrict_le q B x).trans (hb L x))
  exact le_antisymm (hd.trans_eq (Function.notMem_support.mp hx))
    ((((ξ.scalarExtension (L := L)).restrict B).quotient U).localDist_nonneg
      ((q.restrict B).quotient U) x)

namespace IsDominated

/-- The actual determinant-line dual of every native relative quotient has
produced measurability, with the determinant line still rank one at zero rank. -/
theorem scalarExtension_restrict_quotient_determinant_dual_isMeasurable_of_positive_atoms
    [MeasurableSingletonClass S.Ω] (ξ : NormFamily S E)
    (hξ : ξ.IsDominated) (hpos : ∀ ω : S.Ω, 0 < S.v {ω})
    (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    (((ξ.scalarExtension (L := L)).restrict B).quotient U).determinant.dual.IsMeasurable :=
  (scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms
    ξ hξ hpos hS B U).dual_of_finrank_one
      (determinant_finrank (K := L) (E := B ⧸ U))

end IsDominated

/-- The original dominated-family determinant result applies to the actual
projective-line curve over every constant field. -/
theorem IsDominated.functionField_scalarExtension_restrict_determinant_isMeasurable
    {k L : Type*} [Field k] [Field L] [Algebra (RatFunc k) L]
    [FiniteDimensional (RatFunc k) L] {E : Type*} [AddCommGroup E]
    [Module (RatFunc k) E] [FiniteDimensional (RatFunc k) E]
    (ξ : NormFamily (AdelicStructure.functionFieldAdelicStructure k) E)
    (hξ : ξ.IsDominated) (B : Submodule L (L ⊗[RatFunc k] E)) :
    ((ξ.scalarExtension (L := L)).restrict B).determinant.IsMeasurable := by
  apply IsDominated.scalarExtension_restrict_determinant_isMeasurable_of_positive_atoms
    ξ hξ AdelicStructure.functionField_singleton_pos _ B
  intro ω
  by_contra h
  have hω : ω ∈ (AdelicStructure.functionFieldAdelicStructure k).Ωinf := h
  rw [AdelicStructure.functionField_Ωinf_eq_empty] at hω
  exact hω

/-- The actual determinant dual on geometric finite native subspaces is also
measurable, including the zero native subspace. -/
theorem IsDominated.functionField_scalarExtension_restrict_determinant_dual_isMeasurable
    {k L : Type*} [Field k] [Field L] [Algebra (RatFunc k) L]
    [FiniteDimensional (RatFunc k) L] {E : Type*} [AddCommGroup E]
    [Module (RatFunc k) E] [FiniteDimensional (RatFunc k) E]
    (ξ : NormFamily (AdelicStructure.functionFieldAdelicStructure k) E)
    (hξ : ξ.IsDominated) (B : Submodule L (L ⊗[RatFunc k] E)) :
    ((ξ.scalarExtension (L := L)).restrict B).determinant.dual.IsMeasurable :=
  (IsDominated.functionField_scalarExtension_restrict_determinant_isMeasurable
    ξ hξ B).dual_of_finrank_one (determinant_finrank (K := L) (E := B))

/-- Every literal relative subquotient determinant on the geometric
projective-line curve is measurable over arbitrary constant fields. -/
theorem IsDominated.functionField_scalarExtension_restrict_quotient_determinant_isMeasurable
    {k L : Type*} [Field k] [Field L] [Algebra (RatFunc k) L]
    [FiniteDimensional (RatFunc k) L] {E : Type*} [AddCommGroup E]
    [Module (RatFunc k) E] [FiniteDimensional (RatFunc k) E]
    (ξ : NormFamily (AdelicStructure.functionFieldAdelicStructure k) E)
    (hξ : ξ.IsDominated) (B : Submodule L (L ⊗[RatFunc k] E)) (U : Submodule L B) :
    (((ξ.scalarExtension (L := L)).restrict B).quotient U).determinant.IsMeasurable := by
  apply IsDominated.scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms
    ξ hξ AdelicStructure.functionField_singleton_pos _ B U
  intro ω
  by_contra h
  have hω : ω ∈ (AdelicStructure.functionFieldAdelicStructure k).Ωinf := h
  rw [AdelicStructure.functionField_Ωinf_eq_empty] at hω
  exact hω

/-- Genuine native subquotient determinant duals have measurable rational
profiles by line duality, including equal relative endpoints. -/
theorem IsDominated.functionField_scalarExtension_restrict_quotient_determinant_dual_isMeasurable
    {k L : Type*} [Field k] [Field L] [Algebra (RatFunc k) L]
    [FiniteDimensional (RatFunc k) L] {E : Type*} [AddCommGroup E]
    [Module (RatFunc k) E] [FiniteDimensional (RatFunc k) E]
    (ξ : NormFamily (AdelicStructure.functionFieldAdelicStructure k) E)
    (hξ : ξ.IsDominated) (B : Submodule L (L ⊗[RatFunc k] E)) (U : Submodule L B) :
    (((ξ.scalarExtension (L := L)).restrict B).quotient U).determinant.dual.IsMeasurable :=
  (IsDominated.functionField_scalarExtension_restrict_quotient_determinant_isMeasurable
    ξ hξ B U).dual_of_finrank_one (determinant_finrank (K := L) (E := B ⧸ U))

/-- Every rational logarithmic determinant profile on a native finite relative
quotient is integrable for the actual extension measure. -/
theorem IsDominated.integrable_native_determinant_logNorm_of_positive_atoms
    [MeasurableSingletonClass S.Ω] (ξ : NormFamily S E)
    (hξ : ξ.IsDominated) (hpos : ∀ ω : S.Ω, 0 < S.v {ω})
    (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B)
    (z : ⋀[L]^(Module.finrank L (B ⧸ U)) (B ⧸ U)) :
    Integrable ((((ξ.scalarExtension (L := L)).restrict B).quotient U).determinant.logNorm z)
      (S.algebraicExtension L).v := by
  have hinf : S.Ωinf = ∅ := by
    ext ω
    exact ⟨fun h ↦ False.elim (h (hS ω)), fun h ↦ False.elim h⟩
  have hfin : S.v S.Ωinf < ⊤ := by rw [hinf, measure_empty]; exact ENNReal.zero_lt_top
  have hLN : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion := by
    intro x hx
    exact False.elim (hx (allFinite_nativeDeterminant_scalarExtension hS x))
  have hd := (((hξ.scalarExtension_isStronglyDominated ξ hfin).isDominated.restrict B).quotient U
    ).determinant hLN
  exact hd.integrable_logNorm
    (IsDominated.scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms
      ξ hξ hpos hS B U) z

/-- The actual geometric projective-line native determinant logarithm is
integrable over every finite extension and every relative subquotient. -/
theorem IsDominated.functionField_integrable_native_determinant_logNorm
    {k L : Type*} [Field k] [Field L] [Algebra (RatFunc k) L]
    [FiniteDimensional (RatFunc k) L] {E : Type*} [AddCommGroup E]
    [Module (RatFunc k) E] [FiniteDimensional (RatFunc k) E]
    (ξ : NormFamily (AdelicStructure.functionFieldAdelicStructure k) E)
    (hξ : ξ.IsDominated) (B : Submodule L (L ⊗[RatFunc k] E)) (U : Submodule L B)
    (z : ⋀[L]^(Module.finrank L (B ⧸ U)) (B ⧸ U)) :
    Integrable ((((ξ.scalarExtension (L := L)).restrict B).quotient U).determinant.logNorm z)
      ((AdelicStructure.functionFieldAdelicStructure k).algebraicExtension L).v := by
  apply IsDominated.integrable_native_determinant_logNorm_of_positive_atoms
    ξ hξ AdelicStructure.functionField_singleton_pos _ B U z
  intro ω
  by_contra h
  have hω : ω ∈ (AdelicStructure.functionFieldAdelicStructure k).Ωinf := h
  rw [AdelicStructure.functionField_Ωinf_eq_empty] at hω
  exact hω

end ArakelovGeometry.NormFamily
