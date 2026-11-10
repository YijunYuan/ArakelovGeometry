/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Examples.FunctionFields
public import ArakelovGeometry.AdelicVectorBundle.Determinant.Basic
public import ArakelovGeometry.AdelicVectorBundle.Measurability.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic
import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicVectorBundle.Determinant.Comparison
import ArakelovGeometry.AdelicVectorBundle.Exterior.Domination
import ArakelovGeometry.AdelicVectorBundle.Measurability.Coordinates.Determinant
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Line
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Domination.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.AtomicNormComparison
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.ScalarExtensionExceptions
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.ScalarExtensionMeasurable

/-!
# Actual native determinant regularity after finite geometric extension

Determinant distance vanishes wherever the original families agree. The
produced countable exceptional set transfers actual coordinate determinant
measurability to native subspaces of original dominated scalar extensions.
-/

@[expose] public section

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
  have hfin := AdelicStructure.v_Ωinf_lt_top_of_forall_mem_Ωfin hS
  obtain ⟨H, _, _, hc, _, hb, _⟩ :=
    IsDominated.exists_scalarExtension_coordinate_exceptions_of_positive_atoms ξ b hξ hpos hfin
  have ht := AdelicStructure.ParameterSpaceExtension.countable_preimage_proj_of_finiteDimensional
    (L := L) (Function.support H) hc
  let q := ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)
  have hq : q = ofBasis (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L) := by
    ext x z
    exact ofBasisMixed_norm_of_finite (b.baseChange L) x
      (AdelicStructure.forall_mem_Ωfin_algebraicExtension hS x) z
  have hm : (q.restrict B).determinant.IsMeasurable := by
    rw [hq]
    exact ofBasis_restrict_determinant_isMeasurable_of_all_finite
      (b.baseChange L) B (AdelicStructure.forall_mem_Ωfin_algebraicExtension hS)
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
  have hfin := AdelicStructure.v_Ωinf_lt_top_of_forall_mem_Ωfin hS
  obtain ⟨H, _, _, hc, _, hb, _⟩ :=
    IsDominated.exists_scalarExtension_coordinate_exceptions_of_positive_atoms ξ b hξ hpos hfin
  have ht := AdelicStructure.ParameterSpaceExtension.countable_preimage_proj_of_finiteDimensional
    (L := L) (Function.support H) hc
  let q := ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)
  have hq : q = ofBasis (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L) := by
    ext x z
    exact ofBasisMixed_norm_of_finite (b.baseChange L) x
      (AdelicStructure.forall_mem_Ωfin_algebraicExtension hS x) z
  have hm : ((q.restrict B).quotient U).determinant.IsMeasurable := by
    rw [hq]
    exact ofBasis_restrict_quotient_determinant_isMeasurable_of_all_finite
      (b.baseChange L) B U (AdelicStructure.forall_mem_Ωfin_algebraicExtension hS)
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
  have hfin := AdelicStructure.v_Ωinf_lt_top_of_forall_mem_Ωfin hS
  have hLN : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion := by
    intro x hx
    exact False.elim (hx (AdelicStructure.forall_mem_Ωfin_algebraicExtension hS x))
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
