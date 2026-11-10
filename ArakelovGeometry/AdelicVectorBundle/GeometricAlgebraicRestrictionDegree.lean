/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.AbsoluteInvariantsDiscrete
public import ArakelovGeometry.AdelicVectorBundle.GeometricAlgebraicNativeDeterminant
public import ArakelovGeometry.AdelicVectorBundle.GeometricAlgebraicRestriction

/-!
# Canonical geometric native restriction degrees

Actual finite-stage restriction isometries produce determinant measurability
on every native subspace. The resulting canonical degrees have a single
produced rank-multiple upper bound on all native subspaces. The bundle is on
the subspace itself, and no extension-place regularity is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [MeasurableSingletonClass S.Ω]

namespace NormFamily

omit [MeasurableSingletonClass S.Ω] in
/-- An all-finite adelic structure satisfies archimedean normalization vacuously. -/
theorem geometricRestrictionDegree_normalization
    (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion := by
  intro ω hω
  exact False.elim (hω (hS ω))

namespace IsDominated

/-- Finite descent produces the actual restricted determinant measurability,
without passing to a quotient-space proxy. -/
theorem scalarExtension_restrict_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (A : Submodule L (L ⊗[K] E)) :
    ((ξ.scalarExtension (L := L)).restrict A).determinant.IsMeasurable := by
  obtain ⟨F, _, B, _, _, he⟩ := ξ.exists_complexFiniteStage_restriction_isometries
    (geometricRestrictionDegree_normalization hS) (fun _ : Fin 1 => A)
  obtain ⟨e, he⟩ := he 0
  let η₀ := (ξ.scalarExtension (L := F)).restrict (B 0)
  let η := η₀.scalarExtension (L := L)
  let θ := (ξ.scalarExtension (L := L)).restrict A
  have hm₀ : η₀.determinant.IsMeasurable :=
    hξ.scalarExtension_restrict_determinant_isMeasurable_of_positive_atoms ξ hpos hS (B 0)
  have hm : η.determinant.IsMeasurable := hm₀.determinant_scalarExtension
  have ht : (θ.towerPullback F.toIntermediateField).determinant.IsMeasurable :=
    η.determinant_isMeasurable_of_completed_isometry
      (θ.towerPullback F.toIntermediateField) e he hm
  rw [towerPullback_determinant] at ht
  exact (θ.determinant.isMeasurable_towerPullback_iff F.toIntermediateField).mp ht

end IsDominated

variable [S.IsProper]

/-- The canonical measurable-determinant degree of the actual native
restriction bundle on the literal subspace. -/
def nativeAlgebraicRestrictionDegreeOfPositiveAtoms (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (A : Submodule L (L ⊗[K] E)) : ℝ :=
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  (ξ.nativeAlgebraicRestrictionOfPositiveAtoms hξ hpos hS A).degreeOfMeasurableDeterminant
    (hξ.scalarExtension_restrict_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
      ξ hpos hS A)
    (AdelicStructure.isRCLikeNormedField_algebraicExtension
      (L := L) (geometricRestrictionDegree_normalization hS))

/-- Every nonzero actual determinant generator computes the native degree. -/
theorem nativeAlgebraicRestrictionDegreeOfPositiveAtoms_eq_neg_integral
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (A : Submodule L (L ⊗[K] E))
    (t : ⋀[L]^(Module.finrank L A) A) (ht : t ≠ 0) :
    ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms hξ hpos hS A =
      -∫ x, ((ξ.scalarExtension (L := L)).restrict A).determinant.logNorm t x
        ∂(S.algebraicExtension L).v := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  exact AdelicVectorBundle.degreeOfMeasurableDeterminant_eq_neg_integral _ _ _ ⟨t, ht⟩

/-- The actual empty determinant has norm one, giving zero native degree. -/
theorem nativeAlgebraicRestrictionDegreeOfPositiveAtoms_eq_zero_of_finrank_eq_zero
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (A : Submodule L (L ⊗[K] E)) (hr : Module.finrank L A = 0) :
    ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms hξ hpos hS A = 0 := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let W := ξ.nativeAlgebraicRestrictionOfPositiveAtoms hξ hpos hS A
  let hdet :=
    hξ.scalarExtension_restrict_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
      ξ hpos hS A
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension
    (L := L) (geometricRestrictionDegree_normalization hS)
  change (W.determinant hdet hLN).lineDegree (W.determinant_isLine hdet hLN) = 0
  apply AdelicVectorBundle.lineDegree_eq_zero_of_norm_eq_one _ _
    ⟨_, AdelicVectorBundle.determinant_empty_ne_zero hr⟩
  intro x
  change W.toNormFamily.determinant.norm x _ = 1
  simpa only [norm_one] using W.toNormFamily.determinant_norm_empty_tmul hr x 1 (fun _ => 0)

/-- One produced integral envelope bounds the actual determinant degree of
every native subspace, with no extension-place regularity premise. -/
theorem exists_nativeAlgebraicRestrictionDegreeOfPositiveAtoms_le_rank_mul
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    ∃ C : ℝ, ∀ A : Submodule L (L ⊗[K] E),
      ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms hξ hpos hS A ≤
        (Module.finrank L A : ℝ) * C := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let V := ξ.algebraicScalarBundleOfPositiveAtoms (L := L) hξ hpos hS
  let b := Module.finBasis L (L ⊗[K] E)
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension
    (L := L) (geometricRestrictionDegree_normalization hS)
  obtain ⟨H, hH, _, hb⟩ :=
    IsDominated.exists_restricted_dual_basis_norm_bound V.toNormFamily b V.isDominated
  refine ⟨∫ x, H x ∂(S.algebraicExtension L).v, fun A => ?_⟩
  let W := ξ.nativeAlgebraicRestrictionOfPositiveAtoms hξ hpos hS A
  let hdet :=
    hξ.scalarExtension_restrict_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
      ξ hpos hS A
  let t := determinantGenerator (K := L) (E := A)
  have ht : t ≠ 0 := determinantGenerator_ne_zero
  obtain ⟨s, hs⟩ := exists_restrictedCoordinateDualWedge_pairing_ne_zero b A t ht
  let α := determinantDualEquiv L A (restrictedCoordinateDualWedge b A s) t
  have hα : α ≠ 0 := hs
  have hf : Integrable (W.toNormFamily.determinant.logNorm t) (S.algebraicExtension L).v :=
    (W.determinant hdet hLN).integrable_logNorm t
  have hlocal : ∀ᵐ x ∂(S.algebraicExtension L).v,
      Real.log ((S.algebraicExtension L).ϕ x α) ≤
        W.toNormFamily.determinant.logNorm t x + (Module.finrank L A : ℝ) * H x := by
    filter_upwards [hb] with x hx
    have hinf : x ∉ (S.algebraicExtension L).Ωinf := by
      intro hi
      exact hi ((scalarExtension_mem_Ωfin_iff x).mpr (hS x.base))
    simpa only [Set.indicator_of_notMem hinf, add_zero, α, V, W,
      nativeAlgebraicRestrictionOfPositiveAtoms_toNormFamily,
      algebraicScalarBundleOfPositiveAtoms_toNormFamily] using
      log_absValue_coordinate_le_logNorm_restrict_determinant
        V.toNormFamily b A s t ht hs hLN x (H x) (hx A)
  have hi := integral_mono_ae ((S.algebraicExtension L).integrable_log α hα)
    (hf.add (hH.const_mul (Module.finrank L A : ℝ))) hlocal
  simp only [Pi.add_apply] at hi
  rw [integral_add hf (hH.const_mul (Module.finrank L A : ℝ)), integral_const_mul,
    AdelicStructure.IsProper.product_formula α hα] at hi
  rw [ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms_eq_neg_integral
    hξ hpos hS A t ht]
  change -(∫ x, W.toNormFamily.determinant.logNorm t x ∂(S.algebraicExtension L).v) ≤
    (Module.finrank L A : ℝ) * (∫ x, H x ∂(S.algebraicExtension L).v)
  change 0 ≤ (∫ x, W.toNormFamily.determinant.logNorm t x ∂(S.algebraicExtension L).v) +
    (Module.finrank L A : ℝ) * (∫ x, H x ∂(S.algebraicExtension L).v) at hi
  linarith

end NormFamily
namespace AdelicVectorBundle

variable [S.IsProper]

/-- Native geometric and common-density degrees agree on the same actual subspace. -/
theorem nativeAlgebraicRestrictionDegreeOfPositiveAtoms_eq_common_degree
    (V : AdelicVectorBundle S E)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule L (L ⊗[K] E)) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    V.toNormFamily.nativeAlgebraicRestrictionDegreeOfPositiveAtoms V.isDominated hpos hS A =
      ((V.scalarExtension (L := L) hcount hN).restrictOfMeasurableBase A
        (Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))).degree
        (Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))
        (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) := rfl

/-- The geometric and countable-discrete canonical degrees have identical actual norms. -/
theorem nativeAlgebraicRestrictionDegreeOfPositiveAtoms_eq_countable_discrete_degree
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]
    (V : AdelicVectorBundle S E)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule L (L ⊗[K] E)) :
    V.toNormFamily.nativeAlgebraicRestrictionDegreeOfPositiveAtoms V.isDominated hpos hS A =
      V.nativeRestrictionDegreeOfCountableDiscreteBase hN A := rfl

end AdelicVectorBundle
end ArakelovGeometry
