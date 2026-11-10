/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Determinant.Basic
public import ArakelovGeometry.AdelicVectorBundle.Measurability.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic
import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicVectorBundle.Degree.Determinant.Isometry
import ArakelovGeometry.AdelicVectorBundle.Exterior.Domination
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Line
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Domination.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.NativeSubquotientFiniteStage
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.NativeDeterminantMeasurable

/-!
# Native geometric determinant regularity over an algebraic closure

A produced finite-stage completed isometry carries the accepted finite native
determinant regularity to every native relative quotient over an algebraic
closure. The original field and place space need not be countable.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.NormFamily

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [MeasurableSingletonClass S.Ω]

namespace IsDominated

/-- Finite-stage descent produces actual native determinant measurability
on every algebraic closure of an all-finite positive atomic curve. -/
theorem scalarExtension_subquotient_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (P Q : Submodule L (L ⊗[K] E)) (hPQ : P ≤ Q) :
    (((ξ.scalarExtension (L := L)).restrict Q).quotient
      (P.comap Q.subtype)).determinant.IsMeasurable := by
  obtain ⟨F, _, P₀, Q₀, _, _, _, e, he, _⟩ :=
    ξ.exists_complexFiniteStage_subquotient_isometry
      (AdelicStructure.isRCLikeNormedField_of_forall_mem_Ωfin hS) P Q hPQ
  let η₀ := ((ξ.scalarExtension (L := F)).restrict Q₀).quotient (P₀.comap Q₀.subtype)
  let η := η₀.scalarExtension (L := L)
  let θ := ((ξ.scalarExtension (L := L)).restrict Q).quotient (P.comap Q.subtype)
  have hm₀ : η₀.determinant.IsMeasurable :=
    scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms
      ξ hξ hpos hS Q₀ (P₀.comap Q₀.subtype)
  have hm : η.determinant.IsMeasurable := hm₀.determinant_scalarExtension
  have ht : (θ.towerPullback F.toIntermediateField).determinant.IsMeasurable :=
    η.determinant_isMeasurable_of_completed_isometry
      (θ.towerPullback F.toIntermediateField) e he hm
  rw [towerPullback_determinant] at ht
  exact (θ.determinant.isMeasurable_towerPullback_iff F.toIntermediateField).mp ht

/-- Every literal relative quotient is covered by its ambient subspace image. -/
theorem scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    (((ξ.scalarExtension (L := L)).restrict B).quotient U).determinant.IsMeasurable := by
  let P := U.map B.subtype
  have hP : P ≤ B := B.map_subtype_le U
  have hU : P.comap B.subtype = U := by
    change (U.map B.subtype).comap B.subtype = U
    rw [Submodule.comap_map_eq, Submodule.ker_subtype, sup_bot_eq]
  have hm := scalarExtension_subquotient_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
    ξ hξ hpos hS P B hP
  exact Eq.mp (congrArg (fun C : Submodule L B =>
    (((ξ.scalarExtension (L := L)).restrict B).quotient C).determinant.IsMeasurable) hU) hm

/-- The genuine completed determinant dual is measurable, including rank zero. -/
theorem
    scalarExtension_restrict_quotient_determinant_dual_isMeasurable_of_positive_atoms_of_isAlgClosed
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    (((ξ.scalarExtension (L := L)).restrict B).quotient U).determinant.dual.IsMeasurable :=
  (scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
    ξ hξ hpos hS B U).dual_of_finrank_one
      (determinant_finrank (K := L) (E := B ⧸ U))

/-- Produced actual determinant regularity combines with dominated operations
for integrability of every rational determinant logarithm. -/
theorem integrable_native_determinant_logNorm_of_positive_atoms_of_isAlgClosed
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B)
    (z : ⋀[L]^(Module.finrank L (B ⧸ U)) (B ⧸ U)) :
    Integrable ((((ξ.scalarExtension (L := L)).restrict B).quotient U).determinant.logNorm z)
      (S.algebraicExtension L).v := by
  have hd := (((hξ.scalarExtension_isStronglyDominated ξ
    (AdelicStructure.v_Ωinf_lt_top_of_forall_mem_Ωfin hS)).isDominated.restrict B).quotient U
    ).determinant (AdelicStructure.isRCLikeNormedField_algebraicExtension_of_forall_mem_Ωfin hS)
  exact hd.integrable_logNorm
    (scalarExtension_restrict_quotient_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
      ξ hξ hpos hS B U) z

end IsDominated
end ArakelovGeometry.NormFamily
