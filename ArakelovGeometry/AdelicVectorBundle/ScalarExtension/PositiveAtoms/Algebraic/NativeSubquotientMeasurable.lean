/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Measurability.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic
import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicVectorBundle.Degree.Determinant.Isometry
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Domination.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.NativeSubquotientFiniteStage
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.Algebraic.ScalarExtensionMeasurable
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.FinitePositiveAtoms
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.ScalarExtensionMeasurable

/-!
# Actual geometric native subquotient regularity

Produced finite stages and their genuine positive atoms supply full primal and
completed-dual measurability on every native relative quotient over an algebraic
closure. No original measurability, ultrametricity or countability is required.
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

/-- Full primal measurability of every actual native algebraic-closure
subquotient, from finite-stage descent and original domination alone. -/
theorem scalarExtension_subquotient_isMeasurable_of_positive_atoms_of_isAlgClosed
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (P Q : Submodule L (L ⊗[K] E)) (hPQ : P ≤ Q) :
    (((ξ.scalarExtension (L := L)).restrict Q).quotient
      (P.comap Q.subtype)).IsMeasurable := by
  obtain ⟨F, _, P₀, Q₀, _, _, _, e, he, _⟩ :=
    ξ.exists_complexFiniteStage_subquotient_isometry
      (AdelicStructure.isRCLikeNormedField_of_forall_mem_Ωfin hS) P Q hPQ
  let η₀ := ((ξ.scalarExtension (L := F)).restrict Q₀).quotient (P₀.comap Q₀.subtype)
  let η := η₀.scalarExtension (L := L)
  let θ := ((ξ.scalarExtension (L := L)).restrict Q).quotient (P.comap Q.subtype)
  let : MeasurableSingletonClass (S.algebraicExtension F).Ω :=
    AdelicStructure.measurableSingletonClass_algebraicExtension_of_finiteDimensional
      (S := S) (L := F)
  have hFpos (x : (S.algebraicExtension F).Ω) :
      0 < (S.algebraicExtension F).v {x} :=
    AdelicStructure.Algebraic.singleton_pos_algebraicExtension_of_finiteDimensional S hpos x
  have hFS (x : (S.algebraicExtension F).Ω) : x ∈ (S.algebraicExtension F).Ωfin :=
    (AdelicStructure.mem_Ωfin_algebraicExtension_iff x).mpr (hS x.base)
  have hd₀ : η₀.IsDominated :=
    ((hξ.scalarExtension_isStronglyDominated ξ
      (AdelicStructure.v_Ωinf_lt_top_of_forall_mem_Ωfin hS)).isDominated.restrict Q₀
      ).quotient (P₀.comap Q₀.subtype)
  have hm : η.IsMeasurable :=
    hd₀.scalarExtension_isMeasurable_of_positive_atoms_of_isAlgebraic η₀ hFpos hFS
  have ht : (θ.towerPullback F.toIntermediateField).IsMeasurable :=
    hm.of_completed_isometry η (θ.towerPullback F.toIntermediateField) e he
  exact (θ.isMeasurable_towerPullback_iff F.toIntermediateField).mp ht

/-- Full actual completed-dual measurability of every native subquotient;
the transpose of the produced isometry is used on actual rational functionals. -/
theorem scalarExtension_subquotient_dual_isMeasurable_of_positive_atoms_of_isAlgClosed
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (P Q : Submodule L (L ⊗[K] E)) (hPQ : P ≤ Q) :
    (((ξ.scalarExtension (L := L)).restrict Q).quotient
      (P.comap Q.subtype)).dual.IsMeasurable := by
  obtain ⟨F, _, P₀, Q₀, _, _, _, e, he, _⟩ :=
    ξ.exists_complexFiniteStage_subquotient_isometry
      (AdelicStructure.isRCLikeNormedField_of_forall_mem_Ωfin hS) P Q hPQ
  let η₀ := ((ξ.scalarExtension (L := F)).restrict Q₀).quotient (P₀.comap Q₀.subtype)
  let η := η₀.scalarExtension (L := L)
  let θ := ((ξ.scalarExtension (L := L)).restrict Q).quotient (P.comap Q.subtype)
  let : MeasurableSingletonClass (S.algebraicExtension F).Ω :=
    AdelicStructure.measurableSingletonClass_algebraicExtension_of_finiteDimensional
      (S := S) (L := F)
  have hFpos (x : (S.algebraicExtension F).Ω) :
      0 < (S.algebraicExtension F).v {x} :=
    AdelicStructure.Algebraic.singleton_pos_algebraicExtension_of_finiteDimensional S hpos x
  have hFS (x : (S.algebraicExtension F).Ω) : x ∈ (S.algebraicExtension F).Ωfin :=
    (AdelicStructure.mem_Ωfin_algebraicExtension_iff x).mpr (hS x.base)
  have hd₀ : η₀.IsDominated :=
    ((hξ.scalarExtension_isStronglyDominated ξ
      (AdelicStructure.v_Ωinf_lt_top_of_forall_mem_Ωfin hS)).isDominated.restrict Q₀
      ).quotient (P₀.comap Q₀.subtype)
  have hm : η.dual.IsMeasurable :=
    hd₀.scalarExtension_dual_isMeasurable_of_positive_atoms_of_isAlgebraic η₀ hFpos hFS
  exact IsMeasurable.dual_of_tower_completed_isometry F η θ e he hm

/-- Literal relative quotients have actual primal regularity. -/
theorem scalarExtension_restrict_quotient_isMeasurable_of_positive_atoms_of_isAlgClosed
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    (((ξ.scalarExtension (L := L)).restrict B).quotient U).IsMeasurable := by
  let P := U.map B.subtype
  have hP : P ≤ B := B.map_subtype_le U
  have hU : P.comap B.subtype = U := by
    change (U.map B.subtype).comap B.subtype = U
    rw [Submodule.comap_map_eq, Submodule.ker_subtype, sup_bot_eq]
  have hm := scalarExtension_subquotient_isMeasurable_of_positive_atoms_of_isAlgClosed
    ξ hξ hpos hS P B hP
  exact Eq.mp (congrArg (fun C : Submodule L B =>
    (((ξ.scalarExtension (L := L)).restrict B).quotient C).IsMeasurable) hU) hm

/-- Literal relative quotients have actual completed-dual regularity. -/
theorem scalarExtension_restrict_quotient_dual_isMeasurable_of_positive_atoms_of_isAlgClosed
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    (((ξ.scalarExtension (L := L)).restrict B).quotient U).dual.IsMeasurable := by
  let P := U.map B.subtype
  have hP : P ≤ B := B.map_subtype_le U
  have hU : P.comap B.subtype = U := by
    change (U.map B.subtype).comap B.subtype = U
    rw [Submodule.comap_map_eq, Submodule.ker_subtype, sup_bot_eq]
  have hm := scalarExtension_subquotient_dual_isMeasurable_of_positive_atoms_of_isAlgClosed
    ξ hξ hpos hS P B hP
  exact Eq.mp (congrArg (fun C : Submodule L B =>
    (((ξ.scalarExtension (L := L)).restrict B).quotient C).dual.IsMeasurable) hU) hm

end IsDominated
end ArakelovGeometry.NormFamily
