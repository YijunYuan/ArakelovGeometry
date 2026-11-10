/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.GeometricAlgebraicNativeDeterminant
import ArakelovGeometry.AdelicVectorBundle.GeometricAlgebraicScalarExtensionMeasurable
import ArakelovGeometry.AdelicVectorBundle.GeometricFinitePositiveAtoms
import ArakelovGeometry.AdelicVectorBundle.DegreeIsometryDual

/-!
# Actual geometric native subquotient regularity

Produced finite stages and their genuine positive atoms supply full primal and
completed-dual measurability on every native relative quotient over an algebraic
closure. No original measurability, ultrametricity or countability is required.
-/

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.NormFamily

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [MeasurableSingletonClass S.Ω]

omit [MeasurableSingletonClass S.Ω] in
private theorem nativeRegularity_allFinite_normalization
    (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion := by
  intro ω hω
  exact False.elim (hω (hS ω))

omit [MeasurableSingletonClass S.Ω] in
private theorem nativeRegularity_infinity_measure_lt_top
    (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) : S.v S.Ωinf < ⊤ := by
  have hinf : S.Ωinf = ∅ := by
    ext ω
    exact ⟨fun h => False.elim (h (hS ω)), fun h => False.elim h⟩
  rw [hinf, measure_empty]
  exact ENNReal.zero_lt_top

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
      (nativeRegularity_allFinite_normalization hS) P Q hPQ
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
    (scalarExtension_mem_Ωfin_iff x).mpr (hS x.base)
  have hd₀ : η₀.IsDominated :=
    ((hξ.scalarExtension_isStronglyDominated ξ
      (nativeRegularity_infinity_measure_lt_top hS)).isDominated.restrict Q₀
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
      (nativeRegularity_allFinite_normalization hS) P Q hPQ
  let η₀ := ((ξ.scalarExtension (L := F)).restrict Q₀).quotient (P₀.comap Q₀.subtype)
  let η := η₀.scalarExtension (L := L)
  let θ := ((ξ.scalarExtension (L := L)).restrict Q).quotient (P.comap Q.subtype)
  let θt := θ.towerPullback F.toIntermediateField
  let : MeasurableSingletonClass (S.algebraicExtension F).Ω :=
    AdelicStructure.measurableSingletonClass_algebraicExtension_of_finiteDimensional
      (S := S) (L := F)
  have hFpos (x : (S.algebraicExtension F).Ω) :
      0 < (S.algebraicExtension F).v {x} :=
    AdelicStructure.Algebraic.singleton_pos_algebraicExtension_of_finiteDimensional S hpos x
  have hFS (x : (S.algebraicExtension F).Ω) : x ∈ (S.algebraicExtension F).Ωfin :=
    (scalarExtension_mem_Ωfin_iff x).mpr (hS x.base)
  have hd₀ : η₀.IsDominated :=
    ((hξ.scalarExtension_isStronglyDominated ξ
      (nativeRegularity_infinity_measure_lt_top hS)).isDominated.restrict Q₀
      ).quotient (P₀.comap Q₀.subtype)
  have hm : η.dual.IsMeasurable :=
    hd₀.scalarExtension_dual_isMeasurable_of_positive_atoms_of_isAlgebraic η₀ hFpos hFS
  have ht : θt.dual.IsMeasurable := by
    intro ℓ
    have hn (x : ((S.algebraicExtension F).algebraicExtension L).Ω) :
        θt.dual.norm x ((1 : (((S.algebraicExtension F).algebraicExtension L).ϕ x).Completion)
          ⊗ₜ[L] ℓ) =
        η.dual.norm x ((1 : (((S.algebraicExtension F).algebraicExtension L).ϕ x).Completion)
          ⊗ₜ[L] e.dualMap ℓ) := by
      symm
      simpa only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe] using
        η.dualEquiv_norm_eq_of_completed_isometry θt x e (he x)
          ((1 : (((S.algebraicExtension F).algebraicExtension L).ϕ x).Completion) ⊗ₜ[L] ℓ)
    change Measurable (fun x : ((S.algebraicExtension F).algebraicExtension L).Ω =>
      θt.dual.norm x
        ((1 : (((S.algebraicExtension F).algebraicExtension L).ϕ x).Completion) ⊗ₜ[L] ℓ))
    rw [funext hn]
    exact hm (e.dualMap ℓ)
  change (θ.towerPullback F.toIntermediateField).dual.IsMeasurable at ht
  rw [towerPullback_dual] at ht
  exact (θ.dual.isMeasurable_towerPullback_iff F.toIntermediateField).mp ht

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
