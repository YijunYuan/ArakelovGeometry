/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.InvariantTheory.Binary.Instability
public import ArakelovGeometry.InvariantTheory.Binary.TensorTransport
public import ArakelovGeometry.LinearAlgebra.Filtration.Equiv

/-!
# Actual original-field negative filtrations from binary geometric instability

For the unstable case on Bost page 31, geometric nonsemistability of the same
scalar-extended quotient yields centered finite left-continuous real filtrations
over the original characteristic-zero field, with negative actual quotient
expectation and total energy one. The algebraic closure may have infinite
degree. Galois stability is obtained from uniqueness of the optimizer by the
existing rationality theorem; neither stability nor a negative candidate is an
input. This one-way binary implication supplies A9's optimizer input. The
subsequent adelic degree inequality and Bost rank induction are separate.
-/

@[expose] public section

open scoped TensorProduct
open Module ArakelovGeometry ArakelovGeometry.InvariantTheory

noncomputable section

namespace Submodule

universe u wE wV

variable {K : Type u} {E : Type wE} {V : Type wV} {Q : Type*} [Field K] [CharZero K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E] [Nontrivial E]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q] [Nontrivial Q]

/-- The Bost page 31 binary instability implication over the original characteristic-zero
field. The hypothesis is the actual A2 geometric predicate on the Bool tensor presentation
of this same ordinary binary quotient. The conclusion consists of actual centered finite
left-continuous real filtrations, normalized to total energy one, with negative actual
quotient expectation. The algebraic closure need not be finite over `K`; Galois stability
is derived from uniqueness of the optimizer inside the existing rationality theorem.
This supplies the A9 negative-pair input, not the subsequent adelic degree inequality or
Bost rank induction. -/
theorem exists_centered_negative_tensor_filtrations_of_not_geometricallySemistable
    (q : E ⊗[K] V →ₗ[K] Q) (hq : Function.Surjective q) (hQ : 0 < finrank K Q)
    (hns : ¬ IsGeometricallySemistableTensorQuotient (LiftedBoolTensorFactors E V)
      (q.comp (boolTensorPairEquiv K E V).toLinearMap)) :
    ∃ (P : ℝ → Submodule K E) (R : ℝ → Submodule K V),
      (Antitone P ∧ (∃ t, P t = ⊥) ∧ (∃ t, P t = ⊤) ∧
        (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → P s = P t) ∧
        filtrationExpectation P = 0) ∧
      (Antitone R ∧ (∃ t, R t = ⊥) ∧ (∃ t, R t = ⊤) ∧
        (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → R s = R t) ∧
        filtrationExpectation R = 0) ∧
      filtrationPairing P P + filtrationPairing R R = 1 ∧
      filtrationExpectation (fun t ↦ (tensorFiltration P R t).map q) < 0 := by
  let e : ULift.{wV} E ≃ₗ[K] E := ULift.moduleEquiv
  let d : ULift.{wE} V ≃ₗ[K] V := ULift.moduleEquiv
  let A := LiftedBoolTensorFactors E V
  let qL := q.comp (TensorProduct.congr e d).toLinearMap
  have hqL : Function.Surjective qL := hq.comp (TensorProduct.congr e d).surjective
  let q' := qL.comp (boolTensorEquiv K A).toLinearMap
  have hq' : Function.Surjective q' := hqL.comp (boolTensorEquiv K A).surjective
  obtain ⟨F, hF, hneg⟩ :=
    exists_binary_negative_filtrations_of_not_isQuotientSemistable
      (piTensorQuotientBaseChange (L := AlgebraicClosure K) q')
      (piTensorQuotientBaseChange_surjective q' hq')
      (by simpa only [Module.finrank_baseChange] using hQ) hns
  have hnegL : filtrationExpectation
      (fun t ↦ (tensorFiltration (F false) (F true) t).map
        (tensorQuotientBaseChange (L := AlgebraicClosure K) qL)) < 0 :=
    (congrArg filtrationExpectation
      (funext (piTensor_image_bool_baseChange (E := A) qL F))).symm.trans_lt hneg
  obtain ⟨P, R, hP, hR, hunit, hnegP⟩ :=
    exists_centered_negative_tensor_filtrations_of_baseChange qL hqL hQ
      (F false) (F true) (hF false) (hF true) hnegL
  refine ⟨fun t ↦ (P t).map e.toLinearMap, fun t ↦ (R t).map d.toLinearMap,
    centered_filtration_map_equiv e P hP, centered_filtration_map_equiv d R hR, ?_, ?_⟩
  · simpa only [filtrationPairing_map_equiv] using hunit
  · have heq : (fun t ↦ (tensorFiltration P R t).map qL) =
        (fun t ↦ (tensorFiltration (fun s ↦ (P s).map e.toLinearMap)
          (fun s ↦ (R s).map d.toLinearMap) t).map q) := by
      funext t
      change (tensorFiltration P R t).map
        (q.comp (TensorProduct.map e.toLinearMap d.toLinearMap)) = _
      rw [map_comp, tensorFiltration_map]
    exact (congrArg filtrationExpectation heq).symm.trans_lt hnegP

end Submodule
