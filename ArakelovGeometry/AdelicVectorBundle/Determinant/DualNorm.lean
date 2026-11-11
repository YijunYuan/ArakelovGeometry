/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Determinant.DualBaseChange
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Hermitian.Basic

import ArakelovGeometry.AdelicVectorBundle.Tensor.Hermitian.InnerProduct
import ArakelovGeometry.Analysis.Determinant.Pairing
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Duality of completed determinant norms

The determinant pairing is transported along the canonical completed dual and
exterior maps. All norm comparisons use the actual determinant quotient norms.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

variable (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L]
  (E : Type*) [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The actual completed pairing of the determinant of the dual with the
determinant of the original space. -/
def completedDeterminantPairing :
    (L ⊗[K] (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E))) →ₗ[L]
      Module.Dual L (L ⊗[K] (⋀[K]^(Module.finrank K E) E)) :=
  (dualBaseChangeEquiv K L (⋀[K]^(Module.finrank K E) E)).toLinearMap ∘ₗ
    (determinantDualEquiv K E).toLinearMap.baseChange L

/-- On completed wedges the canonical pairing is the matrix of evaluations,
with the canonical equality of the two ranks made explicit. -/
theorem completedDeterminantPairing_ιMulti
    (f : Fin (Module.finrank K (Module.Dual K E)) → L ⊗[K] Module.Dual K E)
    (x : Fin (Module.finrank K E) → L ⊗[K] E) :
    completedDeterminantPairing K L E
        ((exteriorBaseChangeEquiv K L (Module.Dual K E) _).symm
          (_root_.exteriorPower.ιMulti L _ f))
        ((exteriorBaseChangeEquiv K L E _).symm
          (_root_.exteriorPower.ιMulti L _ x)) =
      (Matrix.of fun i j ↦ dualBaseChangeEquiv K L E
        (f ((finCongr Subspace.dual_finrank_eq).symm j)) (x i)).det := by
  simp only [completedDeterminantPairing, determinantDualEquiv,
    LinearEquiv.coe_trans, LinearMap.baseChange_comp, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  change dualBaseChangeEquiv K L (⋀[K]^(Module.finrank K E) E)
    ((_root_.exteriorPower.pairingDual K E (Module.finrank K E)).baseChange L
      (((exteriorPowerDegreeEquiv K (Module.Dual K E)
        Subspace.dual_finrank_eq).toLinearMap).baseChange L
          ((exteriorBaseChangeEquiv K L (Module.Dual K E) _).symm
            (_root_.exteriorPower.ιMulti L _ f)))) _ = _
  rw [exteriorPairingDual_baseChange, exteriorBaseChangeEquiv_degreeEquiv]
  simp only [LinearEquiv.apply_symm_apply, exteriorPowerDegreeEquiv_ιMulti,
    _root_.exteriorPower.map_apply_ιMulti, _root_.exteriorPower.pairingDual_ιMulti_ιMulti,
    Function.comp_apply, LinearEquiv.coe_coe]

namespace NormFamily

variable {K E} {S : AdelicStructure K} (ξ : NormFamily S E)
  {hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}

omit [Field L] [Algebra K L] in
/-- The actual completed determinant pairing has the product bound on pure
wedges of a Hermitian norm family. -/
theorem IsHermitian.norm_completedDeterminantPairing_ιMulti_le
    (hξ : ξ.IsHermitian hS) (ω : S.Ω)
    (f : Fin (Module.finrank K (Module.Dual K E)) →
      (S.ϕ ω).Completion ⊗[K] Module.Dual K E)
    (x : Fin (Module.finrank K E) → (S.ϕ ω).Completion ⊗[K] E) :
    ‖completedDeterminantPairing K (S.ϕ ω).Completion E
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion (Module.Dual K E) _).symm
          (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ f))
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm
          (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ x))‖ ≤
      (∏ i, ξ.norm ω (x i)) * ∏ i, ξ.dual.norm ω (f i) := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let g (i : Fin (Module.finrank K E)) := dualBaseChangeEquiv K (S.ϕ ω).Completion E
    (f ((finCongr Subspace.dual_finrank_eq).symm i))
  have hg : (∏ i, linearMapOperatorSeminorm (g i)) =
      ∏ i, ξ.dual.norm ω (f i) := by
    change (∏ i, ξ.dual.norm ω (f ((finCongr Subspace.dual_finrank_eq).symm i))) = _
    exact Equiv.prod_comp (finCongr (Subspace.dual_finrank_eq (K := K) (V := E))).symm
      (fun i ↦ ξ.dual.norm ω (f i))
  rw [completedDeterminantPairing_ιMulti]
  change ‖(Matrix.of fun i j ↦ g j (x i)).det‖ ≤ _
  by_cases hω : ω ∈ S.Ωfin
  · have hL (a b : (S.ϕ ω).Completion) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
      refine UniformSpace.Completion.induction_on₂ a b ?_ ?_
      · exact isClosed_le (by fun_prop) (by fun_prop)
      · intro c d
        simpa only [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe]
          using (show ‖c + d‖ ≤ max ‖c‖ ‖d‖ from hω c.ofAbs d.ofAbs)
    let : IsUltrametricDist (S.ϕ ω).Completion :=
      IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm hL
    have h := norm_det_pairing_le_of_ultrametric g x
    rw [hg] at h
    exact h
  · let := hS ω hω
    let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    let := hξ.fibreInnerProductSpace ω hω
    have h := norm_det_pairing_le_of_innerProduct g x Module.finrank_baseChange
    rw [hg] at h
    exact h

omit [Field L] [Algebra K L] in
/-- Positive-rank determinant quotients inherit the exact pairing bound by
arbitrarily close single-wedge presentations. -/
theorem IsHermitian.norm_completedDeterminantPairing_le_of_pos_rank
    (hξ : ξ.IsHermitian hS) (hr : 0 < Module.finrank K E) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E)))
    (w : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    ‖completedDeterminantPairing K (S.ϕ ω).Completion E z w‖ ≤
      ξ.determinant.norm ω w * ξ.dual.determinant.norm ω z := by
  have hε (ε : ℝ) (hε : 0 < ε) :
      ‖completedDeterminantPairing K (S.ϕ ω).Completion E z w‖ ≤
        (ξ.determinant.norm ω w + ε) * (ξ.dual.determinant.norm ω z + ε) := by
    obtain ⟨x, hx, hxn⟩ := ξ.exists_determinant_ιMulti_norm_lt hr ω w hε
    obtain ⟨f, hf, hfn⟩ := ξ.dual.exists_determinant_ιMulti_norm_lt
      (show 0 < Module.finrank K (Module.Dual K E) by rwa [Subspace.dual_finrank_eq]) ω z hε
    have hp := hξ.norm_completedDeterminantPairing_ιMulti_le ξ ω f x
    rw [hf, hx] at hp
    exact hp.trans (mul_le_mul hxn.le hfn.le
      (Finset.prod_nonneg fun i _ ↦ ξ.dual.norm_nonneg ω (f i))
      (add_nonneg (ξ.determinant.norm_nonneg ω w) hε.le))
  have hlim : Filter.Tendsto (fun ε : ℝ ↦
      (ξ.determinant.norm ω w + ε) * (ξ.dual.determinant.norm ω z + ε))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (ξ.determinant.norm ω w * ξ.dual.determinant.norm ω z)) := by
    have hc : ContinuousAt (fun ε : ℝ ↦
        (ξ.determinant.norm ω w + ε) * (ξ.dual.determinant.norm ω z + ε)) 0 :=
      (continuousAt_const.add continuousAt_id).mul (continuousAt_const.add continuousAt_id)
    simpa only [add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hpos
  exact hε ε hpos

omit [Field L] [Algebra K L] in
/-- In rank zero the completed determinant pairing is multiplication on the
two scalar unit lines, with its exact product norm. -/
theorem norm_completedDeterminantPairing_of_finrank_eq_zero
    (hr : Module.finrank K E = 0) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E)))
    (w : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    ‖completedDeterminantPairing K (S.ϕ ω).Completion E z w‖ =
      ξ.determinant.norm ω w * ξ.dual.determinant.norm ω z := by
  have hd : Module.finrank K (Module.Dual K E) = 0 := Subspace.dual_finrank_eq.trans hr
  let : IsEmpty (Fin (Module.finrank K E)) := by rw [hr]; infer_instance
  obtain ⟨a, ha⟩ := exteriorPower_eq_smul_empty (S.ϕ ω).Completion hr
    (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _ w)
  obtain ⟨b, hb⟩ := exteriorPower_eq_smul_empty (S.ϕ ω).Completion hd
    (exteriorBaseChangeEquiv K (S.ϕ ω).Completion (Module.Dual K E) _ z)
  have hw : w = a • (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm
      (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ (fun _ ↦ 0)) := by
    apply (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).injective
    simpa only [map_smul, LinearEquiv.apply_symm_apply] using ha
  have hz : z = b • (exteriorBaseChangeEquiv K (S.ϕ ω).Completion (Module.Dual K E) _).symm
      (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ (fun _ ↦ 0)) := by
    apply (exteriorBaseChangeEquiv K (S.ϕ ω).Completion (Module.Dual K E) _).injective
    simpa only [map_smul, LinearEquiv.apply_symm_apply] using hb
  rw [hw, hz]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, norm_mul,
    completedDeterminantPairing_ιMulti, Matrix.det_isEmpty,
    ξ.determinant.norm_smul, ξ.dual.determinant.norm_smul,
    ξ.determinant_norm_empty_completed hr ω, ξ.dual.determinant_norm_empty_completed hd ω,
    mul_one, one_mul, mul_comm]

omit [Field L] [Algebra K L] in
/-- The canonical completed determinant pairing is contractive for a
Hermitian family, including the scalar determinant line in rank zero. -/
theorem IsHermitian.norm_completedDeterminantPairing_le
    (hξ : ξ.IsHermitian hS) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E)))
    (w : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    ‖completedDeterminantPairing K (S.ϕ ω).Completion E z w‖ ≤
      ξ.determinant.norm ω w * ξ.dual.determinant.norm ω z := by
  by_cases hr : Module.finrank K E = 0
  · exact (ξ.norm_completedDeterminantPairing_of_finrank_eq_zero hr ω z w).le
  · exact hξ.norm_completedDeterminantPairing_le_of_pos_rank ξ (Nat.pos_of_ne_zero hr) ω z w

end NormFamily

end

end ArakelovGeometry
