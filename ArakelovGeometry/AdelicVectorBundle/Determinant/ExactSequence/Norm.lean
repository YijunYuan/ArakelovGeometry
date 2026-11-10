/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Determinant.ExactSequence
import ArakelovGeometry.AdelicVectorBundle.Determinant.WedgeApproximation
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Norm bounds for the exact-sequence determinant map

The actual completed wedge formula and approximate quotient lifts give the
product bound for restricted subspace vectors and quotient vectors.
-/

@[expose] public section

open scoped TensorProduct Topology
open Filter

namespace ArakelovGeometry.NormFamily

noncomputable section

variable {K : Type*} [Field K] {S : AdelicStructure K}
  {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E) (W : Submodule K E) (ω : S.Ω)

/-- Every actual choice of completed quotient lifts bounds the determinant
image by the product of the restricted and ambient vector norms. -/
theorem determinantSequence_norm_wedge_lift_le
    (w : Fin (Module.finrank K W) → (S.ϕ ω).Completion ⊗[K] W)
    (v : Fin (Module.finrank K (E ⧸ W)) → (S.ϕ ω).Completion ⊗[K] E) :
    ξ.determinant.norm ω
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm
        (determinantSequenceEquivCompleted W (S.ϕ ω).Completion
          (exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K W) w ⊗ₜ[(S.ϕ ω).Completion]
            exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K (E ⧸ W))
              (fun j ↦ W.mkQ.baseChange (S.ϕ ω).Completion (v j))))) ≤
      (∏ i, (ξ.restrict W).norm ω (w i)) * ∏ j, ξ.norm ω (v j) := by
  have he := determinantSequenceEquivCompleted_ιMulti W (S.ϕ ω).Completion w v
  have hn := congrArg (fun z ↦ ξ.determinant.norm ω
    ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm z)) he
  have h := ξ.determinant_norm_ιMulti_le ω
    (fun i ↦ Fin.append (fun j ↦ W.subtype.baseChange (S.ϕ ω).Completion (w j)) v
      ((finCongr (finrank_subspace_add_quotient W)).symm i))
  rw [(finCongr (finrank_subspace_add_quotient W)).symm.prod_comp
    (fun i ↦ ξ.norm ω (Fin.append
      (fun j ↦ W.subtype.baseChange (S.ϕ ω).Completion (w j)) v i)), Fin.prod_univ_add] at h
  exact hn.le.trans (by
    simpa only [Fin.append_left, Fin.append_right, restrict_norm] using h)

/-- Approximate completed quotient lifts remove all lift choices from the
determinant product bound. Empty tuples are included. -/
theorem determinantSequence_norm_wedge_le
    (w : Fin (Module.finrank K W) → (S.ϕ ω).Completion ⊗[K] W)
    (q : Fin (Module.finrank K (E ⧸ W)) → (S.ϕ ω).Completion ⊗[K] (E ⧸ W)) :
    ξ.determinant.norm ω
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm
        (determinantSequenceEquivCompleted W (S.ϕ ω).Completion
          (exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K W) w ⊗ₜ[(S.ϕ ω).Completion]
            exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K (E ⧸ W)) q))) ≤
      (∏ i, (ξ.restrict W).norm ω (w i)) * ∏ j, (ξ.quotient W).norm ω (q j) := by
  let A := ∏ i, (ξ.restrict W).norm ω (w i)
  have hA : 0 ≤ A := Finset.prod_nonneg fun i _ ↦ (ξ.restrict W).norm_nonneg ω (w i)
  have hc : Continuous (fun t : ℝ ↦ A * ∏ j, ((ξ.quotient W).norm ω (q j) + t)) :=
    continuous_const.mul (continuous_finsetProd _ fun _ _ ↦ continuous_const.add continuous_id)
  have hl : Tendsto (fun t : ℝ ↦ A * ∏ j, ((ξ.quotient W).norm ω (q j) + t))
      (𝓝[Set.Ioi 0] 0) (𝓝 (A * ∏ j, (ξ.quotient W).norm ω (q j))) := by
    simpa only [add_zero] using hc.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝 0)
  apply ge_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hlift (j : Fin (Module.finrank K (E ⧸ W))) :
      ∃ v : (S.ϕ ω).Completion ⊗[K] E,
        W.mkQ.baseChange (S.ϕ ω).Completion v = q j ∧
          ξ.norm ω v < (ξ.quotient W).norm ω (q j) + t :=
    ξ.exists_pushforward_lift_lt W.mkQ W.mkQ_surjective ω (q j) ht
  let v (j : Fin (Module.finrank K (E ⧸ W))) := (hlift j).choose
  have hv (j : Fin (Module.finrank K (E ⧸ W))) :
      W.mkQ.baseChange (S.ϕ ω).Completion (v j) = q j := (hlift j).choose_spec.1
  have hn (j : Fin (Module.finrank K (E ⧸ W))) :
      ξ.norm ω (v j) < (ξ.quotient W).norm ω (q j) + t := (hlift j).choose_spec.2
  have h := ξ.determinantSequence_norm_wedge_lift_le W ω w v
  have he := congrArg (fun q ↦ ξ.determinant.norm ω
    ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm
      (determinantSequenceEquivCompleted W (S.ϕ ω).Completion
        (exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K W) w ⊗ₜ[(S.ϕ ω).Completion]
          exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K (E ⧸ W)) q))))
    (funext hv)
  exact he.symm.le.trans (h.trans (mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (fun j _ ↦ ξ.norm_nonneg ω (v j)) (fun j _ ↦ (hn j).le)) hA))

/-- A bound on all wedges extends to all determinant vectors by the
actual determinant-norm approximation, including both degree-zero lines. -/
theorem norm_determinant_tensor_le_of_wedge_bound
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {U : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    {T : Type*} [AddCommGroup T] [Module K T]
    (α : NormFamily S V) (β : NormFamily S U) (γ : NormFamily S T) (ω : S.Ω)
    (P : (((S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K V) V))
      ⊗[(S.ϕ ω).Completion]
        ((S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K U) U)))
        →ₗ[(S.ϕ ω).Completion] (S.ϕ ω).Completion ⊗[K] T)
    (hP : ∀ (w : Fin (Module.finrank K V) → (S.ϕ ω).Completion ⊗[K] V)
      (q : Fin (Module.finrank K U) → (S.ϕ ω).Completion ⊗[K] U),
      γ.norm ω (P
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion V (Module.finrank K V)).symm
          (exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K V) w) ⊗ₜ[(S.ϕ ω).Completion]
        (exteriorBaseChangeEquiv K (S.ϕ ω).Completion U (Module.finrank K U)).symm
          (exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K U) q))) ≤
      (∏ i, α.norm ω (w i)) * ∏ j, β.norm ω (q j))
    (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K V) V))
    (u : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K U) U)) :
    γ.norm ω (P (z ⊗ₜ[(S.ϕ ω).Completion] u)) ≤
      α.determinant.norm ω z * β.determinant.norm ω u := by
  let L := (S.ϕ ω).Completion
  let eV := exteriorBaseChangeEquiv K L V (Module.finrank K V)
  let eU := exteriorBaseChangeEquiv K L U (Module.finrank K U)
  let A := α.determinant.norm ω z
  let B := β.determinant.norm ω u
  have hc : Continuous (fun t : ℝ ↦ (A + t) * (B + t)) :=
    (continuous_const.add continuous_id).mul (continuous_const.add continuous_id)
  have hl : Tendsto (fun t : ℝ ↦ (A + t) * (B + t))
      (𝓝[Set.Ioi 0] 0) (𝓝 (A * B)) := by
    simpa only [add_zero] using hc.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝 0)
  apply ge_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin] with t ht
  obtain ⟨a, w, hw, ha⟩ := α.exists_smul_determinant_ιMulti_norm_lt ω z ht
  obtain ⟨b, q, hq, hb⟩ := β.exists_smul_determinant_ιMulti_norm_lt ω u ht
  let wdet := eV.symm (exteriorPower.ιMulti L (Module.finrank K V) w)
  let qdet := eU.symm (exteriorPower.ιMulti L (Module.finrank K U) q)
  have he : P (z ⊗ₜ[L] u) = (a * b) • P (wdet ⊗ₜ[L] qdet) := by
    rw [← hw, ← hq, TensorProduct.smul_tmul_smul, map_smul]
  have hn : γ.norm ω (P (z ⊗ₜ[L] u)) =
      (‖a‖ * ‖b‖) * γ.norm ω (P (wdet ⊗ₜ[L] qdet)) := by
    rw [he, γ.norm_smul, norm_mul]
  have hna : 0 ≤ ‖a‖ * ‖b‖ := mul_nonneg (_root_.norm_nonneg a) (_root_.norm_nonneg b)
  have hnq : 0 ≤ ‖b‖ * ∏ j, β.norm ω (q j) :=
    mul_nonneg (_root_.norm_nonneg b) (Finset.prod_nonneg fun j _ ↦ β.norm_nonneg ω (q j))
  calc
    γ.norm ω (P (z ⊗ₜ[L] u))
        = (‖a‖ * ‖b‖) * γ.norm ω (P (wdet ⊗ₜ[L] qdet)) := hn
    _ ≤ (‖a‖ * ‖b‖) * ((∏ i, α.norm ω (w i)) *
        ∏ j, β.norm ω (q j)) := mul_le_mul_of_nonneg_left (hP w q) hna
    _ = (‖a‖ * ∏ i, α.norm ω (w i)) *
        (‖b‖ * ∏ j, β.norm ω (q j)) := by ring
    _ ≤ (A + t) * (B + t) :=
      mul_le_mul ha.le hb.le hnq (add_nonneg (α.determinant.norm_nonneg ω z) ht.le)

/-- The canonical completed determinant map contracts on every pair of
determinant vectors, including degree-zero determinant lines. -/
theorem determinantSequence_norm_tmul_le
    (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K W) W))
    (u : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K (E ⧸ W)) (E ⧸ W))) :
    ξ.determinant.norm ω
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm
        (determinantSequenceEquivCompleted W (S.ϕ ω).Completion
          (exteriorBaseChangeEquiv K (S.ϕ ω).Completion W (Module.finrank K W) z
            ⊗ₜ[(S.ϕ ω).Completion]
            exteriorBaseChangeEquiv K (S.ϕ ω).Completion (E ⧸ W)
              (Module.finrank K (E ⧸ W)) u))) ≤
      (ξ.restrict W).determinant.norm ω z * (ξ.quotient W).determinant.norm ω u := by
  let L := (S.ϕ ω).Completion
  let eW := exteriorBaseChangeEquiv K L W (Module.finrank K W)
  let eQ := exteriorBaseChangeEquiv K L (E ⧸ W) (Module.finrank K (E ⧸ W))
  let eE := exteriorBaseChangeEquiv K L E (Module.finrank K E)
  let P := (eE.symm.toLinearMap.comp (determinantSequenceEquivCompleted W L).toLinearMap).comp
    (TensorProduct.map eW.toLinearMap eQ.toLinearMap)
  have hP (w : Fin (Module.finrank K W) → L ⊗[K] W)
      (q : Fin (Module.finrank K (E ⧸ W)) → L ⊗[K] (E ⧸ W)) :
      ξ.determinant.norm ω (P
        (eW.symm (exteriorPower.ιMulti L (Module.finrank K W) w) ⊗ₜ[L]
          eQ.symm (exteriorPower.ιMulti L (Module.finrank K (E ⧸ W)) q))) ≤
        (∏ i, (ξ.restrict W).norm ω (w i)) * ∏ j, (ξ.quotient W).norm ω (q j) := by
    simpa only [P, LinearMap.comp_apply, TensorProduct.map_tmul,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
        ξ.determinantSequence_norm_wedge_le W ω w q
  have h := norm_determinant_tensor_le_of_wedge_bound (ξ.restrict W) (ξ.quotient W)
    ξ.determinant ω P hP z u
  have he : P (z ⊗ₜ[L] u) =
      eE.symm (determinantSequenceEquivCompleted W L (eW z ⊗ₜ[L] eQ u)) := by
    exact congrArg (fun x ↦ eE.symm (determinantSequenceEquivCompleted W L x))
      (TensorProduct.map_tmul eW.toLinearMap eQ.toLinearMap z u)
  exact (congrArg (ξ.determinant.norm ω) he).symm.le.trans h

end

end ArakelovGeometry.NormFamily
