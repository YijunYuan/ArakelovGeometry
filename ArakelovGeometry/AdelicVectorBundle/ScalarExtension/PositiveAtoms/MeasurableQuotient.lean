/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Measurability.Basic
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Rational
import ArakelovGeometry.Analysis.Ultrametric.SelectedMinor
import ArakelovGeometry.LinearAlgebra.MeasurableMaximalMinor
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Measurable actual coordinate quotients without field countability

A finite measurable ground-field minor selection is retained on each actual
completed fibre. Its residual computes the canonical quotient norm.
-/

@[expose] public section

open scoped TensorProduct Matrix
noncomputable section

namespace ArakelovGeometry.NormFamily

variable {K E m n : Type*} [Field K] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Fintype m] [Fintype n] [DecidableEq n]

/-- A prescribed normalized ground-field minor computes the canonical quotient
norm of every rational section in the actual completed tensor quotient. -/
theorem ofBasis_quotient_norm_rational_eq_residual_of_minor (b : Module.Basis m K E)
    (F : Submodule K E) (c : Module.Basis n K F) (I : n → m)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) :
    let A : Matrix m n K := fun i j ↦ b.equivFun (c j).val i
    (A.submatrix I id).det ≠ 0 →
    (A * (A.submatrix I id)⁻¹).submatrix I id = 1 →
    (∀ i j, (S.ϕ ω) ((A * (A.submatrix I id)⁻¹) i j) ≤ 1) →
    ∀ x : E, ((ofBasis S E b).quotient F).norm ω
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] F.mkQ x) =
        ‖fun i ↦ (S.ϕ ω)
          ((b.equivFun x - (A * (A.submatrix I id)⁻¹) *ᵥ (b.equivFun x ∘ I)) i)‖ := by
  classical
  intro A hd hid hB x
  let L := (S.ϕ ω).Completion
  let f := algebraMap K L
  let C := A.submatrix I id
  let A' := A.map f
  have hCi : (C.map f)⁻¹ = C⁻¹.map f := by
    apply _root_.Matrix.inv_eq_left_inv
    rw [← _root_.Matrix.map_mul,
      _root_.Matrix.nonsing_inv_mul C (isUnit_iff_ne_zero.mpr hd)]
    exact _root_.Matrix.map_one f f.map_zero f.map_one
  have hsub : A'.submatrix I id = C.map f := rfl
  have hmap : A' * (A'.submatrix I id)⁻¹ = (A * C⁻¹).map f := by
    rw [hsub, hCi]
    exact _root_.Matrix.map_mul.symm
  have hdet : (A'.submatrix I id).det ≠ 0 := by
    rw [hsub]
    change (f.mapMatrix C).det ≠ 0
    rw [← f.map_det]
    exact (map_ne_zero f).mpr hd
  have hid' : (A' * (A'.submatrix I id)⁻¹).submatrix I id = 1 := by
    rw [hmap, _root_.Matrix.submatrix_map, hid]
    exact _root_.Matrix.map_one f f.map_zero f.map_one
  have hB' : ∀ i j, ‖(A' * (A'.submatrix I id)⁻¹) i j‖ ≤ 1 := by
    intro i j
    rw [hmap]
    change ‖algebraMap K L ((A * C⁻¹) i j)‖ ≤ 1
    rw [S.norm_algebraMap_eq_absValue]
    exact hB i j
  let : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (S.norm_add_le_max_of_finite ω hω)
  let e := (b.baseChange L).equivFun
  let d := c.baseChange L
  let k := F.subtype.baseChange L
  let q := F.mkQ.baseChange L
  have hecol (j : n) : e (k (d j)) = fun i ↦ f (A i j) := by
    ext i
    change (b.baseChange L).equivFun
      (F.subtype.baseChange L ((c.baseChange L) j)) i = f (A i j)
    rw [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul]
    exact basis_equivFun_one_tmul b ω (c j).val i
  have heA (a : n → L) : e (k (d.equivFun.symm a)) = A' *ᵥ a := by
    rw [← d.sum_equivFun (d.equivFun.symm a), LinearEquiv.apply_symm_apply]
    ext i
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      hecol, Matrix.mulVec, dotProduct, A', Matrix.map_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  let y : L ⊗[K] E := 1 ⊗ₜ[K] x
  obtain ⟨_, hmin, a₀, ha₀⟩ :=
    ArakelovGeometry.Matrix.residual_minimum_of_normalized_minor A' I hdet hid' hB' (e y)
  let u := y + k (d.equivFun.symm a₀)
  have he : e u = e y - (A' * (A'.submatrix I id)⁻¹) *ᵥ (e y ∘ I) := by
    dsimp only [u]
    rw [map_add, heA]
    exact ha₀
  have hqk : q.comp k = 0 := by
    rw [← LinearMap.baseChange_comp]
    have h : F.mkQ.comp F.subtype = 0 := by ext t; simp
    rw [h, LinearMap.baseChange_zero]
  have hu : q u = q y := by
    dsimp only [u]
    rw [map_add]
    have hk : q (k (d.equivFun.symm a₀)) = 0 := congrArg
      (fun g : (L ⊗[K] F) →ₗ[L] (L ⊗[K] (E ⧸ F)) ↦ g (d.equivFun.symm a₀)) hqk
    rw [hk, add_zero]
  have hnorm : ((ofBasis S E b).quotient F).norm ω (q y) = (ofBasis S E b).norm ω u := by
    apply le_antisymm
    · rw [← hu]
      exact (ofBasis S E b).quotientSeminorm_le F.mkQ F.mkQ_surjective ω u
    · apply ((ofBasis S E b).le_quotientSeminorm_iff
        F.mkQ F.mkQ_surjective ω (q y) _).2
      intro v hv
      have hker : v - y ∈ q.ker := by
        change q (v - y) = 0
        rw [map_sub, hv, sub_self]
      rw [baseChange_ker F.mkQ ω, Submodule.ker_mkQ] at hker
      obtain ⟨t, ht⟩ := hker
      let a := d.equivFun t
      have heva : e y + A' *ᵥ a = e v := by
        rw [← heA]
        change e y + e (k (d.equivFun.symm (d.equivFun t))) = e v
        rw [LinearEquiv.symm_apply_apply, ht]
        simp
      rw [ofBasis_norm, ofBasis_norm, he]
      exact heva ▸ hmin a
  change ((ofBasis S E b).quotient F).norm ω (q y) = _
  rw [hnorm, ofBasis_norm, he]
  let r := b.equivFun x - (A * C⁻¹) *ᵥ (b.equivFun x ∘ I)
  have hr : e y - (A' * (A'.submatrix I id)⁻¹) *ᵥ (e y ∘ I) = f ∘ r := by
    ext i
    rw [hmap]
    simp only [Pi.sub_apply, r, map_sub, Function.comp_apply]
    have hey (j : m) : e y j = f (b.equivFun x j) := basis_equivFun_one_tmul b ω x j
    rw [hey, f.map_mulVec]
    congr 1
    congr 1
    funext j
    exact hey (I j)
  rw [hr]
  have hcoord (i : m) : ‖(f ∘ r) i‖ = ‖(S.ϕ ω) (r i)‖ := by
    rw [Function.comp_apply, S.norm_algebraMap_eq_absValue,
      Real.norm_eq_abs, abs_of_nonneg (apply_nonneg _ _)]
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (_root_.norm_nonneg _)).mpr fun i ↦
      (hcoord i).trans_le (norm_le_pi_norm (fun i ↦ (S.ϕ ω) (r i)) i)
  · exact (pi_norm_le_iff_of_nonneg (_root_.norm_nonneg _)).mpr fun i ↦
      (hcoord i).symm.trans_le (norm_le_pi_norm (f ∘ r) i)

omit [Fintype n] [DecidableEq n] in
/-- Actual coordinate quotient norms are measurable on any adelic curve whose
places are all non-Archimedean, without countability of the field or base. -/
theorem ofBasis_quotient_isMeasurable_of_all_finite (b : Module.Basis m K E)
    (F : Submodule K E) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    ((ofBasis S E b).quotient F).IsMeasurable := by
  classical
  let c := Module.finBasis K F
  let A : Matrix m (Fin (Module.finrank K F)) K := fun i j ↦ b.equivFun (c j).val i
  have hA : LinearIndependent K A.col := by
    exact (c.linearIndependent.map' F.subtype
      (LinearMap.ker_eq_bot.mpr (Submodule.subtype_injective _))).map'
      b.equivFun.toLinearMap (LinearMap.ker_eq_bot.mpr b.equivFun.injective)
  obtain ⟨I, _, hnorm, _, _, hres, _⟩ :=
    ArakelovGeometry.Matrix.exists_measurable_maximal_minor_evaluations
      A hA S.ϕ S.measurable_absValue
  intro z
  obtain ⟨x, rfl⟩ := F.mkQ_surjective z
  have hm : Measurable (fun ω ↦ ‖fun i ↦ (S.ϕ ω)
      ((b.equivFun x - (A * (A.submatrix (I ω) id)⁻¹) *ᵥ
        (b.equivFun x ∘ I ω)) i)‖) :=
    (Measurable.of_eval fun i ↦ hres (b.equivFun x) i).norm
  convert hm using 1
  funext ω
  obtain ⟨_, hd, _, hid, hB⟩ := hnorm ω
  exact ofBasis_quotient_norm_rational_eq_residual_of_minor
    b F c (I ω) ω (hS ω) hd hid hB x

end ArakelovGeometry.NormFamily
