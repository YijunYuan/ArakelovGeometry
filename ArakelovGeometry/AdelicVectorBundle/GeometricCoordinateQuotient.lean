/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.UltrametricCoordinateSplit
import ArakelovGeometry.AdelicVectorBundle.BasisNorm
import ArakelovGeometry.AdelicVectorBundle.Quotient

/-!
# Minimum lifts for actual completed coordinate quotients

Maximal minors produce minimum lifts for the canonical quotient family on
actual completed tensor fibres, without assuming an adapted basis.
-/

open scoped TensorProduct Matrix

noncomputable section

namespace ArakelovGeometry.NormFamily

variable {K E m : Type*} [Field K] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E] [Fintype m]

/-- Every actual completed quotient vector has a minimum lift for the coordinate
norm at a non-Archimedean place, including empty kernel or ambient bases. -/
theorem ofBasis_quotient_exists_minimum_lift (b : Module.Basis m K E)
    (F : Submodule K E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⧸ F)) :
    ∃ u : (S.ϕ ω).Completion ⊗[K] E,
      F.mkQ.baseChange (S.ϕ ω).Completion u = z ∧
      (ofBasis S E b).norm ω u = ((ofBasis S E b).quotient F).norm ω z := by
  classical
  let L := (S.ϕ ω).Completion
  let q := F.mkQ.baseChange L
  let e := (b.baseChange L).equivFun
  let c := Module.finBasis L q.ker
  let A : Matrix m (Fin (Module.finrank L q.ker)) L := fun i j ↦ e (c j).val i
  let : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (S.norm_add_le_max_of_finite ω hω)
  have hA : LinearIndependent L A.col := by
    exact (c.linearIndependent.map' q.ker.subtype
      (LinearMap.ker_eq_bot.mpr (Submodule.subtype_injective _))).map'
      e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  have heA (a : Fin (Module.finrank L q.ker) → L) :
      e (c.equivFun.symm a).val = A *ᵥ a := by
    rw [← c.sum_equivFun (c.equivFun.symm a), LinearEquiv.apply_symm_apply]
    ext i
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, A]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  obtain ⟨y, hy⟩ := LinearMap.baseChange_surjective L F.mkQ_surjective z
  obtain ⟨I, _, _, hmin⟩ := ArakelovGeometry.Matrix.exists_maximal_minor_quotient_minimum A hA
  obtain ⟨_, _, hres, a₀, ha₀⟩ := hmin (e y)
  let u := y + (c.equivFun.symm a₀).val
  have he : e u = e y - (A * (A.submatrix I id)⁻¹) *ᵥ (e y ∘ I) := by
    dsimp only [u]
    rw [map_add, heA]
    exact ha₀
  have hu : q u = z := by
    dsimp only [u]
    rw [map_add, (c.equivFun.symm a₀).property, add_zero]
    exact hy
  refine ⟨u, hu, ?_⟩
  apply le_antisymm
  · change (ofBasis S E b).norm ω u ≤
      (ofBasis S E b).quotientSeminorm F.mkQ F.mkQ_surjective ω z
    apply ((ofBasis S E b).le_quotientSeminorm_iff F.mkQ F.mkQ_surjective ω z _).2
    intro v hv
    have hker : v - y ∈ q.ker := by
      change q (v - y) = 0
      rw [map_sub, hv, hy, sub_self]
    let a := c.equivFun ⟨v - y, hker⟩
    have heva : e y + A *ᵥ a = e v := by
      rw [← heA]
      change e y + e (c.equivFun.symm (c.equivFun ⟨v - y, hker⟩)).val = e v
      rw [LinearEquiv.symm_apply_apply]
      simp
    rw [ofBasis_norm, ofBasis_norm, he]
    exact heva ▸ hres a
  · change (ofBasis S E b).quotientSeminorm F.mkQ F.mkQ_surjective ω z ≤
      (ofBasis S E b).norm ω u
    rw [← hu]
    exact (ofBasis S E b).quotientSeminorm_le F.mkQ F.mkQ_surjective ω u

end ArakelovGeometry.NormFamily
