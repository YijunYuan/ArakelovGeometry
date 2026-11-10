/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldFullLatticeGauge
import ArakelovGeometry.AdelicVectorBundle.DeterminantPairingLocal
import ArakelovGeometry.Analysis.DeterminantExactSequence

/-! # Actual finite determinant norms of full-lattice gauges -/

open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry.NormFamily

variable {K E : Type*} [Field K] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- A finite coordinate maximum normalizes its actual completed basis wedge,
including the empty basis, without any condition at infinite places. -/
theorem determinant_norm_completedBasis_eq_one_of_coordinateSup
    (ξ : NormFamily S E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (b : Module.Basis (Fin (Module.finrank K E)) (S.ϕ ω).Completion
      ((S.ϕ ω).Completion ⊗[K] E))
    (hn : ∀ z, ξ.norm ω z = ‖b.equivFun z‖) :
    ξ.determinant.norm ω ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm
      (exteriorPower.ιMulti (S.ϕ ω).Completion _ b)) = 1 := by
  classical
  have hb (i) : ξ.norm ω (b i) ≤ 1 := by
    rw [hn]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    simp only [Module.Basis.equivFun_self]
    split_ifs <;> simp
  have hf (i) : ξ.dual.norm ω
      ((dualBaseChangeEquiv K (S.ϕ ω).Completion E).symm (b.coord i)) ≤ 1 := by
    apply ξ.dual_norm_le ω _ zero_le_one
    intro z
    rw [LinearEquiv.apply_symm_apply, one_mul, hn]
    exact norm_le_pi_norm (b.equivFun z) i
  let e := finCongr (Subspace.dual_finrank_eq (K := K) (V := E))
  let f (i : Fin (Module.finrank K (Module.Dual K E))) :=
    (dualBaseChangeEquiv K (S.ϕ ω).Completion E).symm (b.coord (e i))
  let w := (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm
    (exteriorPower.ιMulti (S.ϕ ω).Completion _ b)
  let z := (exteriorBaseChangeEquiv K (S.ϕ ω).Completion (Module.Dual K E) _).symm
    (exteriorPower.ιMulti (S.ϕ ω).Completion _ f)
  have hp : completedDeterminantPairing K (S.ϕ ω).Completion E z w = 1 := by
    rw [completedDeterminantPairing_ιMulti]
    have hm : Matrix.of (fun i j ↦ b.coord j (b i)) =
        (1 : Matrix (Fin (Module.finrank K E)) (Fin (Module.finrank K E))
          (S.ϕ ω).Completion) := by
      ext i j
      simp [Module.Basis.coord_apply, Matrix.one_apply, Finsupp.single_apply]
    simp only [f, e, Equiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      hm, Matrix.det_one]
  have hw : ξ.determinant.norm ω w ≤ 1 := by
    refine (ξ.determinant_norm_ιMulti_le ω b).trans ?_
    exact (Finset.prod_le_prod (fun i _ ↦ ξ.norm_nonneg ω (b i))
      (fun i _ ↦ hb i)).trans_eq (by simp)
  have hz : ξ.dual.determinant.norm ω z ≤ 1 := by
    refine (ξ.dual.determinant_norm_ιMulti_le ω f).trans ?_
    exact (Finset.prod_le_prod (fun i _ ↦ ξ.dual.norm_nonneg ω (f i))
      (fun i _ ↦ hf (e i))).trans_eq (by simp)
  have h := ξ.norm_completedDeterminantPairing_le_finite ω hω z w
  rw [hp, norm_one] at h
  exact le_antisymm hw (h.trans
    (mul_le_of_le_one_right (ξ.determinant.norm_nonneg ω w) hz))

/-- Finite actual determinant norms of rational wedges are the completed
scalar norms of their rational basis-coordinate determinants. -/
theorem determinant_norm_rational_wedge_of_coordinateSup
    (ξ : NormFamily S E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (b : Module.Basis (Fin (Module.finrank K E)) K E)
    (hn : ∀ z, ξ.norm ω z = ‖(b.baseChange (S.ϕ ω).Completion).equivFun z‖)
    (v : Fin (Module.finrank K E) → E) :
    ξ.determinant.norm ω
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] exteriorPower.ιMulti K _ v) =
      ‖algebraMap K (S.ϕ ω).Completion (b.det v)‖ := by
  have hw : exteriorPower.ιMulti K (Module.finrank K E) v =
      b.det v • exteriorPower.ιMulti K (Module.finrank K E) b := by
    apply (determinantCoordinateEquiv b).injective
    rw [map_smul, determinantCoordinateEquiv_ιMulti,
      determinantCoordinateEquiv_ιMulti, Module.Basis.det_self,
      smul_eq_mul, mul_one]
  have hu := ξ.determinant_norm_completedBasis_eq_one_of_coordinateSup ω hω
    (b.baseChange (S.ϕ ω).Completion) hn
  have hb : ⇑(b.baseChange (S.ϕ ω).Completion) =
      fun i ↦ (1 : (S.ϕ ω).Completion) ⊗ₜ[K] b i := by
    funext i
    exact Module.Basis.baseChange_apply _ _ _
  rw [hb, exteriorBaseChangeEquiv_symm_ιMulti_tmul, Finset.prod_const_one] at hu
  rw [hw, TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul
    (S.ϕ ω).Completion (b.det v), ξ.determinant.norm_smul, hu, mul_one]

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.NumberFieldLocalDeterminantGauge

open NumberField IsDedekindDomain
open AdelicStructure ActualPrimeIndexing NumberFieldFullLattice

variable {K E : Type*} [Field K] [NumberField K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The produced integral local basis, indexed by the original rational rank. -/
def localRankBasis (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K)) :
    Module.Basis (Fin (Module.finrank K E)) K E :=
  (rationalLocalGenericBasis L hfg hspan p).reindex
    (finCongr (finrank_rationalLocalSpan L hfg hspan p))

omit [FiniteDimensional K E] in
/-- The actual finite gauge is the maximum in the same produced local basis,
with only its finite index reordered to the rational rank. -/
theorem fullLatticeGaugeFamily_norm_localRankBasis
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤)
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (p : HeightOneSpectrum (𝓞 K))
    (z : ((normalizedNumberFieldAdelicStructure K).ϕ
      (normalizedPrimeParameter p)).Completion ⊗[K] E) :
    (fullLatticeGaugeFamily L hfg hspan η).norm (normalizedPrimeParameter p) z =
      ‖((localRankBasis L hfg hspan p).baseChange
        ((normalizedNumberFieldAdelicStructure K).ϕ
          (normalizedPrimeParameter p)).Completion).equivFun z‖ := by
  classical
  rw [fullLatticeGaugeFamily_norm_prime,
    scalarLatticeGauge_eq_localBasisNorm L hfg hspan p, NormFamily.ofBasis_norm]
  let b := rationalLocalGenericBasis L hfg hspan p
  let e := finCongr (finrank_rationalLocalSpan L hfg hspan p)
  have he : (localRankBasis L hfg hspan p).baseChange
      ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p)).Completion =
      (b.baseChange ((normalizedNumberFieldAdelicStructure K).ϕ
        (normalizedPrimeParameter p)).Completion).reindex e := by
    ext i
    simp only [localRankBasis, b, e, Module.Basis.baseChange_apply,
      Module.Basis.reindex_apply]
  rw [he]
  let B := b.baseChange ((normalizedNumberFieldAdelicStructure K).ϕ
    (normalizedPrimeParameter p)).Completion
  have hc : (B.reindex e).equivFun z = B.equivFun z ∘ e.symm := by
    funext i
    simp only [Module.Basis.equivFun_apply, Module.Basis.repr_reindex_apply,
      Function.comp_apply]
  change ‖B.equivFun z‖ = ‖(B.reindex e).equivFun z‖
  rw [hc]
  exact (e.symm.surjective.pi_norm_comp (B.equivFun z)).symm

/-- The literal completed determinant norm of every rational wedge is its
coordinate determinant norm in the produced local integral basis. -/
theorem fullLatticeGaugeFamily_determinant_norm_rational_wedge
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤)
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (p : HeightOneSpectrum (𝓞 K)) (v : Fin (Module.finrank K E) → E) :
    (fullLatticeGaugeFamily L hfg hspan η).determinant.norm (normalizedPrimeParameter p)
      ((1 : ((normalizedNumberFieldAdelicStructure K).ϕ
        (normalizedPrimeParameter p)).Completion) ⊗ₜ[K] exteriorPower.ιMulti K _ v) =
      ‖algebraMap K ((normalizedNumberFieldAdelicStructure K).ϕ
        (normalizedPrimeParameter p)).Completion ((localRankBasis L hfg hspan p).det v)‖ := by
  exact NormFamily.determinant_norm_rational_wedge_of_coordinateSup
    (fullLatticeGaugeFamily L hfg hspan η) (normalizedPrimeParameter p)
    (normalizedPrimeParameter_mem_fin p) (localRankBasis L hfg hspan p)
    (fullLatticeGaugeFamily_norm_localRankBasis L hfg hspan η p) v

/-- The wedge of the actual local integral basis has completed determinant norm one. -/
theorem fullLatticeGaugeFamily_determinant_norm_localBasis
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤)
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (p : HeightOneSpectrum (𝓞 K)) :
    (fullLatticeGaugeFamily L hfg hspan η).determinant.norm (normalizedPrimeParameter p)
      ((1 : ((normalizedNumberFieldAdelicStructure K).ϕ
        (normalizedPrimeParameter p)).Completion) ⊗ₜ[K]
          exteriorPower.ιMulti K _ (localRankBasis L hfg hspan p)) = 1 := by
  rw [fullLatticeGaugeFamily_determinant_norm_rational_wedge, Module.Basis.det_self,
    map_one, norm_one]

end ArakelovGeometry.NumberFieldLocalDeterminantGauge
