/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DeterminantSequenceDual
public import ArakelovGeometry.AdelicVectorBundle.ElementaryRestrictionQuotient

/-!
# Majorant discrepancy of an actual exact sequence

Every elementary majorant restricts and descends to elementary majorants
of the end spaces. Its canonical determinant map is an isometry. Comparing
compatible determinant basis vectors and taking the actual majorant infimum
proves the capital-discrepancy operator bound for arbitrary original norms.
All statements include rank zero and zero-dimensional end spaces.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

noncomputable section

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F]

private theorem basisWedge_ne_zero
    (b : Module.Basis (Fin (Module.finrank K E)) K E) :
    _root_.exteriorPower.ιMulti K (Module.finrank K E) b ≠ 0 := by
  intro h
  have hp := determinantDualBasisWedge_pairing b
  rw [h, map_zero] at hp
  exact zero_ne_one hp

private theorem div_normRatios_le_targetRatio
    (mW mQ pW pQ pE a : ℝ) (hpW : 0 < pW) (hpQ : 0 < pQ)
    (hpE : 0 < pE) (ha : 0 < a) (hmW : 0 ≤ mW) (hmQ : 0 ≤ mQ)
    (hb : pE ≤ a * (pW * pQ)) :
    (mW / pW) * (mQ / pQ) / a ≤ (mW * mQ) / pE := by
  apply (div_le_iff₀ ha).2
  have hc : pE / (pW * pQ) ≤ a := (div_le_iff₀ (mul_pos hpW hpQ)).2 hb
  calc
    (mW / pW) * (mQ / pQ) = ((mW * mQ) / pE) * (pE / (pW * pQ)) := by
      field_simp [hpW.ne', hpQ.ne', hpE.ne']
    _ ≤ ((mW * mQ) / pE) * a :=
      mul_le_mul_of_nonneg_left hc (div_nonneg (mul_nonneg hmW hmQ) hpE.le)

/-- Pointwise order at a chosen fibre descends to the actual completed
quotient norm, without any elementary or ultrametric premise. -/
theorem pushforward_norm_mono (ξ η : NormFamily S E)
    (π : E →ₗ[K] F) (hπ : Function.Surjective π) (ω : S.Ω)
    (hl : ∀ x, ξ.norm ω x ≤ η.norm ω x) (z : (S.ϕ ω).Completion ⊗[K] F) :
    (ξ.pushforward π hπ).norm ω z ≤ (η.pushforward π hπ).norm ω z := by
  change ξ.quotientSeminorm π hπ ω z ≤ η.quotientSeminorm π hπ ω z
  apply (η.le_quotientSeminorm_iff π hπ ω z _).2
  intro x hx
  rw [← hx]
  exact (ξ.quotientSeminorm_le π hπ ω x).trans (hl x)

/-- In rank zero every actual determinant norm ratio is one, independently
of the two original fibre norms. -/
theorem determinantRatio_eq_one_of_finrank_eq_zero (ξ η : NormFamily S E)
    (ω : S.Ω) (hr : Module.finrank K E = 0) :
    η.determinant.norm ω (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E)) /
      ξ.determinant.norm ω (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E)) = 1 := by
  let b := Module.finBasis K E
  let w := _root_.exteriorPower.ιMulti K (Module.finrank K E) b
  have hw : w ≠ 0 := basisWedge_ne_zero b
  have hc : (1 : (S.ϕ ω).Completion) ⊗ₜ[K] w ≠ 0 := by
    intro h
    have hp := ξ.determinant.norm_rational_pos ω hw
    rw [h, ξ.determinant.norm_zero] at hp
    exact (lt_irrefl 0) hp
  have hξ : ξ.determinant.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] w) = 1 := by
    simpa only [w, norm_one] using ξ.determinant_norm_empty_tmul hr ω 1 b
  have hη : η.determinant.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] w) = 1 := by
    simpa only [w, norm_one] using η.determinant_norm_empty_tmul hr ω 1 b
  have h := ξ.determinantRatio_eq_of_nonzero η ω (1 ⊗ₜ[K] w) hc
  rw [hξ, hη, div_one] at h
  exact h.symm

/-- A lower bound for every actual elementary majorant ratio bounds the
intrinsic infimum, with its exact rank-zero convention. -/
theorem le_majorantDiscrepancy_of_forall_majorant (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω) (a : ℝ)
    (ha : ∀ η : NormFamily S E, η.IsElementaryAt hN ω →
      (∀ x, ξ.norm ω x ≤ η.norm ω x) →
      a ≤ η.determinant.norm ω (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E)) /
        ξ.determinant.norm ω (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E))) :
    a ≤ ξ.majorantDiscrepancy hN ω := by
  by_cases hr : Module.finrank K E = 0
  · rw [ξ.majorantDiscrepancy_eq_one_of_finrank_eq_zero hN hr]
    obtain ⟨η, he, hl⟩ := ξ.exists_elementaryMajorant hN ω
    simpa only [ξ.determinantRatio_eq_one_of_finrank_eq_zero η ω hr] using ha η he hl
  · rw [majorantDiscrepancy, ite_eq_right hr]
    apply le_csInf (ξ.majorantRatios_nonempty hN ω)
    rintro b ⟨η, he, hl, rfl⟩
    exact ha η he hl

/-- The canonical determinant isomorphism has positive operator norm in
all ranks, since its tensor determinant source is always a nonzero line. -/
theorem determinantSequence_operatorNorm_pos_of_equiv (ξ : NormFamily S E)
    (W : Submodule K E) (ω : S.Ω) :
    0 < ((ξ.restrict W).determinant.injectiveTensorPair
      (ξ.quotient W).determinant).operatorNorm
      ξ.determinant ω (determinantSequenceEquiv W).toLinearMap := by
  let DW := ⋀[K]^(Module.finrank K W) W
  let DQ := ⋀[K]^(Module.finrank K (E ⧸ W)) (E ⧸ W)
  have hr : Module.finrank K (DW ⊗[K] DQ) = 1 := by
    rw [Module.finrank_tensorProduct,
      show Module.finrank K DW = 1 from determinant_finrank,
      show Module.finrank K DQ = 1 from determinant_finrank, mul_one]
  let : Nontrivial (DW ⊗[K] DQ) :=
    Module.nontrivial_of_finrank_pos (by rw [hr]; exact zero_lt_one)
  apply operatorNorm_pos
  intro hf
  obtain ⟨x, hx⟩ := exists_ne (0 : DW ⊗[K] DQ)
  apply hx
  apply (determinantSequenceEquiv W).injective
  change (determinantSequenceEquiv W).toLinearMap x =
    (determinantSequenceEquiv W).toLinearMap 0
  rw [hf]
  rfl

/-- Every actual elementary majorant supplies the capital-discrepancy
product bound through its actual end norms and determinant isometry. -/
theorem majorantDiscrepancy_restrict_mul_quotient_div_le_majorantRatio
    (ξ η : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (W : Submodule K E) (ω : S.Ω)
    (he : η.IsElementaryAt hN ω) (hl : ∀ x, ξ.norm ω x ≤ η.norm ω x) :
    (ξ.restrict W).majorantDiscrepancy hN ω *
        (ξ.quotient W).majorantDiscrepancy hN ω /
        ((ξ.restrict W).determinant.injectiveTensorPair
          (ξ.quotient W).determinant).operatorNorm
          ξ.determinant ω (determinantSequenceEquiv W).toLinearMap ≤
      η.determinant.norm ω (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E)) /
        ξ.determinant.norm ω (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E)) := by
  let DW := ⋀[K]^(Module.finrank K W) W
  let DQ := ⋀[K]^(Module.finrank K (E ⧸ W)) (E ⧸ W)
  let D := (ξ.restrict W).determinant.injectiveTensorPair (ξ.quotient W).determinant
  let w := determinantGenerator (K := K) (E := W)
  let q := determinantGenerator (K := K) (E := E ⧸ W)
  let pW := (ξ.restrict W).determinant.norm ω (1 ⊗ₜ[K] w)
  let pQ := (ξ.quotient W).determinant.norm ω (1 ⊗ₜ[K] q)
  let pE := ξ.determinant.norm ω (1 ⊗ₜ[K] determinantSequenceEquiv W (w ⊗ₜ[K] q))
  let mW := (η.restrict W).determinant.norm ω (1 ⊗ₜ[K] w)
  let mQ := (η.quotient W).determinant.norm ω (1 ⊗ₜ[K] q)
  let mE := η.determinant.norm ω (1 ⊗ₜ[K] determinantSequenceEquiv W (w ⊗ₜ[K] q))
  let a := D.operatorNorm ξ.determinant ω (determinantSequenceEquiv W).toLinearMap
  have hw : w ≠ 0 := determinantGenerator_ne_zero
  have hq : q ≠ 0 := determinantGenerator_ne_zero
  have hpW : 0 < pW := (ξ.restrict W).determinant.norm_rational_pos ω hw
  have hpQ : 0 < pQ := (ξ.quotient W).determinant.norm_rational_pos ω hq
  have hWline : Module.finrank K DW = 1 := determinant_finrank
  have hQline : Module.finrank K DQ = 1 := determinant_finrank
  have hn := (ξ.restrict W).determinant.injectiveTensorPair_norm_rational_generators
    (ξ.quotient W).determinant hWline hQline hw hq ω
  change D.norm ω (1 ⊗ₜ[K] (w ⊗ₜ[K] q)) = pW * pQ at hn
  have ht : w ⊗ₜ[K] q ≠ 0 := by
    intro h
    rw [h, TensorProduct.tmul_zero, D.norm_zero] at hn
    linarith [mul_pos hpW hpQ]
  have hf : determinantSequenceEquiv W (w ⊗ₜ[K] q) ≠ 0 :=
    fun h ↦ ht ((determinantSequenceEquiv W).injective
      (h.trans (determinantSequenceEquiv W).map_zero.symm))
  have hpE : 0 < pE := ξ.determinant.norm_rational_pos ω hf
  have ha0 : 0 < a := ξ.determinantSequence_operatorNorm_pos_of_equiv W ω
  have hcE : (1 : (S.ϕ ω).Completion) ⊗ₜ[K]
      determinantSequenceEquiv W (w ⊗ₜ[K] q) ≠ 0 := by
    intro h
    apply hpE.ne'
    change ξ.determinant.norm ω
      (1 ⊗ₜ[K] determinantSequenceEquiv W (w ⊗ₜ[K] q)) = 0
    rw [h, ξ.determinant.norm_zero]
  have horderW (x : (S.ϕ ω).Completion ⊗[K] W) :
      (ξ.restrict W).norm ω x ≤ (η.restrict W).norm ω x :=
    hl (W.subtype.baseChange (S.ϕ ω).Completion x)
  have horderQ (x : (S.ϕ ω).Completion ⊗[K] (E ⧸ W)) :
      (ξ.quotient W).norm ω x ≤ (η.quotient W).norm ω x :=
    ξ.pushforward_norm_mono η W.mkQ W.mkQ_surjective ω hl x
  have hW := (ξ.restrict W).majorantDiscrepancy_le_ratio (η.restrict W) hN ω
    (he.restrict W) horderW
  have hQ := (ξ.quotient W).majorantDiscrepancy_le_ratio (η.quotient W) hN ω
    (he.quotient W) horderQ
  change (ξ.restrict W).majorantDiscrepancy hN ω ≤ mW / pW at hW
  change (ξ.quotient W).majorantDiscrepancy hN ω ≤ mQ / pQ at hQ
  have hi := he.determinantSequence_norm_eq W (1 ⊗ₜ[K] (w ⊗ₜ[K] q))
  rw [LinearMap.baseChange_tmul,
    (η.restrict W).determinant.injectiveTensorPair_norm_rational_generators
      (η.quotient W).determinant hWline hQline hw hq ω] at hi
  change mE = mW * mQ at hi
  have hb := D.norm_baseChange_le_operatorNorm ξ.determinant ω
    (determinantSequenceEquiv W).toLinearMap (1 ⊗ₜ[K] (w ⊗ₜ[K] q))
  rw [LinearMap.baseChange_tmul, hn] at hb
  change pE ≤ a * (pW * pQ) at hb
  have hprod := mul_le_mul hW hQ
    ((ξ.quotient W).majorantDiscrepancy_pos hN ω).le
    (div_nonneg ((η.restrict W).determinant.norm_nonneg ω _) hpW.le)
  calc
    _ ≤ (mW / pW) * (mQ / pQ) / a := (div_le_div_iff_of_pos_right ha0).2 hprod
    _ ≤ (mW * mQ) / pE := div_normRatios_le_targetRatio mW mQ pW pQ pE a
      hpW hpQ hpE ha0 ((η.restrict W).determinant.norm_nonneg ω _)
      ((η.quotient W).determinant.norm_nonneg ω _) hb
    _ = mE / pE := by rw [hi]
    _ = _ := ξ.determinantRatio_eq_of_nonzero η ω
      (1 ⊗ₜ[K] determinantSequenceEquiv W (w ⊗ₜ[K] q)) hcE

/-- The actual majorant infimum proves the capital-discrepancy operator
bound for arbitrary original norms, including rank zero. -/
theorem majorantDiscrepancy_restrict_mul_quotient_div_le_operatorNorm
    (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (W : Submodule K E) (ω : S.Ω) :
    (ξ.restrict W).majorantDiscrepancy hN ω *
        (ξ.quotient W).majorantDiscrepancy hN ω / ξ.majorantDiscrepancy hN ω ≤
      ((ξ.restrict W).determinant.injectiveTensorPair
        (ξ.quotient W).determinant).operatorNorm
        ξ.determinant ω (determinantSequenceEquiv W).toLinearMap := by
  let a := ((ξ.restrict W).determinant.injectiveTensorPair
    (ξ.quotient W).determinant).operatorNorm
    ξ.determinant ω (determinantSequenceEquiv W).toLinearMap
  have ha : 0 < a := ξ.determinantSequence_operatorNorm_pos_of_equiv W ω
  have h := ξ.le_majorantDiscrepancy_of_forall_majorant hN ω
    ((ξ.restrict W).majorantDiscrepancy hN ω *
      (ξ.quotient W).majorantDiscrepancy hN ω / a)
    (fun η he hl =>
      ξ.majorantDiscrepancy_restrict_mul_quotient_div_le_majorantRatio η hN W ω he hl)
  apply (div_le_iff₀ (ξ.majorantDiscrepancy_pos hN ω)).2
  exact ((div_le_iff₀ ha).1 h).trans_eq (mul_comm (ξ.majorantDiscrepancy hN ω) a)

/-- End-space capital discrepancies multiply to at most the middle one
for arbitrary original fibre norms. -/
theorem majorantDiscrepancy_restrict_mul_quotient_le (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (W : Submodule K E) (ω : S.Ω) :
    (ξ.restrict W).majorantDiscrepancy hN ω *
      (ξ.quotient W).majorantDiscrepancy hN ω ≤ ξ.majorantDiscrepancy hN ω :=
  (div_le_one (ξ.majorantDiscrepancy_pos hN ω)).1
    ((ξ.majorantDiscrepancy_restrict_mul_quotient_div_le_operatorNorm hN W ω).trans
      (ξ.determinantSequence_operatorNorm_le_one W ω))

theorem majorantDiscrepancy_restrict_le (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (W : Submodule K E) (ω : S.Ω) :
    (ξ.restrict W).majorantDiscrepancy hN ω ≤ ξ.majorantDiscrepancy hN ω := by
  calc
    _ = (ξ.restrict W).majorantDiscrepancy hN ω * 1 := (mul_one _).symm
    _ ≤ (ξ.restrict W).majorantDiscrepancy hN ω *
        (ξ.quotient W).majorantDiscrepancy hN ω :=
      mul_le_mul_of_nonneg_left ((ξ.quotient W).one_le_majorantDiscrepancy hN ω)
        ((ξ.restrict W).majorantDiscrepancy_pos hN ω).le
    _ ≤ ξ.majorantDiscrepancy hN ω :=
      ξ.majorantDiscrepancy_restrict_mul_quotient_le hN W ω

theorem majorantDiscrepancy_quotient_le (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (W : Submodule K E) (ω : S.Ω) :
    (ξ.quotient W).majorantDiscrepancy hN ω ≤ ξ.majorantDiscrepancy hN ω := by
  calc
    _ = 1 * (ξ.quotient W).majorantDiscrepancy hN ω := (one_mul _).symm
    _ ≤ (ξ.restrict W).majorantDiscrepancy hN ω *
        (ξ.quotient W).majorantDiscrepancy hN ω :=
      mul_le_mul_of_nonneg_right ((ξ.restrict W).one_le_majorantDiscrepancy hN ω)
        ((ξ.quotient W).majorantDiscrepancy_pos hN ω).le
    _ ≤ ξ.majorantDiscrepancy hN ω :=
      ξ.majorantDiscrepancy_restrict_mul_quotient_le hN W ω

end

end ArakelovGeometry.NormFamily
