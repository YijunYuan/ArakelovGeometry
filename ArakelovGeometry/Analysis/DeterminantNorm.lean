/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.TensorNorm
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite

/-!
# Determinant norms and nearly optimal bases

Local determinant estimates over complete valued fields, including trivial
valuations. The separated projective tensor norm supplies actual bounds for
multilinear maps; no determinant norm or optimal basis is assumed.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

variable {L : Type*} [NormedField L] [CompleteSpace L]

/-- Multilinear maps on finitely many finite-dimensional spaces have product
bounds over every complete valued field, including trivial valuations. -/
theorem multilinearMap_exists_pos_bound {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace L (E i)]
    [∀ i, FiniteDimensional L (E i)] {W : Type*} [SeminormedAddCommGroup W]
    [NormedSpace L W] (f : MultilinearMap L E W) :
    ∃ C > 0, ∀ x : ∀ i, E i, ‖f x‖ ≤ C * ∏ i, ‖x i‖ := by
  let p := PiTensorProduct.projectiveSeminorm (𝕜 := L) (E := E)
  let tensorNormed : NormedAddCommGroup (⨂[L] i, E i) :=
    (⟨p.toAddGroupSeminorm, fun x ↦ (projectiveSeminorm_eq_zero_iff x).mp⟩ :
      AddGroupNorm (⨂[L] i, E i)).toNormedAddCommGroup
  let : SeminormedAddCommGroup (⨂[L] i, E i) := tensorNormed.toSeminormedAddCommGroup
  let : NormedSpace L (⨂[L] i, E i) := ⟨fun a x ↦ (map_smul_eq_mul p a x).le⟩
  obtain ⟨C, hC, h⟩ := linearMap_exists_pos_bound (L := L) (V := ⨂[L] i, E i)
    (W := W) (PiTensorProduct.lift f)
  refine ⟨C, hC, fun x ↦ ?_⟩
  calc
    ‖f x‖ = ‖PiTensorProduct.lift f (⨂ₜ[L] i, x i)‖ := by rw [PiTensorProduct.lift.tprod]
    _ ≤ C * p (⨂ₜ[L] i, x i) := h _
    _ ≤ C * ∏ i, ‖x i‖ := mul_le_mul_of_nonneg_left
      (PiTensorProduct.projectiveSeminorm_tprod_le x) hC.le

/-- Product dual evaluations are bounded by the genuine injective seminorm
times the product of the factor dual norms. -/
theorem norm_tensorDualEval_le_injective {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace L (E i)]
    [∀ i, FiniteDimensional L (E i)] (φ : ∀ i, E i →ₗ[L] L) (z : ⨂[L] i, E i) :
    ‖tensorDualEval φ z‖ ≤ injectiveTensorSeminorm z *
      ∏ i, linearMapOperatorSeminorm (φ i) := by
  by_cases hD : ∏ i, linearMapOperatorSeminorm (φ i) = 0
  · simpa only [hD, zero_mul, mul_zero] using norm_tensorDualEval_le_projective φ z
  have hp : 0 < ∏ i, linearMapOperatorSeminorm (φ i) :=
    lt_of_le_of_ne (Finset.prod_nonneg fun _ _ ↦ apply_nonneg _ _) (Ne.symm hD)
  apply (div_le_iff₀ hp).mp
  simpa only [tensorDualRatioSeminorm_apply] using tensorDualRatioSeminorm_le_injective φ z

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace L E] [FiniteDimensional L E]

private def determinantRatio (b : Module.Basis ι L E) (x : ι → E) : ℝ :=
  ‖b.det x‖ / ∏ i, ‖x i‖

private theorem determinantRatio_bddAbove (b : Module.Basis ι L E) :
    BddAbove (Set.range (determinantRatio b)) := by
  obtain ⟨C, hC, h⟩ := multilinearMap_exists_pos_bound b.det.toMultilinearMap
  refine ⟨C, ?_⟩
  rintro _ ⟨x, rfl⟩
  by_cases hx : ∏ i, ‖x i‖ = 0
  · simpa only [determinantRatio, hx, div_zero] using hC.le
  have hp : 0 < ∏ i, ‖x i‖ :=
    lt_of_le_of_ne (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) (Ne.symm hx)
  exact (div_le_iff₀ hp).mpr (h x)

private def determinantRatioSup (b : Module.Basis ι L E) : ℝ :=
  sSup (Set.range (determinantRatio b))

private theorem determinantRatio_le_sup (b : Module.Basis ι L E) (x : ι → E) :
    determinantRatio b x ≤ determinantRatioSup b :=
  le_csSup (determinantRatio_bddAbove b) ⟨x, rfl⟩

private theorem determinantRatioSup_pos (b : Module.Basis ι L E) :
    0 < determinantRatioSup b := by
  have hb : 0 < determinantRatio b b := by
    rw [determinantRatio, b.det_self, norm_one]
    exact div_pos zero_lt_one (Finset.prod_pos fun i _ ↦ norm_pos_iff.mpr (b.ne_zero i))
  exact hb.trans_le (determinantRatio_le_sup b b)

private theorem norm_det_le_sup_mul_prod (b : Module.Basis ι L E) (x : ι → E) :
    ‖b.det x‖ ≤ determinantRatioSup b * ∏ i, ‖x i‖ := by
  by_cases hx : ∏ i, ‖x i‖ = 0
  · obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hx
    have hdet := b.det.toMultilinearMap.map_coord_zero i (norm_eq_zero.mp hi)
    change b.det x = 0 at hdet
    simp only [hdet, norm_zero, hx, mul_zero, le_refl]
  have hp : 0 < ∏ i, ‖x i‖ :=
    lt_of_le_of_ne (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) (Ne.symm hx)
  exact (div_le_iff₀ hp).mp (determinantRatio_le_sup b x)

omit [Fintype ι] [DecidableEq ι] in
/-- Every finite-dimensional normed space over a complete valued field has
a basis whose vector and dual-coordinate norms have products between one and
`α⁻¹`. No ultrametric hypothesis on the vector norm is required. -/
theorem exists_basis_mul_dual_norm_le [Finite ι] (b : Module.Basis ι L E)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ e : Module.Basis ι L E, ∀ i,
      1 ≤ ‖e i‖ * linearMapOperatorSeminorm (e.coord i) ∧
      ‖e i‖ * linearMapOperatorSeminorm (e.coord i) ≤ α⁻¹ := by
  classical
  let := Fintype.ofFinite ι
  have hS := determinantRatioSup_pos b
  obtain ⟨_, ⟨v, rfl⟩, hv⟩ := exists_lt_of_lt_csSup (Set.range_nonempty (determinantRatio b))
    (show α * determinantRatioSup b < determinantRatioSup b from
      mul_lt_of_lt_one_left hS hα1)
  have hvpos : 0 < determinantRatio b v := (mul_pos hα hS).trans hv
  have hd : b.det v ≠ 0 := by
    intro hd
    simp only [determinantRatio, hd, norm_zero, zero_div] at hvpos
    exact (lt_irrefl 0) hvpos
  obtain ⟨hli, hsp⟩ := b.is_basis_iff_det.mpr (IsUnit.mk0 _ hd)
  let e := Module.Basis.mk hli hsp.ge
  have he (i : ι) : e i = v i := Module.Basis.mk_apply hli hsp.ge i
  have hD : 0 < ‖b.det v‖ := norm_pos_iff.mpr hd
  have hP : 0 < ∏ j, ‖v j‖ :=
    Finset.prod_pos fun j _ ↦ norm_pos_iff.mpr (by rw [← he j]; exact e.ne_zero j)
  have hSP : α * determinantRatioSup b * (∏ j, ‖v j‖) < ‖b.det v‖ :=
    (lt_div_iff₀ hP).mp hv
  refine ⟨e, fun i ↦ ⟨?_, ?_⟩⟩
  · simpa [Module.Basis.coord_apply, mul_comm] using norm_linearMap_apply_le (e.coord i) (e i)
  · let P := ∏ j ∈ Finset.univ.erase i, ‖v j‖
    have hP0 : 0 ≤ P := Finset.prod_nonneg fun _ _ ↦ norm_nonneg _
    have hc : linearMapOperatorSeminorm (e.coord i) ≤
        determinantRatioSup b * P / ‖b.det v‖ := by
      apply linearMapOperatorSeminorm_le _ (div_nonneg (mul_nonneg hS.le hP0) hD.le)
      intro x
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hD).2
      have hcoord : ‖b.det v‖ * ‖e.coord i x‖ = ‖b.det (Function.update v i x)‖ := by
        have h := congrArg norm
          (LinearMap.congr_fun (b.det_smul_mk_coord_eq_det_update hli hsp.ge i) x)
        change ‖b.det v * e.coord i x‖ = ‖b.det (Function.update v i x)‖ at h
        rwa [norm_mul] at h
      have hpupdate : (∏ j, ‖Function.update v i x j‖) = ‖x‖ * P := by
        simp only [Function.apply_update (fun _ : ι ↦ (norm : E → ℝ)),
          Finset.prod_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase, P]
      have h := norm_det_le_sup_mul_prod b (Function.update v i x)
      rw [← hcoord, hpupdate] at h
      simpa only [mul_assoc, mul_left_comm, mul_comm] using h
    calc
      ‖e i‖ * linearMapOperatorSeminorm (e.coord i) ≤
          ‖e i‖ * (determinantRatioSup b * P / ‖b.det v‖) :=
        mul_le_mul_of_nonneg_left hc (norm_nonneg _)
      _ = determinantRatioSup b * (∏ j, ‖v j‖) / ‖b.det v‖ := by
        rw [he]
        rw [← Finset.mul_prod_erase Finset.univ (fun j ↦ ‖v j‖) (Finset.mem_univ i)]
        dsimp [P]
        ring
      _ ≤ α⁻¹ := by
        apply (div_le_iff₀ hD).2
        apply (mul_le_mul_iff_right₀ hα).mp
        calc
          α * (determinantRatioSup b * ∏ j, ‖v j‖) ≤ ‖b.det v‖ := by
            simpa only [mul_assoc] using hSP.le
          _ = α * (α⁻¹ * ‖b.det v‖) := by
            rw [← mul_assoc, mul_inv_cancel₀ hα.ne', one_mul]

omit [Fintype ι] [DecidableEq ι] in
/-- The nearly optimal basis theorem with its canonical finite-rank index. -/
theorem exists_finBasis_mul_dual_norm_le {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ e : Module.Basis (Fin (Module.finrank L E)) L E, ∀ i,
      1 ≤ ‖e i‖ * linearMapOperatorSeminorm (e.coord i) ∧
      ‖e i‖ * linearMapOperatorSeminorm (e.coord i) ≤ α⁻¹ :=
  exists_basis_mul_dual_norm_le (Module.finBasis L E) hα hα1

omit [CompleteSpace L] [FiniteDimensional L E] in
private theorem exists_det_eq_prod_norm_lt_of_ratioSup [Nonempty ι]
    (b : Module.Basis ι L E) (a : L) {c : ℝ} (hcpos : 0 < c)
    (hc : ‖a‖ < determinantRatioSup b * c) :
    ∃ x : ι → E, b.det x = a ∧ (∏ i, ‖x i‖) < c := by
  classical
  by_cases ha : a = 0
  · refine ⟨fun _ ↦ 0, ?_, ?_⟩
    · change b.det (0 : ι → E) = a
      rw [ha, b.det.map_zero]
    · simpa using hcpos
  have hlt : ‖a‖ / c < determinantRatioSup b := by
    apply (div_lt_iff₀ hcpos).2
    exact hc
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ :=
    exists_lt_of_lt_csSup (Set.range_nonempty (determinantRatio b)) hlt
  have hxpos : 0 < determinantRatio b x :=
    (div_pos (norm_pos_iff.mpr ha) hcpos).trans hx
  have hd : b.det x ≠ 0 := by
    intro hd
    simp only [determinantRatio, hd, norm_zero, zero_div] at hxpos
    exact (lt_irrefl 0) hxpos
  have hP : 0 < ∏ j, ‖x j‖ := by
    exact (div_pos_iff.mp hxpos).resolve_right (fun h ↦ (norm_nonneg _).not_gt h.1) |>.2
  let i : ι := Classical.arbitrary ι
  refine ⟨Function.update x i ((a / b.det x) • x i), ?_, ?_⟩
  · rw [b.det.map_update_smul, Function.update_eq_self, smul_eq_mul, div_mul_cancel₀ _ hd]
  · have hpupdate : (∏ j, ‖Function.update x i ((a / b.det x) • x i) j‖) =
        ‖a / b.det x‖ * ∏ j, ‖x j‖ := by
      simp only [Function.apply_update (fun _ : ι ↦ (norm : E → ℝ)),
        Finset.prod_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase,
        norm_smul]
      rw [mul_assoc, Finset.mul_prod_erase Finset.univ (fun j ↦ ‖x j‖) (Finset.mem_univ i)]
    rw [hpupdate, norm_div, div_mul_eq_mul_div]
    apply (div_lt_iff₀ (norm_pos_iff.mpr hd)).2
    have h := (div_lt_div_iff₀ hcpos hP).mp hx
    simpa only [determinantRatio, mul_comm] using h

/-- Every determinant coefficient of a tensor admits a single tuple with
the same determinant and product cost arbitrarily close above that tensor's
projective norm. Positive rank is essential for scaling one factor. -/
theorem exists_det_eq_prod_norm_lt_of_projective [Nonempty ι]
    (b : Module.Basis ι L E) (z : ⨂[L] (_ : ι), E) {c : ℝ}
    (hc : PiTensorProduct.projectiveSeminorm z < c) :
    ∃ x : ι → E, b.det x = PiTensorProduct.lift b.det.toMultilinearMap z ∧
      (∏ i, ‖x i‖) < c := by
  have hS := determinantRatioSup_pos b
  apply exists_det_eq_prod_norm_lt_of_ratioSup b _ ((apply_nonneg _ z).trans_lt hc)
  apply lt_of_le_of_lt _ (mul_lt_mul_of_pos_left hc hS)
  apply norm_linearMap_le_projective_of_tprod_le
    (PiTensorProduct.lift b.det.toMultilinearMap) hS.le
  intro x
  simpa only [PiTensorProduct.lift.tprod, AlternatingMap.coe_multilinearMap] using
    norm_det_le_sup_mul_prod b x

/-- The quotient of the projective tensor norm by a determinant coordinate
is exactly the infimum of single-tuple product costs. This is the local
positive-rank determinant formula, expressed in an arbitrary basis. -/
theorem sInf_prod_norm_det_eq_sInf_projective [Nonempty ι]
    (b : Module.Basis ι L E) (a : L) :
    sInf {c : ℝ | ∃ x : ι → E, b.det x = a ∧ (∏ i, ‖x i‖) = c} =
      sInf {c : ℝ | ∃ z : ⨂[L] (_ : ι), E,
        PiTensorProduct.lift b.det.toMultilinearMap z = a ∧
          PiTensorProduct.projectiveSeminorm z = c} := by
  let f := PiTensorProduct.lift b.det.toMultilinearMap
  have hA : BddBelow {c : ℝ | ∃ x : ι → E, b.det x = a ∧ (∏ i, ‖x i‖) = c} := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, _, rfl⟩
    exact Finset.prod_nonneg fun _ _ ↦ norm_nonneg _
  have hB : BddBelow {c : ℝ | ∃ z : ⨂[L] (_ : ι), E,
      f z = a ∧ PiTensorProduct.projectiveSeminorm z = c} := by
    refine ⟨0, ?_⟩
    rintro _ ⟨z, _, rfl⟩
    exact apply_nonneg _ _
  have hBne : {c : ℝ | ∃ z : ⨂[L] (_ : ι), E,
      f z = a ∧ PiTensorProduct.projectiveSeminorm z = c}.Nonempty := by
    refine ⟨_, a • (⨂ₜ[L] i, b i), ?_, rfl⟩
    simp only [f, map_smul, PiTensorProduct.lift.tprod, AlternatingMap.coe_multilinearMap,
      b.det_self, smul_eq_mul, mul_one]
  have hAne : {c : ℝ | ∃ x : ι → E, b.det x = a ∧ (∏ i, ‖x i‖) = c}.Nonempty := by
    obtain ⟨_, z, hz, rfl⟩ := hBne
    obtain ⟨x, hx, _⟩ := exists_det_eq_prod_norm_lt_of_projective b z
      (lt_add_of_pos_right _ zero_lt_one)
    exact ⟨_, x, hx.trans hz, rfl⟩
  apply le_antisymm
  · apply le_csInf hBne
    rintro _ ⟨z, hz, rfl⟩
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨x, hx, hc⟩ := exists_det_eq_prod_norm_lt_of_projective b z
      (lt_add_of_pos_right _ hε)
    exact (csInf_le hA ⟨x, hx.trans hz, rfl⟩).trans hc.le
  · apply le_csInf hAne
    rintro _ ⟨x, hx, rfl⟩
    apply (csInf_le hB (show ∃ z, f z = a ∧ PiTensorProduct.projectiveSeminorm z =
      PiTensorProduct.projectiveSeminorm (⨂ₜ[L] i, x i) from ⟨_, ?_, rfl⟩)).trans
      (PiTensorProduct.projectiveSeminorm_tprod_le x)
    simpa only [f, PiTensorProduct.lift.tprod, AlternatingMap.coe_multilinearMap] using hx

omit [CompleteSpace L] [Fintype ι] [DecidableEq ι] in
/-- A basis determinant is a coordinate on the actual top exterior power,
including the zeroth exterior power in dimension zero. -/
theorem determinantCoordinate_injective {n : ℕ} (b : Module.Basis (Fin n) L E) :
    Function.Injective (exteriorPower.alternatingMapLinearEquiv b.det) := by
  have hdim : Module.finrank L (⋀[L]^n E) = Module.finrank L L := by
    rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis b, Fintype.card_fin,
      Nat.choose_self, Module.finrank_self]
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr
  intro a
  refine ⟨a • exteriorPower.ιMulti L n b, ?_⟩
  rw [map_smul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    b.det_self, smul_eq_mul, mul_one]

omit [DecidableEq ι] in
/-- A linear map from a finite tensor power to an ultrametric normed target
is contractive for the injective norm if it satisfies the pure-tensor product
bound. The factor norm itself need not be ultrametric. -/
theorem norm_linearMap_le_injective_of_ultrametric {W : Type*}
    [SeminormedAddCommGroup W] [NormedSpace L W]
    (f : (⨂[L] (_ : ι), E) →ₗ[L] W)
    (hW : ∀ x y : W, ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (hf : ∀ x : ι → E, ‖f (⨂ₜ[L] i, x i)‖ ≤ ∏ i, ‖x i‖)
    (z : ⨂[L] (_ : ι), E) : ‖f z‖ ≤ injectiveTensorSeminorm z := by
  classical
  have hαbound (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
      ‖f z‖ ≤ injectiveTensorSeminorm z * α⁻¹ ^ Fintype.card ι := by
    obtain ⟨e, he⟩ := exists_finBasis_mul_dual_norm_le (L := L) (E := E) hα hα1
    let B := Basis.piTensorProduct (fun _ : ι ↦ e)
    have hC : 0 ≤ injectiveTensorSeminorm z * α⁻¹ ^ Fintype.card ι :=
      mul_nonneg (apply_nonneg _ _) (pow_nonneg (inv_nonneg.mpr hα.le) _)
    calc
      ‖f z‖ = ‖∑ p, (B.repr z) p • f (B p)‖ := by
        simpa only [map_sum, map_smul] using congrArg norm (congrArg f (B.sum_repr z)).symm
      _ ≤ injectiveTensorSeminorm z * α⁻¹ ^ Fintype.card ι := by
        have : IsUltrametricDist W :=
          IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr hW
        apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC
        intro p _
        have hp := norm_tensorDualEval_le_injective (fun i : ι ↦ e.coord (p i)) z
        rw [tensorDualEval_coord] at hp
        change ‖(B.repr z) p‖ ≤ injectiveTensorSeminorm z *
          ∏ i, linearMapOperatorSeminorm (e.coord (p i)) at hp
        have hb : ‖f (B p)‖ ≤ ∏ i, ‖e (p i)‖ := by
          simpa only [B, Basis.piTensorProduct_apply] using hf (fun i ↦ e (p i))
        calc
          ‖(B.repr z) p • f (B p)‖ = ‖(B.repr z) p‖ * ‖f (B p)‖ := norm_smul _ _
          _ ≤ (injectiveTensorSeminorm z * ∏ i, linearMapOperatorSeminorm (e.coord (p i))) *
              ∏ i, ‖e (p i)‖ := mul_le_mul hp hb (norm_nonneg _) (by positivity)
          _ = injectiveTensorSeminorm z *
              ∏ i, ‖e (p i)‖ * linearMapOperatorSeminorm (e.coord (p i)) := by
            rw [Finset.prod_mul_distrib]
            ring
          _ ≤ injectiveTensorSeminorm z * ∏ _ : ι, α⁻¹ := by
            apply mul_le_mul_of_nonneg_left _ (apply_nonneg _ _)
            exact Finset.prod_le_prod₀ (fun _ _ ↦ mul_nonneg (norm_nonneg _) (apply_nonneg _ _))
              (fun i _ ↦ (he (p i)).2)
          _ = injectiveTensorSeminorm z * α⁻¹ ^ Fintype.card ι := by
            rw [Finset.prod_const, Finset.card_univ]
  have hlim : Filter.Tendsto (fun α : ℝ ↦ injectiveTensorSeminorm z * α⁻¹ ^ Fintype.card ι)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (injectiveTensorSeminorm z)) := by
    have hc : ContinuousAt (fun α : ℝ ↦ injectiveTensorSeminorm z * α⁻¹ ^ Fintype.card ι) 1 := by
      exact continuousAt_const.mul ((continuousAt_id.inv₀ one_ne_zero).pow _)
    simpa only [inv_one, one_pow, mul_one] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (zero_lt_one : (0 : ℝ) < 1))]
    with α hα1 hα
  exact hαbound α hα hα1

omit [DecidableEq ι] in
/-- The injective contraction principle also applies directly to seminorms
on arbitrary linear targets. -/
theorem seminorm_linearMap_le_injective_of_ultrametric {W : Type*}
    [AddCommGroup W] [Module L W] (p : Seminorm L W)
    (f : (⨂[L] (_ : ι), E) →ₗ[L] W)
    (hp : ∀ x y, p (x + y) ≤ max (p x) (p y))
    (hf : ∀ x : ι → E, p (f (⨂ₜ[L] i, x i)) ≤ ∏ i, ‖x i‖)
    (z : ⨂[L] (_ : ι), E) : p (f z) ≤ injectiveTensorSeminorm z := by
  let : SeminormedAddCommGroup W := p.toAddGroupSeminorm.toSeminormedAddCommGroup
  let : NormedSpace L W := ⟨fun a x ↦ (map_smul_eq_mul p a x).le⟩
  exact norm_linearMap_le_injective_of_ultrametric f hp hf z

private theorem sInf_projective_det_eq_norm_div [Nonempty ι]
    (b : Module.Basis ι L E) (a : L) :
    sInf {c : ℝ | ∃ z : ⨂[L] (_ : ι), E,
      PiTensorProduct.lift b.det.toMultilinearMap z = a ∧
        PiTensorProduct.projectiveSeminorm z = c} = ‖a‖ / determinantRatioSup b := by
  classical
  rw [← sInf_prod_norm_det_eq_sInf_projective]
  have hD := determinantRatioSup_pos b
  have hne : {c : ℝ | ∃ x : ι → E, b.det x = a ∧ (∏ i, ‖x i‖) = c}.Nonempty := by
    let i : ι := Classical.arbitrary ι
    refine ⟨_, Function.update b i (a • b i), ?_, rfl⟩
    rw [b.det.map_update_smul, Function.update_eq_self, b.det_self, smul_eq_mul, mul_one]
  have hb : BddBelow {c : ℝ | ∃ x : ι → E, b.det x = a ∧ (∏ i, ‖x i‖) = c} := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, _, rfl⟩
    exact Finset.prod_nonneg fun _ _ ↦ norm_nonneg _
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hc : 0 < ‖a‖ / determinantRatioSup b + ε :=
      add_pos_of_nonneg_of_pos (div_nonneg (norm_nonneg _) hD.le) hε
    have hprod : ‖a‖ < determinantRatioSup b * (‖a‖ / determinantRatioSup b + ε) := by
      rw [mul_add, mul_div_cancel₀ _ hD.ne']
      exact lt_add_of_pos_right _ (mul_pos hD hε)
    obtain ⟨x, hx, hcost⟩ := exists_det_eq_prod_norm_lt_of_ratioSup b a hc hprod
    exact (csInf_le hb ⟨x, hx, rfl⟩).trans hcost.le
  · apply le_csInf hne
    rintro _ ⟨x, hx, rfl⟩
    apply (div_le_iff₀ hD).mpr
    simpa only [hx, mul_comm] using norm_det_le_sup_mul_prod b x

/-- Over a non-Archimedean field the projective and injective tensor
quotients have the same determinant coordinate norm. -/
theorem determinantCoordinate_projective_injective_quotient_eq [Nonempty ι]
    (hL : ∀ a b : L, ‖a + b‖ ≤ max ‖a‖ ‖b‖) (b : Module.Basis ι L E) (a : L) :
    sInf {c : ℝ | ∃ z : ⨂[L] (_ : ι), E,
      PiTensorProduct.lift b.det.toMultilinearMap z = a ∧
        PiTensorProduct.projectiveSeminorm z = c} =
      sInf {c : ℝ | ∃ z : ⨂[L] (_ : ι), E,
        PiTensorProduct.lift b.det.toMultilinearMap z = a ∧ injectiveTensorSeminorm z = c} := by
  let f := PiTensorProduct.lift b.det.toMultilinearMap
  have hD := determinantRatioSup_pos b
  let p : Seminorm L L :=
    NNReal.mk (determinantRatioSup b)⁻¹ (inv_nonneg.mpr hD.le) • normSeminorm L L
  have hpap (v : L) : p v = ‖v‖ / determinantRatioSup b := by
    change (determinantRatioSup b)⁻¹ * ‖v‖ = _
    rw [div_eq_mul_inv, mul_comm]
  have hp : ∀ v w, p (v + w) ≤ max (p v) (p w) := by
    intro v w
    simp only [hpap]
    rw [max_div_div_right hD.le]
    exact div_le_div_of_nonneg_right (hL v w) hD.le
  have hf : ∀ x : ι → E, p (f (⨂ₜ[L] i, x i)) ≤ ∏ i, ‖x i‖ := by
    intro x
    rw [hpap]
    apply (div_le_iff₀ hD).mpr
    simpa only [f, PiTensorProduct.lift.tprod, AlternatingMap.coe_multilinearMap, mul_comm]
      using norm_det_le_sup_mul_prod b x
  have hcontract (z : ⨂[L] (_ : ι), E) :
      ‖f z‖ / determinantRatioSup b ≤ injectiveTensorSeminorm z := by
    rw [← hpap]
    exact seminorm_linearMap_le_injective_of_ultrametric p f hp hf z
  have hsurj : ∃ z : ⨂[L] (_ : ι), E, f z = a := by
    refine ⟨a • (⨂ₜ[L] i, b i), ?_⟩
    simp only [f, map_smul, PiTensorProduct.lift.tprod, AlternatingMap.coe_multilinearMap,
      b.det_self, smul_eq_mul, mul_one]
  have hπne : {c : ℝ | ∃ z : ⨂[L] (_ : ι), E,
      f z = a ∧ PiTensorProduct.projectiveSeminorm z = c}.Nonempty := by
    obtain ⟨z, hz⟩ := hsurj
    exact ⟨_, z, hz, rfl⟩
  have hεne : {c : ℝ | ∃ z : ⨂[L] (_ : ι), E,
      f z = a ∧ injectiveTensorSeminorm z = c}.Nonempty := by
    obtain ⟨z, hz⟩ := hsurj
    exact ⟨_, z, hz, rfl⟩
  have hεb : BddBelow {c : ℝ | ∃ z : ⨂[L] (_ : ι), E,
      f z = a ∧ injectiveTensorSeminorm z = c} := by
    refine ⟨0, ?_⟩
    rintro _ ⟨z, _, rfl⟩
    exact apply_nonneg _ _
  apply le_antisymm
  · rw [sInf_projective_det_eq_norm_div]
    apply le_csInf hεne
    rintro _ ⟨z, hz, rfl⟩
    rw [← hz]
    exact hcontract z
  · apply le_csInf hπne
    rintro _ ⟨z, hz, rfl⟩
    exact (csInf_le hεb ⟨z, hz, rfl⟩).trans (injectiveTensorSeminorm_le_projective z)

omit [Fintype ι] [DecidableEq ι] in
/-- The projective and genuine injective tensor quotients on the actual top
exterior power agree over every complete non-Archimedean valued field.
No ultrametricity of the original vector norm is assumed, and rank zero is included. -/
theorem determinant_projective_injective_quotient_eq {n : ℕ}
    (hL : ∀ a b : L, ‖a + b‖ ≤ max ‖a‖ ‖b‖) (b : Module.Basis (Fin n) L E)
    (η : ⋀[L]^n E) :
    sInf {c : ℝ | ∃ z : ⨂[L] (_ : Fin n), E,
      PiTensorProduct.lift (exteriorPower.ιMulti L n).toMultilinearMap z = η ∧
        PiTensorProduct.projectiveSeminorm z = c} =
      sInf {c : ℝ | ∃ z : ⨂[L] (_ : Fin n), E,
        PiTensorProduct.lift (exteriorPower.ιMulti L n).toMultilinearMap z = η ∧
          injectiveTensorSeminorm z = c} := by
  by_cases hn : n = 0
  · subst n
    simp_rw [projectiveSeminorm_isEmpty, injectiveTensorSeminorm_isEmpty]
  let : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  let g := exteriorPower.alternatingMapLinearEquiv b.det
  let q := PiTensorProduct.lift (exteriorPower.ιMulti L n (M := E)).toMultilinearMap
  let f := PiTensorProduct.lift b.det.toMultilinearMap
  have hg : g.comp q = f := by
    apply PiTensorProduct.ext
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, q, f, g,
      PiTensorProduct.lift.tprod, AlternatingMap.coe_multilinearMap,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  have hfibre (z : ⨂[L] (_ : Fin n), E) : f z = g η ↔ q z = η := by
    rw [← hg, LinearMap.comp_apply]
    exact (determinantCoordinate_injective b).eq_iff
  have h := determinantCoordinate_projective_injective_quotient_eq hL b (g η)
  change sInf {c : ℝ | ∃ z, f z = g η ∧ PiTensorProduct.projectiveSeminorm z = c} =
    sInf {c : ℝ | ∃ z, f z = g η ∧ injectiveTensorSeminorm z = c} at h
  simp_rw [hfibre] at h
  exact h

omit [Fintype ι] [DecidableEq ι] in
/-- The local projective quotient on the actual positive-rank determinant
line is the infimum over single wedge presentations. -/
theorem determinant_projective_quotient_eq_sInf_ιMulti {n : ℕ} (hn : 0 < n)
    (b : Module.Basis (Fin n) L E) (η : ⋀[L]^n E) :
    sInf {c : ℝ | ∃ z : ⨂[L] (_ : Fin n), E,
      PiTensorProduct.lift (exteriorPower.ιMulti L n).toMultilinearMap z = η ∧
        PiTensorProduct.projectiveSeminorm z = c} =
      sInf {c : ℝ | ∃ x : Fin n → E,
        exteriorPower.ιMulti L n x = η ∧ (∏ i, ‖x i‖) = c} := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let g := exteriorPower.alternatingMapLinearEquiv b.det
  let q := PiTensorProduct.lift (exteriorPower.ιMulti L n (M := E)).toMultilinearMap
  let f := PiTensorProduct.lift b.det.toMultilinearMap
  have hg : g.comp q = f := by
    apply PiTensorProduct.ext
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, q, f, g,
      PiTensorProduct.lift.tprod, AlternatingMap.coe_multilinearMap,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  have hfibre (z : ⨂[L] (_ : Fin n), E) : f z = g η ↔ q z = η := by
    rw [← hg, LinearMap.comp_apply]
    exact (determinantCoordinate_injective b).eq_iff
  have hwedge (x : Fin n → E) : b.det x = g η ↔ exteriorPower.ιMulti L n x = η := by
    rw [← exteriorPower.alternatingMapLinearEquiv_apply_ιMulti b.det]
    exact (determinantCoordinate_injective b).eq_iff
  have h := sInf_prod_norm_det_eq_sInf_projective b (g η)
  change sInf {c : ℝ | ∃ x, b.det x = g η ∧ (∏ i, ‖x i‖) = c} =
    sInf {c : ℝ | ∃ z, f z = g η ∧ PiTensorProduct.projectiveSeminorm z = c} at h
  simp_rw [hwedge, hfibre] at h
  exact h.symm

end

end ArakelovGeometry
