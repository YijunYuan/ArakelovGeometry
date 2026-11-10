/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionIsomorphismDeterminant
import ArakelovGeometry.NumberTheory.AdelicVectorBundleNumberFieldNormalization
import ArakelovGeometry.NumberTheory.NormalizedNumberFieldIntegralComparison
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldNormalizationHermitian
import ArakelovGeometry.AdelicVectorBundle.DegreeDeterminant

/-!
# Determinant norms and degrees under actual number-field normalization

The actual projective determinant quotient is characterized by scalar-weighted
wedge costs. Transporting those costs by the actual positive normalization
power preserves the determinant norm and its weighted logarithmic integral.
-/

open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

section DeterminantPower

variable {K E A C : Type*} [Field K] [NormedField A] [NormedField C]
  [Algebra K A] [Algebra K C] [AddCommGroup E] [Module K E]
  (τ : A ≃+* C)
  (p : Seminorm A (A ⊗[K] E))
  (pd : Seminorm A (A ⊗[K] (⋀[K]^(Module.finrank K E) E)))
  (q : Seminorm C (C ⊗[K] E))
  (qd : Seminorm C (C ⊗[K] (⋀[K]^(Module.finrank K E) E)))

local instance numberFieldDeterminant_forwardInverse :
    RingHomInvPair (τ : A →+* C) (τ.symm : C →+* A) :=
  RingHomInvPair.of_ringEquiv τ
local instance numberFieldDeterminant_reverseInverse :
    RingHomInvPair (τ.symm : C →+* A) (τ : A →+* C) :=
  RingHomInvPair.of_ringEquiv_symm τ

/-- Scalar-weighted wedge bounds and actual quotient approximation transport
by every positive scalar/vector norm power, including the empty wedge. -/
theorem completedDeterminantSeminorm_norm_rpow
    (e : (A ⊗[K] E) ≃ₛₗ[(τ : A →+* C)] (C ⊗[K] E))
    (θ : ℝ) (hθ : 0 < θ)
    (hτ : ∀ a, ‖τ a‖ = ‖a‖ ^ θ)
    (he : ∀ v, q (e v) = p v ^ θ)
    (haP : ∀ z ε, 0 < ε → ∃ (a : A) (v : Fin (Module.finrank K E) → A ⊗[K] E),
      a • (exteriorBaseChangeEquiv K A E (Module.finrank K E)).symm
        (_root_.exteriorPower.ιMulti A (Module.finrank K E) v) = z ∧
      ‖a‖ * (∏ i, p (v i)) < pd z + ε)
    (haQ : ∀ z ε, 0 < ε → ∃ (a : C) (v : Fin (Module.finrank K E) → C ⊗[K] E),
      a • (exteriorBaseChangeEquiv K C E (Module.finrank K E)).symm
        (_root_.exteriorPower.ιMulti C (Module.finrank K E) v) = z ∧
      ‖a‖ * (∏ i, q (v i)) < qd z + ε)
    (hwP : ∀ v : Fin (Module.finrank K E) → A ⊗[K] E,
      pd ((exteriorBaseChangeEquiv K A E (Module.finrank K E)).symm
        (_root_.exteriorPower.ιMulti A (Module.finrank K E) v)) ≤ ∏ i, p (v i))
    (hwQ : ∀ v : Fin (Module.finrank K E) → C ⊗[K] E,
      qd ((exteriorBaseChangeEquiv K C E (Module.finrank K E)).symm
        (_root_.exteriorPower.ιMulti C (Module.finrank K E) v)) ≤ ∏ i, q (v i))
    (z : A ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    qd (completedDeterminantSemilinearEquiv τ e rfl z) = pd z ^ θ := by
  let d := completedDeterminantSemilinearEquiv τ e rfl
  have hcancel {r : ℝ} (hr : 0 ≤ r) : (r ^ θ⁻¹) ^ θ = r := by
    rw [← Real.rpow_mul hr, inv_mul_cancel₀ hθ.ne', Real.rpow_one]
  have hprod (v : Fin (Module.finrank K E) → A ⊗[K] E) :
      (∏ i, q (e (v i))) = (∏ i, p (v i)) ^ θ := by
    simp only [he]
    have H (s : Finset (Fin (Module.finrank K E))) :
        (∏ i ∈ s, p (v i) ^ θ) = (∏ i ∈ s, p (v i)) ^ θ := by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.prod_insert hi, ih,
          Real.mul_rpow (apply_nonneg p _) (Finset.prod_nonneg fun _ _ => apply_nonneg p _)]
    exact H Finset.univ
  apply le_antisymm
  · have hroot : qd (d z) ^ θ⁻¹ ≤ pd z := by
      apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨a, v, hv, hc⟩ := haP z ε hε
      let w := (exteriorBaseChangeEquiv K A E (Module.finrank K E)).symm
        (_root_.exteriorPower.ιMulti A (Module.finrank K E) v)
      have hd : d w = (exteriorBaseChangeEquiv K C E (Module.finrank K E)).symm
          (_root_.exteriorPower.ιMulti C (Module.finrank K E) (fun i => e (v i))) := by
        simpa only [finCongr_refl, Equiv.refl_symm, Equiv.refl_apply] using
          completedDeterminantSemilinearEquiv_ιMulti τ e rfl v
      have hb : qd (d z) ≤ (‖a‖ * ∏ i, p (v i)) ^ θ := by
        calc
          _ = ‖τ a‖ * qd (d w) := by
            rw [← hv, d.map_smulₛₗ]
            change qd (τ a • d w) = _
            rw [map_smul_eq_mul]
          _ ≤ ‖a‖ ^ θ * (∏ i, p (v i)) ^ θ := by
            rw [hτ, hd]
            exact mul_le_mul_of_nonneg_left ((hwQ _).trans_eq (hprod v))
              (Real.rpow_nonneg (norm_nonneg _) θ)
          _ = _ := (Real.mul_rpow (norm_nonneg _)
            (Finset.prod_nonneg fun _ _ => apply_nonneg p _)).symm
      have H := Real.rpow_le_rpow (apply_nonneg qd _) hb (inv_pos.mpr hθ).le
      rw [← Real.rpow_mul (mul_nonneg (norm_nonneg a)
        (Finset.prod_nonneg fun _ _ => apply_nonneg p _)),
        mul_inv_cancel₀ hθ.ne', Real.rpow_one] at H
      exact H.trans hc.le
    exact (hcancel (apply_nonneg qd _)).symm.trans_le
      (Real.rpow_le_rpow (Real.rpow_nonneg (apply_nonneg qd _) _) hroot hθ.le)
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨a, v, hv, hc⟩ := haQ (d z) ε hε
    let u : Fin (Module.finrank K E) → A ⊗[K] E := fun i => e.symm (v i)
    let w := (exteriorBaseChangeEquiv K A E (Module.finrank K E)).symm
      (_root_.exteriorPower.ιMulti A (Module.finrank K E) u)
    have hd : d w = (exteriorBaseChangeEquiv K C E (Module.finrank K E)).symm
        (_root_.exteriorPower.ιMulti C (Module.finrank K E) v) := by
      simpa only [u, finCongr_refl, Equiv.refl_symm, Equiv.refl_apply,
        LinearEquiv.apply_symm_apply] using
          completedDeterminantSemilinearEquiv_ιMulti τ e rfl u
    have hz : τ.symm a • w = z := by
      apply d.injective
      rw [d.map_smulₛₗ]
      change τ (τ.symm a) • d w = d z
      rw [RingEquiv.apply_symm_apply, hd]
      exact hv
    have ha : ‖τ.symm a‖ ^ θ = ‖a‖ := by
      simpa only [RingEquiv.apply_symm_apply] using (hτ (τ.symm a)).symm
    have hp : (∏ i, p (u i)) ^ θ = ∏ i, q (v i) := by
      rw [← hprod]
      simp only [u, LinearEquiv.apply_symm_apply]
    calc
      pd z ^ θ = (‖τ.symm a‖ * pd w) ^ θ := by rw [← hz, map_smul_eq_mul]
      _ = ‖a‖ * pd w ^ θ := by rw [Real.mul_rpow (norm_nonneg _) (apply_nonneg pd _), ha]
      _ ≤ ‖a‖ * (∏ i, p (u i)) ^ θ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (apply_nonneg pd _) (hwP u) hθ.le)
          (norm_nonneg a)
      _ = ‖a‖ * ∏ i, q (v i) := by rw [hp]
      _ ≤ qd (d z) + ε := hc.le

end DeterminantPower

section NumberFieldDeterminant

open AdelicStructure

variable {K : Type*} [Field K] [NumberField K]
  {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})

private abbrev normalizedCompletedFieldRingEquiv :
    (placeRep ω.val).Completion ≃+* (normalizedPlaceValue ω).Completion :=
  (AbsoluteValue.completionAlgEquivOfIsEquiv
    (placeRep ω.val) (normalizedPlaceValue ω)
      (normalizedPlaceValue_isEquiv_placeRep ω).symm).toRingEquiv

local instance : RingHomInvPair
    (normalizedCompletedFieldRingEquiv ω : (placeRep ω.val).Completion →+*
      (normalizedPlaceValue ω).Completion)
    ((normalizedCompletedFieldRingEquiv ω).symm : (normalizedPlaceValue ω).Completion →+*
      (placeRep ω.val).Completion) :=
  RingHomInvPair.of_ringEquiv (normalizedCompletedFieldRingEquiv ω)
local instance : RingHomInvPair
    ((normalizedCompletedFieldRingEquiv ω).symm : (normalizedPlaceValue ω).Completion →+*
      (placeRep ω.val).Completion)
    (normalizedCompletedFieldRingEquiv ω : (placeRep ω.val).Completion →+*
      (normalizedPlaceValue ω).Completion) :=
  RingHomInvPair.of_ringEquiv_symm (normalizedCompletedFieldRingEquiv ω)

/-- The actual tensor normalization with its genuine completed semilinear scalar action. -/
def normalizedNormFamilyTensorSemilinearEquiv :
    ((placeRep ω.val).Completion ⊗[K] E) ≃ₛₗ[
      (normalizedCompletedFieldRingEquiv ω : (placeRep ω.val).Completion →+*
        (normalizedPlaceValue ω).Completion)]
      ((normalizedPlaceValue ω).Completion ⊗[K] E) :=
  { (normalizedNormFamilyTensorEquiv ω).toAddEquiv with
    map_smul' := AbsoluteValue.completionScalarExtensionEquiv_smul _ _
      (normalizedPlaceValue_isEquiv_placeRep ω).symm E }

omit [FiniteDimensional K E] in
/-- Semilinear normalization is the already canonical tensor map on every vector. -/
theorem normalizedNormFamilyTensorSemilinearEquiv_apply
    (z : (placeRep ω.val).Completion ⊗[K] E) :
    normalizedNormFamilyTensorSemilinearEquiv ω z = normalizedNormFamilyTensorEquiv ω z := rfl

/-- The actual completed determinant equivalence induced by exterior normalization. -/
def normalizedCompletedDeterminantEquiv :
    ((placeRep ω.val).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) ≃ₛₗ[
      (normalizedCompletedFieldRingEquiv ω : (placeRep ω.val).Completion →+*
        (normalizedPlaceValue ω).Completion)]
      ((normalizedPlaceValue ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :=
  completedDeterminantSemilinearEquiv (normalizedCompletedFieldRingEquiv ω)
    (normalizedNormFamilyTensorSemilinearEquiv ω) rfl

omit [FiniteDimensional K E] in
/-- The canonical exterior normalization agrees with tensor normalization on the determinant. -/
theorem normalizedCompletedDeterminantEquiv_eq_tensor
    (z : (placeRep ω.val).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    normalizedCompletedDeterminantEquiv ω z = normalizedNormFamilyTensorEquiv ω z := by
  let d := normalizedCompletedDeterminantEquiv (E := E) ω
  have H (x : ⋀[K]^(Module.finrank K E) E)
      (hx : x ∈ Submodule.span K (Set.range (_root_.exteriorPower.ιMulti K
        (Module.finrank K E)))) :
      ∀ a : (placeRep ω.val).Completion,
        d (a ⊗ₜ[K] x) = normalizedNormFamilyTensorEquiv ω (a ⊗ₜ[K] x) := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      intro a
      let p := exteriorBaseChangeEquiv K (placeRep ω.val).Completion E (Module.finrank K E)
      let q := exteriorBaseChangeEquiv K (normalizedPlaceValue ω).Completion E
        (Module.finrank K E)
      have hp : p.symm (_root_.exteriorPower.ιMulti (placeRep ω.val).Completion
          (Module.finrank K E) (fun i => (1 : (placeRep ω.val).Completion) ⊗ₜ[K] v i)) =
          (1 : (placeRep ω.val).Completion) ⊗ₜ[K]
            _root_.exteriorPower.ιMulti K (Module.finrank K E) v := by
        apply p.injective
        simp only [p, LinearEquiv.apply_symm_apply, exteriorBaseChangeEquiv_tmul_ιMulti,
          one_smul]
      have hq : q.symm (_root_.exteriorPower.ιMulti (normalizedPlaceValue ω).Completion
          (Module.finrank K E) (fun i => (1 : (normalizedPlaceValue ω).Completion) ⊗ₜ[K] v i)) =
          (1 : (normalizedPlaceValue ω).Completion) ⊗ₜ[K]
            _root_.exteriorPower.ιMulti K (Module.finrank K E) v := by
        apply q.injective
        simp only [q, LinearEquiv.apply_symm_apply, exteriorBaseChangeEquiv_tmul_ιMulti,
          one_smul]
      have hd : d ((1 : (placeRep ω.val).Completion) ⊗ₜ[K]
          _root_.exteriorPower.ιMulti K (Module.finrank K E) v) =
          (1 : (normalizedPlaceValue ω).Completion) ⊗ₜ[K]
            _root_.exteriorPower.ιMulti K (Module.finrank K E) v := by
        have h := completedDeterminantSemilinearEquiv_ιMulti
          (normalizedCompletedFieldRingEquiv ω)
          (normalizedNormFamilyTensorSemilinearEquiv (E := E) ω) rfl
          (fun i => (1 : (placeRep ω.val).Completion) ⊗ₜ[K] v i)
        simp only [finCongr_refl, Equiv.refl_symm, Equiv.refl_apply,
          normalizedNormFamilyTensorSemilinearEquiv_apply,
          normalizedNormFamilyTensorEquiv_one_tmul] at h
        change d (p.symm (_root_.exteriorPower.ιMulti (placeRep ω.val).Completion
          (Module.finrank K E) (fun i => (1 : (placeRep ω.val).Completion) ⊗ₜ[K] v i))) =
            q.symm (_root_.exteriorPower.ιMulti (normalizedPlaceValue ω).Completion
              (Module.finrank K E)
                (fun i => (1 : (normalizedPlaceValue ω).Completion) ⊗ₜ[K] v i)) at h
        rw [hp, hq] at h
        exact h
      calc
        d (a ⊗ₜ[K] _root_.exteriorPower.ιMulti K (Module.finrank K E) v) =
            (normalizedCompletedFieldRingEquiv ω) a • d ((1 : (placeRep ω.val).Completion) ⊗ₜ[K]
              _root_.exteriorPower.ιMulti K (Module.finrank K E) v) := by
          have h := d.map_smulₛₗ a ((1 : (placeRep ω.val).Completion) ⊗ₜ[K]
            _root_.exteriorPower.ιMulti K (Module.finrank K E) v)
          change d (a • ((1 : (placeRep ω.val).Completion) ⊗ₜ[K]
            _root_.exteriorPower.ιMulti K (Module.finrank K E) v)) =
              normalizedCompletedFieldRingEquiv ω a • d _ at h
          simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h
        _ = normalizedCompletedFieldRingEquiv ω a ⊗ₜ[K]
            _root_.exteriorPower.ιMulti K (Module.finrank K E) v := by
          rw [hd]
          simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        _ = _ := (AbsoluteValue.completionScalarExtensionEquiv_tmul _ _
          (normalizedPlaceValue_isEquiv_placeRep ω).symm _ a _).symm
    | zero => intro a; simp only [TensorProduct.tmul_zero, map_zero]
    | add x y hx hy ihx ihy =>
      intro a
      simp only [TensorProduct.tmul_add, map_add, ihx a, ihy a]
    | smul r x hx ih =>
      intro a
      simpa only [TensorProduct.tmul_smul, TensorProduct.smul_tmul] using ih (r • a)
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul a x =>
    apply H x _ a
    rw [_root_.exteriorPower.ιMulti_span]
    exact Submodule.mem_top

namespace NormFamily

variable (ξ : NormFamily (numberFieldAdelicStructure K) E) (hξ : ξ.IsUltrametric)

/-- The actual completed determinant quotient transports by the same positive
normalization power as its actual completed vector norm. -/
theorem numberFieldNormalize_determinant_norm_map
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (z : (placeRep ω.val).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    (ξ.numberFieldNormalize hξ).determinant.norm ω
        (normalizedNormFamilyTensorEquiv ω z) =
      ξ.determinant.norm ω.val z ^ numberFieldNormalizationExponent ω := by
  have hτ (a : (placeRep ω.val).Completion) :
      ‖normalizedCompletedFieldRingEquiv ω a‖ =
        ‖a‖ ^ numberFieldNormalizationExponent ω := by
    apply AbsoluteValue.norm_completionAlgEquivOfIsEquiv _ _
      (normalizedPlaceValue_isEquiv_placeRep ω).symm
      (numberFieldNormalizationExponent ω) (numberFieldNormalizationExponent_pos ω)
    intro a
    by_cases hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin
    · erw [numberFieldNormalizationExponent_of_fin ω hω]
      exact normalizedPlace_value_rpow_of_mem_fin ω hω a
    · erw [numberFieldNormalizationExponent_of_inf ω hω, Real.rpow_one]
      exact normalizedPlace_value_eq_of_not_mem_fin ω hω a
  have H := completedDeterminantSeminorm_norm_rpow
    (normalizedCompletedFieldRingEquiv ω)
    (ξ.norm ω.val) (ξ.determinant.norm ω.val)
    ((ξ.numberFieldNormalize hξ).norm ω) ((ξ.numberFieldNormalize hξ).determinant.norm ω)
    (normalizedNormFamilyTensorSemilinearEquiv ω)
    (numberFieldNormalizationExponent ω) (numberFieldNormalizationExponent_pos ω)
    hτ (ξ.numberFieldNormalize_norm_map hξ ω)
    (fun z ε hε => ξ.exists_smul_determinant_ιMulti_norm_lt ω.val z hε)
    (fun z ε hε => (ξ.numberFieldNormalize hξ).exists_smul_determinant_ιMulti_norm_lt ω z hε)
    (ξ.determinant_norm_ιMulti_le ω.val)
    ((ξ.numberFieldNormalize hξ).determinant_norm_ιMulti_le ω) z
  exact (congrArg ((ξ.numberFieldNormalize hξ).determinant.norm ω)
    (normalizedCompletedDeterminantEquiv_eq_tensor ω z)).symm.trans H

omit hξ in
/-- Every actual determinant family is a line, so its finite norms are ultrametric. -/
theorem numberField_determinant_isUltrametric : ξ.determinant.IsUltrametric :=
  ξ.determinant.isUltrametric_of_finrank_le_one determinant_finrank.le

/-- Normalization commutes with the genuine completed determinant norm family. -/
theorem numberFieldNormalize_determinant :
    (ξ.numberFieldNormalize hξ).determinant =
      ξ.determinant.numberFieldNormalize ξ.numberField_determinant_isUltrametric := by
  ext ω z
  obtain ⟨y, rfl⟩ := (normalizedNormFamilyTensorEquiv ω).surjective z
  erw [numberFieldNormalize_determinant_norm_map, numberFieldNormalize_norm_map]

/-- The genuine determinant log norm has the same local positive exponent,
including the totalized logarithm of the zero determinant vector. -/
theorem numberFieldNormalize_determinant_logNorm
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (x : ⋀[K]^(Module.finrank K E) E) :
    (ξ.numberFieldNormalize hξ).determinant.logNorm x ω =
      numberFieldNormalizationExponent ω * ξ.determinant.logNorm x ω.val := by
  rw [ξ.numberFieldNormalize_determinant hξ]
  exact ξ.determinant.numberFieldNormalize_logNorm ξ.numberField_determinant_isUltrametric x ω

/-- The actual extended determinant log norm integral is preserved even when infinite. -/
theorem numberFieldNormalize_determinant_lintegral_enorm_logNorm
    (x : ⋀[K]^(Module.finrank K E) E) :
    (∫⁻ ω, ‖(ξ.numberFieldNormalize hξ).determinant.logNorm x ω‖ₑ
      ∂(normalizedNumberFieldAdelicStructure K).v) =
      ∫⁻ ω, ‖ξ.determinant.logNorm x ω‖ₑ ∂(numberFieldAdelicStructure K).v := by
  exact (lintegral_congr (fun ω => congrArg (fun r : ℝ => ‖r‖ₑ)
    (ξ.numberFieldNormalize_determinant_logNorm hξ ω x))).trans
      (lintegral_enorm_numberFieldNormalizationExponent_mul (ξ.determinant.logNorm x))

/-- Integrability of the actual determinant log norm is unchanged by normalization. -/
theorem numberFieldNormalize_determinant_integrable_logNorm_iff
    (x : ⋀[K]^(Module.finrank K E) E) :
    Integrable ((ξ.numberFieldNormalize hξ).determinant.logNorm x)
        (normalizedNumberFieldAdelicStructure K).v ↔
      Integrable (ξ.determinant.logNorm x) (numberFieldAdelicStructure K).v := by
  have H : (ξ.numberFieldNormalize hξ).determinant.logNorm x =
      fun ω => numberFieldNormalizationExponent ω * ξ.determinant.logNorm x ω.val :=
    funext (fun ω => ξ.numberFieldNormalize_determinant_logNorm hξ ω x)
  rw [H]
  exact integrable_numberFieldNormalizationExponent_mul_iff (ξ.determinant.logNorm x)

/-- Exact signed integration of the genuine actual determinant log norm. -/
theorem numberFieldNormalize_determinant_integral_logNorm
    (x : ⋀[K]^(Module.finrank K E) E)
    (hx : Integrable (ξ.determinant.logNorm x) (numberFieldAdelicStructure K).v) :
    (∫ ω, (ξ.numberFieldNormalize hξ).determinant.logNorm x ω
      ∂(normalizedNumberFieldAdelicStructure K).v) =
      ∫ ω, ξ.determinant.logNorm x ω ∂(numberFieldAdelicStructure K).v := by
  rw [ξ.numberFieldNormalize_determinant hξ]
  exact ξ.determinant.numberFieldNormalize_integral_logNorm
    ξ.numberField_determinant_isUltrametric x hx

/-- Exact absolute integration of the genuine actual determinant log norm. -/
theorem numberFieldNormalize_determinant_integral_abs_logNorm
    (x : ⋀[K]^(Module.finrank K E) E)
    (hx : Integrable (ξ.determinant.logNorm x) (numberFieldAdelicStructure K).v) :
    (∫ ω, |(ξ.numberFieldNormalize hξ).determinant.logNorm x ω|
      ∂(normalizedNumberFieldAdelicStructure K).v) =
      ∫ ω, |ξ.determinant.logNorm x ω| ∂(numberFieldAdelicStructure K).v := by
  rw [ξ.numberFieldNormalize_determinant hξ]
  exact ξ.determinant.numberFieldNormalize_integral_abs_logNorm
    ξ.numberField_determinant_isUltrametric x hx

end NormFamily

namespace AdelicVectorBundle

variable (V : AdelicVectorBundle (numberFieldAdelicStructure K) E)
  (hV : V.toNormFamily.IsUltrametric)

/-- The native actual normalized determinant degree equals the old native degree;
all properness, Archimedean and discrete-base properties are supplied by the curves. -/
theorem numberFieldNormalize_degree :
    let _oldMeasurable : MeasurableSpace (AbsoluteValue.Place K) := ⊤
    letI := normalizedNumberFieldAdelicStructure_isProper (K := K)
    (V.numberFieldNormalize hV).degree
        (Or.inl (inferInstanceAs (DiscreteMeasurableSpace
          {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})))
        normalizedNumberFieldArchimedeanCompletions =
      V.degree (Or.inl (inferInstanceAs (DiscreteMeasurableSpace (AbsoluteValue.Place K))))
        numberFieldArchimedeanCompletions := by
  let _oldMeasurable : MeasurableSpace (AbsoluteValue.Place K) := ⊤
  let := normalizedNumberFieldAdelicStructure_isProper (K := K)
  let hS : DiscreteMeasurableSpace (numberFieldAdelicStructure K).Ω ∨
      (numberFieldAdelicStructure K).HasCommonCountableDenseSubfield :=
    Or.inl (inferInstanceAs (DiscreteMeasurableSpace (AbsoluteValue.Place K)))
  let hnS : DiscreteMeasurableSpace (normalizedNumberFieldAdelicStructure K).Ω ∨
      (normalizedNumberFieldAdelicStructure K).HasCommonCountableDenseSubfield :=
    Or.inl (inferInstanceAs (DiscreteMeasurableSpace
      {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}))
  let D := V.determinantOfMeasurableBase hS numberFieldArchimedeanCompletions
  let s := D.lineGenerator (V.determinantOfMeasurableBase_isLine hS
    numberFieldArchimedeanCompletions)
  rw [(V.numberFieldNormalize hV).degree_eq_neg_integral hnS
    normalizedNumberFieldArchimedeanCompletions s,
    V.degree_eq_neg_integral hS numberFieldArchimedeanCompletions s]
  exact congrArg (fun r : ℝ => -r)
    (V.toNormFamily.numberFieldNormalize_determinant_integral_logNorm hV s.val
      (D.integrable_logNorm s.val))

/-- The actual normalized rank-zero bundle retains its native degree zero. -/
theorem numberFieldNormalize_degree_eq_zero_of_finrank_eq_zero
    (hr : Module.finrank K E = 0) :
    letI := normalizedNumberFieldAdelicStructure_isProper (K := K)
    (V.numberFieldNormalize hV).degree
        (Or.inl (inferInstanceAs (DiscreteMeasurableSpace
          {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})))
        normalizedNumberFieldArchimedeanCompletions = 0 := by
  let _oldMeasurable : MeasurableSpace (AbsoluteValue.Place K) := ⊤
  rw [V.numberFieldNormalize_degree hV]
  exact V.degree_eq_zero_of_finrank_eq_zero _ numberFieldArchimedeanCompletions hr

end AdelicVectorBundle

end NumberFieldDeterminant

end ArakelovGeometry
