/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.NormFamilyPowerTransport
import ArakelovGeometry.NumberTheory.NormalizedNumberFieldCompletionComparison

/-!
# Norm families on the actual normalized number-field curve

Transport the actual completed tensor fibres. Finite norms use the inverse
actual completion degree; infinite norms retain their usual absolute values.
-/

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry

open AdelicStructure ActualPrimeIndexing

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [AddCommGroup E] [Module K E]

/-- A normalized finite class is finite for the actual old representative too. -/
theorem normalizedPlace_mem_old_fin
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) :
    ω.val ∈ (numberFieldAdelicStructure K).Ωfin :=
  (NumberField.isNonarchimedean_congr (normalizedPlaceValue_isEquiv_placeRep ω)).mp hω

/-- The actual inverse completion degree is strictly positive at every finite class. -/
theorem normalizedFiniteExponent_pos
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) :
    0 < ((normalizedPlaceValue ω).localDegree ℚ : ℝ)⁻¹ := by
  obtain ⟨P, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
  apply inv_pos.mpr
  exact_mod_cast normalizedPlaceValue_finitePlace_localDegree_pos (FinitePlace.mk P)

/-- Actual finite original values obey the inverse local-degree power at every scalar. -/
theorem normalizedPlace_value_rpow_of_mem_fin
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) (a : K) :
    normalizedPlaceValue ω a =
      (placeRep ω.val a) ^ ((normalizedPlaceValue ω).localDegree ℚ : ℝ)⁻¹ := by
  obtain ⟨P, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
  exact (normalizedPlaceValue_eq_finitePlace_rpow (FinitePlace.mk P) a).trans
    (congrArg (fun v : AbsoluteValue K ℝ =>
      (v a) ^ ((normalizedPlaceValue (normalizedPrimeParameter P)).localDegree ℚ : ℝ)⁻¹)
      (placeRep_mk_finitePlace (FinitePlace.mk P)).symm)

/-- At each actual infinite class the original normalized and old values agree exactly. -/
theorem normalizedPlace_value_eq_of_not_mem_fin
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (hω : ω ∉ (normalizedNumberFieldAdelicStructure K).Ωfin) (a : K) :
    normalizedPlaceValue ω a = placeRep ω.val a := by
  rcases place_trichotomy ω.val with ht | ⟨v, hv⟩ | ⟨w, hw⟩
  · exact False.elim (ω.property ht)
  · have hb : IsNonarchimedean (placeRep ω.val) := by
      rw [hv, placeRep_mk_finitePlace]
      exact NumberField.finitePlace_isNonarchimedean v
    exact False.elim (hω
      ((NumberField.isNonarchimedean_congr (normalizedPlaceValue_isEquiv_placeRep ω)).mpr hb))
  · have he : ω = ⟨Quotient.mk' w.val, mk_infinitePlace_ne_trivialPlace w⟩ := Subtype.ext hw
    exact (congrArg (fun η => normalizedPlaceValue η a) he).trans
      ((congrArg (fun v : AbsoluteValue K ℝ => v a)
        (normalizedPlaceValue_eq_infinitePlace w)).trans
        ((congrArg (fun v : AbsoluteValue K ℝ => v a)
          (placeRep_mk_infinitePlace w)).symm.trans
          (congrArg (fun c => placeRep c a) hw).symm))

/-- The actual old and normalized completed tensor fibres over a nontrivial class. -/
def normalizedNormFamilyTensorEquiv
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) :
    ((placeRep ω.val).Completion ⊗[K] E) ≃ₗ[K]
      ((normalizedPlaceValue ω).Completion ⊗[K] E) :=
  AbsoluteValue.completionScalarExtensionEquiv _ _
    (normalizedPlaceValue_isEquiv_placeRep ω).symm E

/-- The actual completed tensor normalization fixes every original vector. -/
theorem normalizedNormFamilyTensorEquiv_one_tmul
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) (x : E) :
    normalizedNormFamilyTensorEquiv ω (1 ⊗ₜ[K] x) = 1 ⊗ₜ[K] x :=
  (AbsoluteValue.completionScalarExtensionEquiv_tmul _ _
    (normalizedPlaceValue_isEquiv_placeRep ω).symm E 1 x).trans
    (congrArg (fun a : (normalizedPlaceValue ω).Completion => a ⊗ₜ[K] x)
      (AbsoluteValue.completionAlgEquivOfIsEquiv _ _
        (normalizedPlaceValue_isEquiv_placeRep ω).symm).map_one)

namespace NormFamily

variable (ξ : NormFamily (numberFieldAdelicStructure K) E) (hξ : ξ.IsUltrametric)

/-- Normalize the actual completed norm family at every nontrivial number-field place. -/
def numberFieldNormalize : NormFamily (normalizedNumberFieldAdelicStructure K) E where
  norm := fun (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) => by
    classical
    exact if hω : IsNonarchimedean (normalizedPlaceValue ω) then
      AbsoluteValue.powerTransportSeminorm _ _
        (normalizedPlaceValue_isEquiv_placeRep ω).symm E
        ((normalizedPlaceValue ω).localDegree ℚ : ℝ)⁻¹
        (normalizedFiniteExponent_pos ω hω)
        (normalizedPlace_value_rpow_of_mem_fin ω hω) (ξ.norm ω.val)
        (hξ ω.val (normalizedPlace_mem_old_fin ω hω))
    else
      AbsoluteValue.sameValueTransportSeminorm _ _
        (normalizedPlaceValue_isEquiv_placeRep ω).symm E (ξ.norm ω.val)
        (normalizedPlace_value_eq_of_not_mem_fin ω hω)
  norm_eq_zero_iff :=
      fun (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) y => by
    classical
    split_ifs with hω
    · erw [dif_pos hω]
      exact AbsoluteValue.powerTransportSeminorm_eq_zero_iff _ _
        (normalizedPlaceValue_isEquiv_placeRep ω).symm E
        ((normalizedPlaceValue ω).localDegree ℚ : ℝ)⁻¹
        (normalizedFiniteExponent_pos ω hω)
        (normalizedPlace_value_rpow_of_mem_fin ω hω) (ξ.norm ω.val)
        (hξ ω.val (normalizedPlace_mem_old_fin ω hω)) (ξ.norm_eq_zero_iff ω.val) y
    · erw [dif_neg hω]
      exact AbsoluteValue.sameValueTransportSeminorm_eq_zero_iff _ _
        (normalizedPlaceValue_isEquiv_placeRep ω).symm E (ξ.norm ω.val)
        (normalizedPlace_value_eq_of_not_mem_fin ω hω) (ξ.norm_eq_zero_iff ω.val) y

/-- Every transported actual finite completed tensor has the inverse-degree norm power. -/
theorem numberFieldNormalize_norm_map_fin
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin)
    (z : (placeRep ω.val).Completion ⊗[K] E) :
    (ξ.numberFieldNormalize hξ).norm ω (normalizedNormFamilyTensorEquiv ω z) =
      ξ.norm ω.val z ^ ((normalizedPlaceValue ω).localDegree ℚ : ℝ)⁻¹ := by
  classical
  change IsNonarchimedean (normalizedPlaceValue ω) at hω
  unfold numberFieldNormalize
  dsimp only
  erw [dif_pos hω]
  exact AbsoluteValue.powerTransportSeminorm_map _ _ _ _ _ _ _ _ _ z

/-- Every transported actual infinite completed tensor retains its original norm. -/
theorem numberFieldNormalize_norm_map_inf
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (hω : ω ∉ (normalizedNumberFieldAdelicStructure K).Ωfin)
    (z : (placeRep ω.val).Completion ⊗[K] E) :
    (ξ.numberFieldNormalize hξ).norm ω (normalizedNormFamilyTensorEquiv ω z) =
      ξ.norm ω.val z := by
  classical
  change ¬ IsNonarchimedean (normalizedPlaceValue ω) at hω
  unfold numberFieldNormalize
  dsimp only
  erw [dif_neg hω]
  exact AbsoluteValue.sameValueTransportSeminorm_map _ _ _ _ _ _ z

/-- The actual normalized family is ultrametric at every normalized finite place. -/
theorem numberFieldNormalize_isUltrametric : (ξ.numberFieldNormalize hξ).IsUltrametric := by
  classical
  intro ω hω y z
  change IsNonarchimedean (normalizedPlaceValue ω) at hω
  unfold numberFieldNormalize
  dsimp only
  erw [dif_pos hω]
  exact AbsoluteValue.powerTransportSeminorm_isUltrametric _ _ _ _ _ _ _ _ _ y z

/-- The normalization formula for every rational vector at an actual finite place. -/
theorem numberFieldNormalize_norm_tmul_fin
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) (x : E) :
    (ξ.numberFieldNormalize hξ).norm ω (1 ⊗ₜ[K] x) =
      ξ.norm ω.val (1 ⊗ₜ[K] x) ^ ((normalizedPlaceValue ω).localDegree ℚ : ℝ)⁻¹ :=
  (congrArg ((ξ.numberFieldNormalize hξ).norm ω)
    (normalizedNormFamilyTensorEquiv_one_tmul ω x).symm).trans
    (ξ.numberFieldNormalize_norm_map_fin hξ ω hω (1 ⊗ₜ[K] x))

/-- The normalization formula for every rational vector at an actual infinite place. -/
theorem numberFieldNormalize_norm_tmul_inf
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (hω : ω ∉ (normalizedNumberFieldAdelicStructure K).Ωfin) (x : E) :
    (ξ.numberFieldNormalize hξ).norm ω (1 ⊗ₜ[K] x) = ξ.norm ω.val (1 ⊗ₜ[K] x) :=
  (congrArg ((ξ.numberFieldNormalize hξ).norm ω)
    (normalizedNormFamilyTensorEquiv_one_tmul ω x).symm).trans
    (ξ.numberFieldNormalize_norm_map_inf hξ ω hω (1 ⊗ₜ[K] x))

/-- Actual local-degree weights cancel the finite tensor norm power, also at zero. -/
theorem numberFieldNormalize_weighted_log_norm_map_fin
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin)
    (z : (placeRep ω.val).Completion ⊗[K] E) :
    ((normalizedPlaceValue ω).localDegree ℚ : ℝ) *
      Real.log ((ξ.numberFieldNormalize hξ).norm ω (normalizedNormFamilyTensorEquiv ω z)) =
        Real.log (ξ.norm ω.val z) := by
  have hd : (0 : ℝ) < ((normalizedPlaceValue ω).localDegree ℚ : ℝ) :=
    inv_pos.mp (normalizedFiniteExponent_pos ω hω)
  have hv := ξ.numberFieldNormalize_norm_map_fin hξ ω hω z
  by_cases hz : ξ.norm ω.val z = 0
  · have hn : (ξ.numberFieldNormalize hξ).norm ω (normalizedNormFamilyTensorEquiv ω z) = 0 :=
      hv.trans ((congrArg (fun r : ℝ => r ^
        ((normalizedPlaceValue ω).localDegree ℚ : ℝ)⁻¹) hz).trans
          (Real.zero_rpow (inv_pos.mpr hd).ne'))
    rw [hn, hz, Real.log_zero, mul_zero]
  · calc
      _ = ((normalizedPlaceValue ω).localDegree ℚ : ℝ) *
          Real.log (ξ.norm ω.val z ^ ((normalizedPlaceValue ω).localDegree ℚ : ℝ)⁻¹) :=
        congrArg (fun r : ℝ => ((normalizedPlaceValue ω).localDegree ℚ : ℝ) * Real.log r) hv
      _ = _ := by
        rw [Real.log_rpow (lt_of_le_of_ne (ξ.norm_nonneg ω.val z) (Ne.symm hz)),
          ← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul]

end NormFamily

end ArakelovGeometry
