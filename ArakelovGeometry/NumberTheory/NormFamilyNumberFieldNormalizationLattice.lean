/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldNormalization
import ArakelovGeometry.NumberTheory.NormFamilyCompletedLocalUnitBall
import ArakelovGeometry.NumberTheory.NormFamilyGlobalUnitBall

/-!
# Actual local and global finite unit balls under normalization

The actual completed tensor map restricts to the literal unit balls.
The old zero-mass trivial place still contributes to its global intersection.
-/

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry

open AdelicStructure ActualPrimeIndexing

variable {K : Type*} [Field K] [NumberField K]
  {E : Type*} [AddCommGroup E] [Module K E]

/-- The canonical completed scalar map has the actual positive finite norm power. -/
theorem norm_normalizedCompletionEquiv
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin)
    (a : (placeRep ω.val).Completion) :
    ‖AbsoluteValue.completionAlgEquivOfIsEquiv _ _
      (normalizedPlaceValue_isEquiv_placeRep ω).symm a‖ =
      ‖a‖ ^ ((normalizedPlaceValue ω).localDegree ℚ : ℝ)⁻¹ :=
  AbsoluteValue.norm_completionAlgEquivOfIsEquiv _ _ _ _
    (normalizedFiniteExponent_pos ω hω)
    (normalizedPlace_value_rpow_of_mem_fin ω hω) a

/-- The actual completed scalar unit-ball inequality is preserved and reflected. -/
theorem norm_normalizedCompletionEquiv_le_one_iff
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin)
    (a : (placeRep ω.val).Completion) :
    ‖AbsoluteValue.completionAlgEquivOfIsEquiv _ _
      (normalizedPlaceValue_isEquiv_placeRep ω).symm a‖ ≤ 1 ↔ ‖a‖ ≤ 1 := by
  rw [norm_normalizedCompletionEquiv ω hω]
  simpa only [Real.one_rpow] using
    Real.rpow_le_rpow_iff (_root_.norm_nonneg a) zero_le_one
      (normalizedFiniteExponent_pos ω hω)

/-- Restriction of the canonical field map to the actual completed coefficient rings. -/
def normalizedCompletedLocalRingEquiv
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) :
    (numberFieldAdelicStructure K).completedLocalRing ω.val
      (normalizedPlace_mem_old_fin ω hω) ≃+*
      (normalizedNumberFieldAdelicStructure K).completedLocalRing ω hω := by
  let e := AbsoluteValue.completionAlgEquivOfIsEquiv _ _
    (normalizedPlaceValue_isEquiv_placeRep ω).symm
  let oldS := numberFieldAdelicStructure K
  let newS := normalizedNumberFieldAdelicStructure K
  refine
    { toFun := fun a => ⟨e a.val, (newS.mem_completedLocalRing ω hω _).mpr
        ((norm_normalizedCompletionEquiv_le_one_iff ω hω a.val).mpr
          ((oldS.mem_completedLocalRing ω.val (normalizedPlace_mem_old_fin ω hω) a.val).mp
            a.property))⟩
      invFun := fun a => ⟨e.symm a.val, ?_⟩
      left_inv := fun a => Subtype.ext (e.symm_apply_apply a.val)
      right_inv := fun a => Subtype.ext (e.apply_symm_apply a.val)
      map_mul' := fun a b => Subtype.ext (e.map_mul a.val b.val)
      map_add' := fun a b => Subtype.ext (e.map_add a.val b.val) }
  exact (oldS.mem_completedLocalRing ω.val (normalizedPlace_mem_old_fin ω hω) _).mpr
    ((norm_normalizedCompletionEquiv_le_one_iff ω hω (e.symm a.val)).mp (by
      change ‖e (e.symm a.val)‖ ≤ 1
      erw [e.apply_symm_apply a.val]
      exact (newS.mem_completedLocalRing ω hω a.val).mp a.property))

/-- The coefficient-ring restriction is the same a.valctual completed field map. -/
theorem normalizedCompletedLocalRingEquiv_coe
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin)
    (a : (numberFieldAdelicStructure K).completedLocalRing ω.val
      (normalizedPlace_mem_old_fin ω hω)) :
    (normalizedCompletedLocalRingEquiv ω hω a).val =
      AbsoluteValue.completionAlgEquivOfIsEquiv _ _
        (normalizedPlaceValue_isEquiv_placeRep ω).symm a.val := rfl

namespace NormFamily

variable (ξ : NormFamily (numberFieldAdelicStructure K) E) (hξ : ξ.IsUltrametric)

/-- The canonical actual tensor map preserves and reflects the completed unit ball. -/
theorem numberFieldNormalize_mem_completedUnitBall_map_iff
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin)
    (z : (placeRep ω.val).Completion ⊗[K] E) :
    normalizedNormFamilyTensorEquiv ω z ∈ (ξ.numberFieldNormalize hξ).completedUnitBall ω ↔
      z ∈ ξ.completedUnitBall ω.val := by
  change (ξ.numberFieldNormalize hξ).norm ω (normalizedNormFamilyTensorEquiv ω z) ≤ 1 ↔
    ξ.norm ω.val z ≤ 1
  erw [ξ.numberFieldNormalize_norm_map_fin hξ ω hω z]
  simpa only [Real.one_rpow] using
    Real.rpow_le_rpow_iff (ξ.norm_nonneg ω.val z) zero_le_one
      (normalizedFiniteExponent_pos ω hω)

/-- The actual rational unit balls agree at every nontrivial finite place. -/
theorem numberFieldNormalize_mem_rationalUnitBall_iff
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) (x : E) :
    x ∈ (ξ.numberFieldNormalize hξ).rationalUnitBall ω ↔ x ∈ ξ.rationalUnitBall ω.val := by
  change (ξ.numberFieldNormalize hξ).norm ω (1 ⊗ₜ[K] x) ≤ 1 ↔
    ξ.norm ω.val (1 ⊗ₜ[K] x) ≤ 1
  erw [ξ.numberFieldNormalize_norm_tmul_fin hξ ω hω x]
  simpa only [Real.one_rpow] using
    Real.rpow_le_rpow_iff (ξ.norm_nonneg ω.val (1 ⊗ₜ[K] x)) zero_le_one
      (normalizedFiniteExponent_pos ω hω)

/-- Restriction of the canonical tensor map to the genuine completed unit-ball modules. -/
def numberFieldNormalizeCompletedUnitBallEquiv
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) :
    ξ.completedUnitBallModule ω.val (normalizedPlace_mem_old_fin ω hω) hξ ≃+
      (ξ.numberFieldNormalize hξ).completedUnitBallModule ω hω
        (ξ.numberFieldNormalize_isUltrametric hξ) := by
  let T := normalizedNormFamilyTensorEquiv (E := E) ω
  refine
    { toFun := fun z => ⟨T z.val,
        (ξ.numberFieldNormalize_mem_completedUnitBall_map_iff hξ ω hω z.val).mpr z.property⟩
      invFun := fun z => ⟨T.symm z.val, ?_⟩
      left_inv := fun z => Subtype.ext (T.symm_apply_apply z.val)
      right_inv := fun z => Subtype.ext (T.apply_symm_apply z.val)
      map_add' := fun x y => Subtype.ext (T.map_add x.val y.val) }
  exact (ξ.numberFieldNormalize_mem_completedUnitBall_map_iff hξ ω hω (T.symm z.val)).mp
    (by erw [T.apply_symm_apply z.val]; exact z.property)

/-- The completed-ball equivalence has the actual canonical tensor value. -/
theorem numberFieldNormalizeCompletedUnitBallEquiv_coe
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin)
    (z : ξ.completedUnitBallModule ω.val (normalizedPlace_mem_old_fin ω hω) hξ) :
    (ξ.numberFieldNormalizeCompletedUnitBallEquiv hξ ω hω z).val =
      normalizedNormFamilyTensorEquiv ω z.val := rfl

/-- The actual ball equivalence respects the transported completed coefficient action. -/
theorem numberFieldNormalizeCompletedUnitBallEquiv_smul
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin)
    (a : (numberFieldAdelicStructure K).completedLocalRing ω.val
      (normalizedPlace_mem_old_fin ω hω))
    (z : ξ.completedUnitBallModule ω.val (normalizedPlace_mem_old_fin ω hω) hξ) :
    ξ.numberFieldNormalizeCompletedUnitBallEquiv hξ ω hω (a • z) =
      normalizedCompletedLocalRingEquiv ω hω a •
        ξ.numberFieldNormalizeCompletedUnitBallEquiv hξ ω hω z := by
  apply Subtype.ext
  exact AbsoluteValue.completionScalarExtensionEquiv_smul _ _ _ E a.val z.val

/-- Every new completed unit-ball vector comes from the actual old completed ball. -/
theorem numberFieldNormalize_completedUnitBall_image
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) :
    normalizedNormFamilyTensorEquiv ω '' ξ.completedUnitBall ω.val =
      (ξ.numberFieldNormalize hξ).completedUnitBall ω := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (ξ.numberFieldNormalize_mem_completedUnitBall_map_iff hξ ω hω z).mpr hz
  · intro hy
    obtain ⟨z, rfl⟩ := (normalizedNormFamilyTensorEquiv ω).surjective y
    exact ⟨z, (ξ.numberFieldNormalize_mem_completedUnitBall_map_iff hξ ω hω z).mp hy, rfl⟩

/-- The normalized global ball imposes precisely the nontrivial old finite conditions. -/
theorem numberFieldNormalize_mem_globalUnitBall_iff (x : E) :
    x ∈ (ξ.numberFieldNormalize hξ).globalUnitBall ↔
      ∀ ω ∈ (numberFieldAdelicStructure K).Ωfin,
        ω ≠ AbsoluteValue.trivialPlace K → x ∈ ξ.rationalUnitBall ω := by
  constructor
  · intro hx ω hω hnt
    have hnew : (⟨ω, hnt⟩ : (normalizedNumberFieldAdelicStructure K).Ω) ∈
        (normalizedNumberFieldAdelicStructure K).Ωfin :=
      (NumberField.isNonarchimedean_congr
        (normalizedPlaceValue_isEquiv_placeRep ⟨ω, hnt⟩)).mpr hω
    exact (ξ.numberFieldNormalize_mem_rationalUnitBall_iff hξ ⟨ω, hnt⟩ hnew x).mp
      (hx ⟨ω, hnt⟩ hnew)
  · intro hx ω hω
    exact (ξ.numberFieldNormalize_mem_rationalUnitBall_iff hξ ω hω x).mpr
      (hx ω.val (normalizedPlace_mem_old_fin ω hω) ω.property)

/-- The old global ball is the normalized global ball with the trivial-point condition. -/
theorem mem_globalUnitBall_iff_numberFieldNormalize (x : E) :
    x ∈ ξ.globalUnitBall ↔ x ∈ (ξ.numberFieldNormalize hξ).globalUnitBall ∧
      x ∈ ξ.rationalUnitBall (AbsoluteValue.trivialPlace K) := by
  have ht : AbsoluteValue.trivialPlace K ∈ (numberFieldAdelicStructure K).Ωfin :=
    (NumberField.isNonarchimedean_congr (placeRep_equiv (AbsoluteValue.trivialPlace K))).mp
      AbsoluteValue.isNonarchimedeanPlace_trivialPlace
  constructor
  · intro hx
    exact ⟨(ξ.numberFieldNormalize_mem_globalUnitBall_iff hξ x).mpr
      (fun ω hω _ => hx ω hω), hx _ ht⟩
  · rintro ⟨hx, hxt⟩ ω hω
    by_cases hnt : ω = AbsoluteValue.trivialPlace K
    · exact hnt ▸ hxt
    · exact (ξ.numberFieldNormalize_mem_globalUnitBall_iff hξ x).mp hx ω hω hnt

/-- The old global ball is contained in the normalized one, with no converse asserted. -/
theorem globalUnitBall_subset_numberFieldNormalize :
    ξ.globalUnitBall ⊆ (ξ.numberFieldNormalize hξ).globalUnitBall :=
  fun x hx => ((ξ.mem_globalUnitBall_iff_numberFieldNormalize hξ x).mp hx).1

/-- Adding or omitting the one trivial parameter preserves finite norm exceptions. -/
theorem numberFieldNormalize_hasFiniteNormExceptions_iff :
    (ξ.numberFieldNormalize hξ).HasFiniteNormExceptions ↔ ξ.HasFiniteNormExceptions := by
  constructor
  · intro hfinite x
    have hi := (hfinite x).image
      (Subtype.val : (normalizedNumberFieldAdelicStructure K).Ω → AbsoluteValue.Place K)
    refine (hi.union (Set.finite_singleton (AbsoluteValue.trivialPlace K))).subset ?_
    rintro ω ⟨hω, hx⟩
    by_cases ht : ω = AbsoluteValue.trivialPlace K
    · exact Or.inr ht
    · refine Or.inl ⟨⟨ω, ht⟩, ⟨?_, ?_⟩, rfl⟩
      · exact (NumberField.isNonarchimedean_congr
          (normalizedPlaceValue_isEquiv_placeRep ⟨ω, ht⟩)).mpr hω
      · have hnew : (⟨ω, ht⟩ : (normalizedNumberFieldAdelicStructure K).Ω) ∈
            (normalizedNumberFieldAdelicStructure K).Ωfin :=
          (NumberField.isNonarchimedean_congr
            (normalizedPlaceValue_isEquiv_placeRep ⟨ω, ht⟩)).mpr hω
        have hold : x ∉ ξ.rationalUnitBall ω := not_le.mpr hx
        exact not_le.mp (mt
          (ξ.numberFieldNormalize_mem_rationalUnitBall_iff hξ ⟨ω, ht⟩ hnew x).mp hold)
  · intro hfinite x
    have hp : ((Subtype.val : (normalizedNumberFieldAdelicStructure K).Ω →
        AbsoluteValue.Place K) ⁻¹' {ω | ω ∈ (numberFieldAdelicStructure K).Ωfin ∧
        1 < ξ.norm ω (1 ⊗ₜ[K] x)}).Finite :=
      Set.Finite.preimage (f := (Subtype.val : (normalizedNumberFieldAdelicStructure K).Ω →
        AbsoluteValue.Place K)) (fun _ _ _ _ h => Subtype.ext h) (hfinite x)
    refine hp.subset ?_
    rintro ω ⟨hω, hx⟩
    refine ⟨normalizedPlace_mem_old_fin ω hω, ?_⟩
    have hnew : x ∉ (ξ.numberFieldNormalize hξ).rationalUnitBall ω := not_le.mpr hx
    exact not_le.mp (mt
      (ξ.numberFieldNormalize_mem_rationalUnitBall_iff hξ ω hω x).mpr hnew)

end NormFamily

end ArakelovGeometry
