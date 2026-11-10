/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.RestrictionFunctor

/-!
# Slopes of actual adelic vector bundles

The mean slope is real. The maximal slope is the extended-real supremum over
nonzero actual restrictions. Following source equation (4.45), minimal slope
is the infimum of maximal slopes of nonzero actual quotients. No boundedness
or attainment premise is included in these definitions.
-/

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace NormFamily

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- A completed isometry restricts to the canonical equivalence of each
rational subspace with its image, with the actual restricted norms. -/
theorem restrict_map_equiv_norm_eq (ξ : NormFamily S E) (η : NormFamily S F)
    (e : E ≃ₗ[K] F) (W : Submodule K E) (ω : S.Ω)
    (he : ∀ x, η.norm ω (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = ξ.norm ω x)
    (z : (S.ϕ ω).Completion ⊗[K] W) :
    (η.restrict (W.map e.toLinearMap)).norm ω
        ((e.submoduleMap W).toLinearMap.baseChange (S.ϕ ω).Completion z) =
      (ξ.restrict W).norm ω z := by
  have hc : (W.map e.toLinearMap).subtype.comp (e.submoduleMap W).toLinearMap =
      e.toLinearMap.comp W.subtype := by
    ext x
    rfl
  have hz := DFunLike.congr_fun
    (congrArg (fun f ↦ f.baseChange (S.ϕ ω).Completion) hc) z
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at hz
  simp only [restrict_norm]
  rw [hz]
  exact he _

omit [FiniteDimensional K F] in
/-- Every actual quotient map has the source's canonical kernel normal form
as an isometry on the actual completed quotient fibres. -/
theorem quotient_ker_equiv_norm_eq (ξ : NormFamily S E)
    (π : E →ₗ[K] F) (hπ : Function.Surjective π) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⧸ π.ker)) :
    (ξ.pushforward π hπ).norm ω
      ((π.quotKerEquivOfSurjective hπ).toLinearMap.baseChange (S.ϕ ω).Completion z) =
      (ξ.quotient π.ker).norm ω z := by
  let e := π.quotKerEquivOfSurjective hπ
  let eω := e.baseChange K (S.ϕ ω).Completion _ _
  have hc : e.toLinearMap.comp π.ker.mkQ = π := by
    ext x
    exact LinearMap.quotKerEquivOfSurjective_apply_mk π hπ x
  have hf (x : (S.ϕ ω).Completion ⊗[K] E) :
      eω (π.ker.mkQ.baseChange (S.ϕ ω).Completion x) =
        π.baseChange (S.ϕ ω).Completion x := by
    change e.toLinearMap.baseChange (S.ϕ ω).Completion
      (π.ker.mkQ.baseChange (S.ϕ ω).Completion x) = π.baseChange (S.ϕ ω).Completion x
    simpa only [LinearMap.baseChange_comp, LinearMap.comp_apply] using
      DFunLike.congr_fun (congrArg (fun f ↦ f.baseChange (S.ϕ ω).Completion) hc) x
  apply le_antisymm
  · apply (ξ.le_quotientSeminorm_iff π.ker.mkQ π.ker.mkQ_surjective ω z _).mpr
    intro x hx
    change (ξ.pushforward π hπ).norm ω (eω z) ≤ ξ.norm ω x
    rw [← hx, hf]
    exact ξ.pushforward_norm_le π hπ ω x
  · apply (ξ.le_quotientSeminorm_iff π hπ ω (eω z) _).mpr
    intro x hx
    have hz : π.ker.mkQ.baseChange (S.ϕ ω).Completion x = z :=
      eω.injective ((hf x).trans hx)
    rw [← hz]
    exact ξ.quotient_norm_mk_le π.ker ω x

/-- An actual completed isometry induces the canonical isometry on each
quotient by a rational subspace and its image. The infima of lift norms are
compared directly; no existence of a norm-minimizing lift is assumed. -/
theorem quotient_map_equiv_norm_eq (ξ : NormFamily S E) (η : NormFamily S F)
    (e : E ≃ₗ[K] F) (U : Submodule K E) (ω : S.Ω)
    (he : ∀ x, η.norm ω (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = ξ.norm ω x)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⧸ U)) :
    (η.quotient (U.map e.toLinearMap)).norm ω
      ((Submodule.Quotient.equiv U (U.map e.toLinearMap) e rfl).toLinearMap.baseChange
        (S.ϕ ω).Completion z) = (ξ.quotient U).norm ω z := by
  let T := U.map e.toLinearMap
  let q := Submodule.Quotient.equiv U T e rfl
  let qω := q.baseChange K (S.ϕ ω).Completion _ _
  let eω := e.baseChange K (S.ϕ ω).Completion E F
  have hc : q.toLinearMap.comp U.mkQ = T.mkQ.comp e.toLinearMap := by
    ext x
    simp [q, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  have hf (x : (S.ϕ ω).Completion ⊗[K] E) :
      qω (U.mkQ.baseChange (S.ϕ ω).Completion x) =
        T.mkQ.baseChange (S.ϕ ω).Completion (eω x) := by
    change q.toLinearMap.baseChange (S.ϕ ω).Completion
      (U.mkQ.baseChange (S.ϕ ω).Completion x) =
        T.mkQ.baseChange (S.ϕ ω).Completion
          (e.toLinearMap.baseChange (S.ϕ ω).Completion x)
    simpa only [LinearMap.baseChange_comp, LinearMap.comp_apply] using
      DFunLike.congr_fun (congrArg (fun f ↦ f.baseChange (S.ϕ ω).Completion) hc) x
  have hen (x : (S.ϕ ω).Completion ⊗[K] E) : η.norm ω (eω x) = ξ.norm ω x := he x
  change (η.quotient T).norm ω (qω z) = (ξ.quotient U).norm ω z
  apply le_antisymm
  · apply (ξ.le_quotientSeminorm_iff U.mkQ U.mkQ_surjective ω z _).mpr
    intro x hx
    rw [← hx, hf]
    exact (η.quotient_norm_mk_le T ω (eω x)).trans_eq (hen x)
  · apply (η.le_quotientSeminorm_iff T.mkQ T.mkQ_surjective ω (qω z) _).mpr
    intro y hy
    obtain ⟨x, rfl⟩ := eω.surjective y
    have hx : U.mkQ.baseChange (S.ϕ ω).Completion x = z :=
      qω.injective ((hf x).trans hy)
    rw [← hx]
    exact (ξ.quotient_norm_mk_le U ω x).trans_eq (hen x).symm

end NormFamily

namespace AdelicVectorBundle

variable [S.IsProper]

/-- The real mean slope, with the source rank-zero value `0`. -/
def slope (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) : ℝ :=
  V.degree hS hN / Module.finrank K E

/-- The extended-real supremum of slopes of all nonzero actual restrictions. -/
def maximalSlope (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) : EReal :=
  ⨆ W : {W : Submodule K E // 0 < Module.finrank K W},
    ((V.restrictOfMeasurableBase W.val hS).slope hS hN : EReal)

/-- Source equation (4.45): the infimum of maximal slopes of all nonzero
actual quotients. Every quotient can be represented by its rational kernel. -/
def minimalSlope (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) : EReal :=
  ⨅ W : {W : Submodule K E // 0 < Module.finrank K (E ⧸ W)},
    (V.quotientOfMeasurableBase W.val hS).maximalSlope hS hN

/-- The zero-rank mean slope is zero as in the source convention. -/
theorem slope_eq_zero_of_finrank_eq_zero (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : Module.finrank K E = 0) : V.slope hS hN = 0 := by
  simp only [slope, hr, Nat.cast_zero, div_zero]

/-- There are no nonzero subspaces of a zero-rank bundle, so the supremum
is minus infinity. -/
theorem maximalSlope_eq_bot_of_finrank_eq_zero (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : Module.finrank K E = 0) : V.maximalSlope hS hN = ⊥ := by
  let : IsEmpty {W : Submodule K E // 0 < Module.finrank K W} := ⟨fun W ↦ by
    have hle := W.val.finrank_le
    rw [hr] at hle
    exact (not_lt_of_ge hle) W.property⟩
  exact iSup_of_empty _

/-- There are no nonzero quotients of a zero-rank bundle, so the infimum
is plus infinity. -/
theorem minimalSlope_eq_top_of_finrank_eq_zero (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : Module.finrank K E = 0) : V.minimalSlope hS hN = ⊤ := by
  let : IsEmpty {W : Submodule K E // 0 < Module.finrank K (E ⧸ W)} := ⟨fun W ↦ by
    have h := W.val.finrank_quotient_add_finrank
    rw [hr] at h
    have hz : Module.finrank K (E ⧸ W.val) = 0 := by omega
    exact (ne_of_gt W.property) hz⟩
  exact iInf_of_empty _

/-- Degree is rank times mean slope, also at rank zero. -/
theorem degree_eq_rank_mul_slope (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.degree hS hN = (Module.finrank K E : ℝ) * V.slope hS hN := by
  by_cases hr : Module.finrank K E = 0
  · rw [V.degree_eq_zero_of_finrank_eq_zero hS hN hr, hr, Nat.cast_zero, zero_mul]
  · rw [slope, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hr)]

/-- Actual completed isometries preserve the real mean slope. -/
theorem slope_eq_of_completed_isometry (V : AdelicVectorBundle S E)
    (W : AdelicVectorBundle S F) (e : E ≃ₗ[K] F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (he : ∀ ω x, W.toNormFamily.norm ω
      (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = V.toNormFamily.norm ω x) :
    V.slope hS hN = W.slope hS hN := by
  rw [slope, slope, V.degree_eq_of_completed_isometry W e hS hN he, e.finrank_eq]

/-- Every nonzero actual restricted slope is bounded by the maximal slope. -/
theorem slope_restrict_le_maximalSlope (V : AdelicVectorBundle S E)
    (W : Submodule K E) (hW : 0 < Module.finrank K W)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ((V.restrictOfMeasurableBase W hS).slope hS hN : EReal) ≤ V.maximalSlope hS hN :=
  le_iSup (fun U : {W : Submodule K E // 0 < Module.finrank K W} ↦
    ((V.restrictOfMeasurableBase U.val hS).slope hS hN : EReal)) ⟨W, hW⟩

/-- A bound for every nonzero actual restriction bounds the maximal slope. -/
theorem maximalSlope_le (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) {a : EReal}
    (ha : ∀ W : Submodule K E, 0 < Module.finrank K W →
      ((V.restrictOfMeasurableBase W hS).slope hS hN : EReal) ≤ a) :
    V.maximalSlope hS hN ≤ a :=
  iSup_le (fun W ↦ ha W.val W.property)

/-- The total actual restriction has the ambient mean slope. -/
theorem slope_restrict_top (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.restrictOfMeasurableBase ⊤ hS).slope hS hN = V.slope hS hN := by
  rw [slope, slope, V.degree_restrict_top hS hN, Submodule.topEquiv.finrank_eq]

/-- For nonzero bundles, the identity subspace gives mean slope at most
maximal slope. The dimensional qualification is essential at rank zero. -/
theorem slope_le_maximalSlope (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : 0 < Module.finrank K E) : (V.slope hS hN : EReal) ≤ V.maximalSlope hS hN := by
  have ht : 0 < Module.finrank K (⊤ : Submodule K E) := by
    rw [Submodule.topEquiv.finrank_eq]
    exact hr
  simpa only [V.slope_restrict_top hS hN] using V.slope_restrict_le_maximalSlope ⊤ ht hS hN

/-- A nonzero bundle's maximal slope cannot equal minus infinity. -/
theorem bot_lt_maximalSlope (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : 0 < Module.finrank K E) : ⊥ < V.maximalSlope hS hN :=
  (EReal.bot_lt_coe _).trans_le (V.slope_le_maximalSlope hS hN hr)

/-- The source minimal slope is bounded by the maximal slope of every
nonzero actual quotient. -/
theorem minimalSlope_le_maximalSlope_quotient (V : AdelicVectorBundle S E)
    (W : Submodule K E) (hW : 0 < Module.finrank K (E ⧸ W))
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.minimalSlope hS hN ≤ (V.quotientOfMeasurableBase W hS).maximalSlope hS hN :=
  iInf_le (fun U : {W : Submodule K E // 0 < Module.finrank K (E ⧸ W)} ↦
    (V.quotientOfMeasurableBase U.val hS).maximalSlope hS hN) ⟨W, hW⟩

/-- A lower bound for every nonzero actual quotient maximal slope bounds
the source minimal slope from below. -/
theorem le_minimalSlope (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) {a : EReal}
    (ha : ∀ W : Submodule K E, 0 < Module.finrank K (E ⧸ W) →
      a ≤ (V.quotientOfMeasurableBase W hS).maximalSlope hS hN) :
    a ≤ V.minimalSlope hS hN :=
  le_iInf (fun W ↦ ha W.val W.property)

/-- The slope supremum is functorial under an actual completed isometry:
each source subspace transports to its actual image subspace. -/
theorem maximalSlope_le_of_completed_isometry (V : AdelicVectorBundle S E)
    (W : AdelicVectorBundle S F) (e : E ≃ₗ[K] F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (he : ∀ ω x, W.toNormFamily.norm ω
      (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = V.toNormFamily.norm ω x) :
    V.maximalSlope hS hN ≤ W.maximalSlope hS hN := by
  apply V.maximalSlope_le hS hN
  intro U hU
  have hr := (e.submoduleMap U).finrank_eq
  have hu : (V.restrictOfMeasurableBase U hS).slope hS hN =
      (W.restrictOfMeasurableBase (U.map e.toLinearMap) hS).slope hS hN := by
    apply slope_eq_of_completed_isometry _ _ (e.submoduleMap U) hS hN
    intro ω z
    simp only [restrictOfMeasurableBase_toNormFamily]
    exact V.toNormFamily.restrict_map_equiv_norm_eq W.toNormFamily e U ω (he ω) z
  rw [hu]
  exact W.slope_restrict_le_maximalSlope (U.map e.toLinearMap) (hr ▸ hU) hS hN

/-- Actual completed isometries preserve maximal slopes, including both
infinite values and the zero-bundle convention. -/
theorem maximalSlope_eq_of_completed_isometry (V : AdelicVectorBundle S E)
    (W : AdelicVectorBundle S F) (e : E ≃ₗ[K] F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (he : ∀ ω x, W.toNormFamily.norm ω
      (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = V.toNormFamily.norm ω x) :
    V.maximalSlope hS hN = W.maximalSlope hS hN := by
  apply le_antisymm (V.maximalSlope_le_of_completed_isometry W e hS hN he)
  apply W.maximalSlope_le_of_completed_isometry V e.symm hS hN
  intro ω y
  let eω := e.baseChange K (S.ϕ ω).Completion E F
  change V.toNormFamily.norm ω (eω.symm y) = W.toNormFamily.norm ω y
  have h := he ω (eω.symm y)
  change W.toNormFamily.norm ω (eω (eω.symm y)) = V.toNormFamily.norm ω (eω.symm y) at h
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

/-- The actual quotient by zero has the original maximal slope, so the
identity quotient used in source equation (4.45) is present. -/
theorem maximalSlope_quotient_bot (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.quotientOfMeasurableBase ⊥ hS).maximalSlope hS hN = V.maximalSlope hS hN := by
  symm
  let e : E ≃ₗ[K] E ⧸ (⊥ : Submodule K E) :=
    LinearEquiv.ofBijective (⊥ : Submodule K E).mkQ
      ⟨LinearMap.ker_eq_bot.mp (Submodule.ker_mkQ ⊥), Submodule.mkQ_surjective ⊥⟩
  apply maximalSlope_eq_of_completed_isometry _ _ e hS hN
  intro ω z
  exact V.toNormFamily.quotient_bot_norm_mk ω z

/-- For a nonzero bundle the identity quotient gives source minimal slope
at most maximal slope. The zero-bundle qualification remains visible. -/
theorem minimalSlope_le_maximalSlope (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : 0 < Module.finrank K E) : V.minimalSlope hS hN ≤ V.maximalSlope hS hN := by
  have hq : 0 < Module.finrank K (E ⧸ (⊥ : Submodule K E)) := by
    have h := (⊥ : Submodule K E).finrank_quotient_add_finrank
    rw [finrank_bot, add_zero] at h
    rwa [h]
  simpa only [V.maximalSlope_quotient_bot hS hN] using
    V.minimalSlope_le_maximalSlope_quotient ⊥ hq hS hN

/-- Mean slope agrees with degree in rank one. -/
theorem slope_eq_degree_of_finrank_one (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : Module.finrank K E = 1) : V.slope hS hN = V.degree hS hN := by
  simp only [slope, hr, Nat.cast_one, div_one]

/-- Every actual surjective quotient has the mean slope of the canonical
quotient by its kernel. -/
theorem slope_pushforward_eq_quotient_ker (V : AdelicVectorBundle S E)
    (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (hm : (V.toNormFamily.pushforward π hπ).IsMeasurable)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.pushforward π hπ hm).slope hS hN =
      (V.quotientOfMeasurableBase π.ker hS).slope hS hN := by
  symm
  apply slope_eq_of_completed_isometry _ _ (π.quotKerEquivOfSurjective hπ) hS hN
  intro ω z
  exact V.toNormFamily.quotient_ker_equiv_norm_eq π hπ ω z

/-- Every actual surjective quotient has the maximal slope of the canonical
quotient by its kernel, independently of the chosen target vector space. -/
theorem maximalSlope_pushforward_eq_quotient_ker (V : AdelicVectorBundle S E)
    (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (hm : (V.toNormFamily.pushforward π hπ).IsMeasurable)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.pushforward π hπ hm).maximalSlope hS hN =
      (V.quotientOfMeasurableBase π.ker hS).maximalSlope hS hN := by
  symm
  apply maximalSlope_eq_of_completed_isometry _ _ (π.quotKerEquivOfSurjective hπ) hS hN
  intro ω z
  exact V.toNormFamily.quotient_ker_equiv_norm_eq π hπ ω z

/-- Canonical kernel indexing in (4.45) includes every nonzero source quotient
with its actual quotient norm, including targets in another universe. -/
theorem minimalSlope_le_maximalSlope_pushforward (V : AdelicVectorBundle S E)
    (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (hm : (V.toNormFamily.pushforward π hπ).IsMeasurable)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : 0 < Module.finrank K F) :
    V.minimalSlope hS hN ≤ (V.pushforward π hπ hm).maximalSlope hS hN := by
  rw [V.maximalSlope_pushforward_eq_quotient_ker π hπ hm hS hN]
  apply V.minimalSlope_le_maximalSlope_quotient π.ker _ hS hN
  rwa [(π.quotKerEquivOfSurjective hπ).finrank_eq]

/-- Transporting every nonzero kernel quotient along an actual isometry
bounds the target minimal slope by the source minimal slope. -/
theorem minimalSlope_ge_of_completed_isometry (V : AdelicVectorBundle S E)
    (W : AdelicVectorBundle S F) (e : E ≃ₗ[K] F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (he : ∀ ω x, W.toNormFamily.norm ω
      (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = V.toNormFamily.norm ω x) :
    W.minimalSlope hS hN ≤ V.minimalSlope hS hN := by
  apply V.le_minimalSlope hS hN
  intro U hU
  let q := Submodule.Quotient.equiv U (U.map e.toLinearMap) e rfl
  have hr := q.finrank_eq
  have hq : (V.quotientOfMeasurableBase U hS).maximalSlope hS hN =
      (W.quotientOfMeasurableBase (U.map e.toLinearMap) hS).maximalSlope hS hN := by
    apply maximalSlope_eq_of_completed_isometry _ _ q hS hN
    intro ω z
    exact V.toNormFamily.quotient_map_equiv_norm_eq W.toNormFamily e U ω (he ω) z
  rw [hq]
  exact W.minimalSlope_le_maximalSlope_quotient (U.map e.toLinearMap) (hr ▸ hU) hS hN

/-- Actual completed isometries preserve the source minimal slope, retaining
all extended-real values and the plus-infinity zero-bundle convention. -/
theorem minimalSlope_eq_of_completed_isometry (V : AdelicVectorBundle S E)
    (W : AdelicVectorBundle S F) (e : E ≃ₗ[K] F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (he : ∀ ω x, W.toNormFamily.norm ω
      (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = V.toNormFamily.norm ω x) :
    V.minimalSlope hS hN = W.minimalSlope hS hN := by
  apply le_antisymm _ (V.minimalSlope_ge_of_completed_isometry W e hS hN he)
  apply W.minimalSlope_ge_of_completed_isometry V e.symm hS hN
  intro ω y
  let eω := e.baseChange K (S.ϕ ω).Completion E F
  change V.toNormFamily.norm ω (eω.symm y) = W.toNormFamily.norm ω y
  have h := he ω (eω.symm y)
  change W.toNormFamily.norm ω (eω (eω.symm y)) = V.toNormFamily.norm ω (eω.symm y) at h
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

end AdelicVectorBundle

end

end ArakelovGeometry
