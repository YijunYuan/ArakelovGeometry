/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.SlopesQuotient
import ArakelovGeometry.AdelicVectorBundle.DegreeMap

/-!
# Slope comparison through actual linear maps

The comparison uses the canonical restriction and quotient norms on completed
fibres and the lower-integral map height of the original rational map.
-/

open MeasureTheory Filter
open scoped TensorProduct

namespace ArakelovGeometry

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace NormFamily

omit [FiniteDimensional K F] in
/-- Restriction of a map to actual rational subspaces cannot increase its
operator norm on the completed fibres. -/
theorem operatorNorm_restriction_le (ξ : NormFamily S E) (η : NormFamily S F)
    (f : E →ₗ[K] F) (U : Submodule K E) (T : Submodule K F)
    (g : U →ₗ[K] T) (hc : T.subtype.comp g = f.comp U.subtype) (ω : S.Ω) :
    (ξ.restrict U).operatorNorm (η.restrict T) ω g ≤ ξ.operatorNorm η ω f := by
  apply (ξ.restrict U).operatorNorm_le (η.restrict T) ω g
    (ξ.operatorNorm_nonneg η ω f)
  intro z
  have hz := DFunLike.congr_fun
    (congrArg (fun p ↦ p.baseChange (S.ϕ ω).Completion) hc) z
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at hz
  simp only [restrict_norm]
  rw [hz]
  exact ξ.norm_baseChange_le_operatorNorm η ω f _

/-- Passage to compatible actual source and target quotients cannot increase
the completed operator norm. The proof compares all lifts. -/
theorem operatorNorm_quotient_le (ξ : NormFamily S E) (η : NormFamily S F)
    (f : E →ₗ[K] F) (hf : f ≠ 0) (U : Submodule K E) (T : Submodule K F)
    (g : (E ⧸ U) →ₗ[K] (F ⧸ T)) (hc : g.comp U.mkQ = T.mkQ.comp f)
    (ω : S.Ω) :
    (ξ.quotient U).operatorNorm (η.quotient T) ω g ≤ ξ.operatorNorm η ω f := by
  have hp := ξ.operatorNorm_pos η ω hf
  apply (ξ.quotient U).operatorNorm_le (η.quotient T) ω g hp.le
  intro z
  have hn : (η.quotient T).norm ω (g.baseChange (S.ϕ ω).Completion z) /
      ξ.operatorNorm η ω f ≤ ξ.quotientSeminorm U.mkQ U.mkQ_surjective ω z := by
    apply (ξ.le_quotientSeminorm_iff U.mkQ U.mkQ_surjective ω z _).mpr
    intro x hx
    apply (div_le_iff₀ hp).mpr
    have hz := DFunLike.congr_fun
      (congrArg (fun p ↦ p.baseChange (S.ϕ ω).Completion) hc) x
    simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at hz
    rw [← hx, hz, mul_comm]
    exact (η.quotient_norm_mk_le T ω _).trans
      (ξ.norm_baseChange_le_operatorNorm η ω f x)
  simpa only [quotient, pushforward, mul_comm] using (div_le_iff₀ hp).mp hn

omit [FiniteDimensional K F] in
/-- Replacing the target by the actual restriction to the range preserves
the completed evaluation bound of the original map. -/
theorem operatorNorm_rangeRestrict_le (ξ : NormFamily S E) (η : NormFamily S F)
    (f : E →ₗ[K] F) (ω : S.Ω) :
    ξ.operatorNorm (η.restrict f.range) ω f.rangeRestrict ≤ ξ.operatorNorm η ω f := by
  apply ξ.operatorNorm_le (η.restrict f.range) ω f.rangeRestrict
    (ξ.operatorNorm_nonneg η ω f)
  intro z
  have hc : f.range.subtype.comp f.rangeRestrict = f := by ext x; rfl
  have hz := DFunLike.congr_fun
    (congrArg (fun p ↦ p.baseChange (S.ϕ ω).Completion) hc) z
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at hz
  simp only [restrict_norm]
  rw [hz]
  exact ξ.norm_baseChange_le_operatorNorm η ω f z

/-- A target quotient decreases every completed evaluation norm. -/
theorem operatorNorm_postQuotient_le (ξ : NormFamily S E) (η : NormFamily S F)
    (f : E →ₗ[K] F) (T : Submodule K F) (ω : S.Ω) :
    ξ.operatorNorm (η.quotient T) ω (T.mkQ.comp f) ≤ ξ.operatorNorm η ω f := by
  apply ξ.operatorNorm_le (η.quotient T) ω (T.mkQ.comp f)
    (ξ.operatorNorm_nonneg η ω f)
  intro z
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply]
  exact (η.quotient_norm_mk_le T ω _).trans
    (ξ.norm_baseChange_le_operatorNorm η ω f z)

/-- On a surjective target, its source quotient norm bounds the identity
operator to the given target norm by the original surjection operator norm. -/
theorem operatorNorm_pushforward_id_le (ξ : NormFamily S E) (η : NormFamily S F)
    (f : E →ₗ[K] F) (hs : Function.Surjective f) (hf : f ≠ 0) (ω : S.Ω) :
    (ξ.pushforward f hs).operatorNorm η ω LinearMap.id ≤ ξ.operatorNorm η ω f := by
  have hp := ξ.operatorNorm_pos η ω hf
  apply (ξ.pushforward f hs).operatorNorm_le η ω LinearMap.id hp.le
  intro z
  simp only [LinearMap.baseChange_id, LinearMap.id_apply]
  have hn : η.norm ω z / ξ.operatorNorm η ω f ≤ ξ.quotientSeminorm f hs ω z := by
    apply (ξ.le_quotientSeminorm_iff f hs ω z _).mpr
    intro x hx
    apply (div_le_iff₀ hp).mpr
    rw [← hx, mul_comm]
    exact ξ.norm_baseChange_le_operatorNorm η ω f x
  simpa only [pushforward_norm, mul_comm] using (div_le_iff₀ hp).mp hn

end NormFamily

namespace AdelicVectorBundle

variable [S.IsProper]

/-- Dividing the determinant degree-map estimate by the common positive rank
gives the mean-slope estimate, including infinite map height. -/
theorem slope_le_slope_add_mapHeight (V : AdelicVectorBundle S E)
    (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (e : E ≃ₗ[K] F) (hr : 0 < Module.finrank K E) :
    (V.slope hS hN : EReal) ≤ (W.slope hS hN : EReal) + V.mapHeight W e.toLinearMap := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos hr
  have hf : e.toLinearMap ≠ 0 := LinearMap.ne_zero_of_injective e.injective
  by_cases ht : V.mapHeight W e.toLinearMap = ⊤
  · rw [ht, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
    exact le_top
  · have he := EReal.coe_toReal ht (ne_of_gt (V.bot_lt_mapHeight W hf))
    have hd := V.degree_le_degree_add_rank_mul_mapHeight W hS hN e
    rw [← he, ← EReal.coe_natCast, ← EReal.coe_mul, ← EReal.coe_add,
      EReal.coe_le_coe_iff] at hd
    rw [V.degree_eq_rank_mul_slope hS hN,
      W.degree_eq_rank_mul_slope hS hN, ← e.finrank_eq] at hd
    rw [← he, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have hp : (0 : ℝ) < Module.finrank K E := Nat.cast_pos.mpr hr
    nlinarith

omit [S.IsProper] in
/-- Pointwise comparison of the actual completed operator norms gives the
comparison of the stipulated lower-integral heights. -/
theorem mapHeight_le_of_operatorNorm_le
    {G : Type*} [AddCommGroup G] [Module K G] [FiniteDimensional K G]
    {H : Type*} [AddCommGroup H] [Module K H] [FiniteDimensional K H]
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (P : AdelicVectorBundle S G) (Q : AdelicVectorBundle S H)
    (f : E →ₗ[K] F) (g : G →ₗ[K] H) (hf : f ≠ 0) (hg : g ≠ 0)
    (hn : ∀ ω, P.toNormFamily.operatorNorm Q.toNormFamily ω g ≤
      V.toNormFamily.operatorNorm W.toNormFamily ω f) :
    P.mapHeight Q g ≤ V.mapHeight W f := by
  rw [P.mapHeight_eq_lowerEnvelopeIntegral Q hg,
    V.mapHeight_eq_lowerEnvelopeIntegral W hf]
  apply lowerEnvelopeIntegral_mono (Eventually.of_forall _)
  intro ω
  exact Real.log_le_log (P.toNormFamily.operatorNorm_pos Q.toNormFamily ω hg) (hn ω)

omit [S.IsProper] in
/-- The height of an actual restricted nonzero map is bounded by the height
of its ambient map. -/
theorem mapHeight_restriction_le (V : AdelicVectorBundle S E)
    (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (f : E →ₗ[K] F) (hf : f ≠ 0) (U : Submodule K E) (T : Submodule K F)
    (g : U →ₗ[K] T) (hg : g ≠ 0) (hc : T.subtype.comp g = f.comp U.subtype) :
    (V.restrictOfMeasurableBase U hS).mapHeight
      (W.restrictOfMeasurableBase T hS) g ≤ V.mapHeight W f := by
  apply V.mapHeight_le_of_operatorNorm_le W _ _ f g hf hg
  intro ω
  exact V.toNormFamily.operatorNorm_restriction_le W.toNormFamily f U T g hc ω

omit [S.IsProper] in
/-- The height of an actual compatible quotient map is bounded by its
ambient map height. -/
theorem mapHeight_quotient_le (V : AdelicVectorBundle S E)
    (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (f : E →ₗ[K] F) (hf : f ≠ 0) (U : Submodule K E) (T : Submodule K F)
    (g : (E ⧸ U) →ₗ[K] (F ⧸ T)) (hg : g ≠ 0)
    (hc : g.comp U.mkQ = T.mkQ.comp f) :
    (V.quotientOfMeasurableBase U hS).mapHeight
      (W.quotientOfMeasurableBase T hS) g ≤ V.mapHeight W f := by
  apply V.mapHeight_le_of_operatorNorm_le W _ _ f g hf hg
  intro ω
  exact V.toNormFamily.operatorNorm_quotient_le W.toNormFamily f hf U T g hc ω

/-- Source Proposition4.3.31(1), including zero injective maps and infinite
height. Each source subspace is compared with its actual range restriction. -/
theorem maximalSlope_le_maximalSlope_add_mapHeight_of_injective
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (f : E →ₗ[K] F) (hf : Function.Injective f) :
    V.maximalSlope hS hN ≤ W.maximalSlope hS hN + V.mapHeight W f := by
  by_cases hz : f = 0
  · let : Subsingleton E := ⟨fun x y ↦ hf (by simp only [hz, LinearMap.zero_apply])⟩
    rw [V.maximalSlope_eq_bot_of_finrank_eq_zero hS hN Module.finrank_zero_of_subsingleton]
    exact bot_le
  · apply V.maximalSlope_le hS hN
    intro U hU
    let e := LinearEquiv.ofInjective (f.comp U.subtype) (hf.comp U.subtype_injective)
    let T := (f.comp U.subtype).range
    let P := V.restrictOfMeasurableBase U hS
    let Q := W.restrictOfMeasurableBase T hS
    let : Nontrivial U := Module.nontrivial_of_finrank_pos hU
    have he : e.toLinearMap ≠ 0 := LinearMap.ne_zero_of_injective e.injective
    have hc : T.subtype.comp e.toLinearMap = f.comp U.subtype := by ext x; rfl
    have hn := P.slope_le_slope_add_mapHeight Q hS hN e hU
    have hh := V.mapHeight_restriction_le W hS f hz U T e.toLinearMap he hc
    have hT : 0 < Module.finrank K T := by rwa [← e.finrank_eq]
    exact hn.trans (add_le_add (W.slope_restrict_le_maximalSlope T hT hS hN) hh)

/-- A nonzero surjection compares the source minimal slope with the actual
target mean slope. Its canonical source quotient norm is constructed here. -/
theorem minimalSlope_le_slope_add_mapHeight_of_surjective
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (f : E →ₗ[K] F) (hs : Function.Surjective f) (hr : 0 < Module.finrank K F) :
    V.minimalSlope hS hN ≤ (W.slope hS hN : EReal) + V.mapHeight W f := by
  let : Nontrivial F := Module.nontrivial_of_finrank_pos hr
  have hf : f ≠ 0 := by
    intro hz
    obtain ⟨y, hy⟩ := exists_ne (0 : F)
    obtain ⟨x, hx⟩ := hs y
    exact hy (by simpa only [hz, LinearMap.zero_apply] using hx.symm)
  let hm := V.isMeasurable.pushforward_of_discrete_or_countable hS f hs
  let P := V.pushforward f hs hm
  have hn := P.slope_le_slope_add_mapHeight W hS hN (LinearEquiv.refl K F) hr
  have hi : (LinearMap.id : F →ₗ[K] F) ≠ 0 := LinearMap.ne_zero_of_injective Function.injective_id
  have hh : P.mapHeight W LinearMap.id ≤ V.mapHeight W f := by
    apply V.mapHeight_le_of_operatorNorm_le W P W f LinearMap.id hf hi
    intro ω
    exact V.toNormFamily.operatorNorm_pushforward_id_le W.toNormFamily f hs hf ω
  exact (V.minimalSlope_le_slope_pushforward f hs hm hr hS hN).trans
    (hn.trans (add_le_add le_rfl hh))

/-- Source Proposition4.3.31(3), using the nonzero actual range and the
canonical source quotient. Infinite map heights are retained. -/
theorem minimalSlope_le_maximalSlope_add_mapHeight_of_ne_zero
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (f : E →ₗ[K] F) (hf : f ≠ 0) :
    V.minimalSlope hS hN ≤ W.maximalSlope hS hN + V.mapHeight W f := by
  have hr : 0 < Module.finrank K f.range := Nat.pos_of_ne_zero (fun hz ↦
    hf (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)))
  let Q := W.restrictOfMeasurableBase f.range hS
  have hfr : f.rangeRestrict ≠ 0 := by
    intro hz
    have hc : f.range.subtype.comp f.rangeRestrict = f := by ext x; rfl
    rw [hz, LinearMap.comp_zero] at hc
    exact hf hc.symm
  have hn := V.minimalSlope_le_slope_add_mapHeight_of_surjective Q hS hN
    f.rangeRestrict f.surjective_rangeRestrict hr
  have hh : V.mapHeight Q f.rangeRestrict ≤ V.mapHeight W f := by
    apply V.mapHeight_le_of_operatorNorm_le W V Q f f.rangeRestrict hf hfr
    intro ω
    exact V.toNormFamily.operatorNorm_rangeRestrict_le W.toNormFamily f ω
  exact hn.trans (add_le_add (W.slope_restrict_le_maximalSlope f.range hr hS hN) hh)

/-- The finite-height part of source Proposition4.3.31(2). The explicit
finite-height premise is used to translate the actual quotient-mean infimum;
the infinite-height case additionally requires the slope-finiteness producer. -/
theorem minimalSlope_le_minimalSlope_add_mapHeight_of_surjective_of_ne_top
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (f : E →ₗ[K] F) (hs : Function.Surjective f) (hf : f ≠ 0)
    (ht : V.mapHeight W f ≠ ⊤) :
    V.minimalSlope hS hN ≤ W.minimalSlope hS hN + V.mapHeight W f := by
  have he := EReal.coe_toReal ht (ne_of_gt (V.bot_lt_mapHeight W hf))
  rw [← he]
  apply (EReal.sub_le_iff_le_add
    (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).mp
  rw [W.minimalSlope_eq_iInf_slope_quotient hS hN]
  apply le_iInf
  intro U
  let Q := W.quotientOfMeasurableBase U.val hS
  let g := U.val.mkQ.comp f
  have hgSurj : Function.Surjective g := U.val.mkQ_surjective.comp hs
  let : Nontrivial (F ⧸ U.val) := Module.nontrivial_of_finrank_pos U.property
  have hg : g ≠ 0 := by
    intro hz
    obtain ⟨y, hy⟩ := exists_ne (0 : F ⧸ U.val)
    obtain ⟨x, hx⟩ := hgSurj y
    exact hy (by simpa only [hz, LinearMap.zero_apply] using hx.symm)
  have hn := V.minimalSlope_le_slope_add_mapHeight_of_surjective Q hS hN g hgSurj U.property
  have hh : V.mapHeight Q g ≤ V.mapHeight W f := by
    apply V.mapHeight_le_of_operatorNorm_le W V Q f g hf hg
    intro ω
    exact V.toNormFamily.operatorNorm_postQuotient_le W.toNormFamily f U.val ω
  apply (EReal.sub_le_iff_le_add
    (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).mpr
  rw [he]
  exact hn.trans (add_le_add le_rfl hh)

end AdelicVectorBundle

end ArakelovGeometry
