/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Game.Payoff

/-!
# Semistability of the adelic slope game

Subspaces of an interval quotient correspond to its intermediate subspaces.
The game's semistability criterion therefore uses the original minimal slopes.
-/

@[expose] public section

open HarderNarasimhan

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S)
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]

/-- The initial subintervals of the game describe all actual restrictions
of its subquotient. Hence game semistability is the existing minimal-slope criterion. -/
theorem isSemistable_restrict_maximalSlopePayoff_iff (I : StrictIntvl (Submodule K V)) :
    ((V.maximalSlopePayoff).restrict I).IsSemistable ↔
      ∀ Z : Submodule K (I.right ⧸ I.left.comap I.right.subtype), Z ≠ ⊥ →
        ((((V.restrictOfNormMeasurability I.right).quotientOfNormMeasurability
          (I.left.comap I.right.subtype)).restrictOfNormMeasurability Z).minimalSlope) ≤
        ((V.restrictOfNormMeasurability I.right).quotientOfNormMeasurability
          (I.left.comap I.right.subtype)).minimalSlope := by
  have hcriterion : ((V.maximalSlopePayoff).restrict I).IsSemistable ↔
      ∀ U : Submodule K V, I.left < U → U ≤ I.right →
        ((V.restrictOfNormMeasurability U).quotientOfNormMeasurability
          (I.left.comap U.subtype)).minimalSlope ≤
        ((V.restrictOfNormMeasurability I.right).quotientOfNormMeasurability
          (I.left.comap I.right.subtype)).minimalSlope := by
    constructor
    · intro h U hAU hUB
      have ht := h.not_lt (⟨U, hAU.le, hUB⟩ : ↥I) hAU
      simp only [PayoffFunction.A_restrict_apply, StrictIntvl.ofSub_top,
        V.A_maximalSlopePayoff_eq_minimalSlope] at ht
      exact le_of_not_gt ht
    · intro h
      constructor
      intro U hU
      simp only [PayoffFunction.A_restrict_apply, StrictIntvl.ofSub_top,
        V.A_maximalSlopePayoff_eq_minimalSlope]
      exact not_lt_of_ge (h U hU U.prop.2)
  rw [hcriterion]
  let T := I.left.comap I.right.subtype
  constructor
  · intro h Z hZ
    let R := Z.comap T.mkQ
    let U := R.map I.right.subtype
    have hAU : I.left ≤ U := by
      have hm := Submodule.map_mono (f := I.right.subtype) (T.le_comap_mkQ Z)
      simpa only [T, Submodule.map_comap_subtype, inf_eq_right.mpr I.lt.le] using hm
    have hUB : U ≤ I.right := Submodule.map_subtype_le I.right R
    have hcomap : U.comap I.right.subtype = R :=
      Submodule.comap_map_eq_of_injective I.right.subtype_injective R
    have hRange : (T.mkQ.comp (U.comap I.right.subtype).subtype).range = Z := by
      rw [LinearMap.range_comp, Submodule.range_subtype, hcomap]
      exact Submodule.map_comap_eq_of_surjective T.mkQ_surjective Z
    have hAU' : I.left < U := hAU.lt_of_ne (by
      intro he
      have he' : U.comap I.right.subtype = T := congrArg (fun P ↦ P.comap I.right.subtype) he.symm
      apply hZ
      rw [← hRange, LinearMap.range_comp, Submodule.range_subtype, he', Submodule.mkQ_map_self])
    have hb := h U hAU' hUB
    rw [← V.minimalSlope_subquotient_restrict_range I.left U I.right hAU hUB,
      hRange] at hb
    exact hb
  · intro h U hAU hUB
    let R := U.comap I.right.subtype
    have hZ : (T.mkQ.comp R.subtype).range ≠ ⊥ := by
      intro hz
      have hmap : R.map T.mkQ = ⊥ := by
        simpa only [LinearMap.range_comp, Submodule.range_subtype] using hz
      have hRT : R ≤ T := by
        have hm := Submodule.map_le_iff_le_comap.mp hmap.le
        simpa only [Submodule.comap_bot, Submodule.ker_mkQ] using hm
      have hm := Submodule.map_mono (f := I.right.subtype) hRT
      have hUA : U ≤ I.left := by
        simpa only [R, T, Submodule.map_comap_subtype,
          inf_eq_right.mpr hUB, inf_eq_right.mpr I.lt.le] using hm
      exact hAU.not_ge hUA
    have hb := h (T.mkQ.comp R.subtype).range hZ
    rw [V.minimalSlope_subquotient_restrict_range I.left U I.right hAU.le hUB] at hb
    exact hb

end

end ArakelovGeometry.AdelicVectorBundle
