/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.GeneralHNOrdered
import ArakelovGeometry.AdelicVectorBundle.GeneralHNFunctoriality
import ArakelovGeometry.AdelicVectorBundle.RestrictionFunctor

/-!
# Actual slopes and intrinsic filtrations of general filtration terms

An ordered jump is the actual minimum slope of its filtration term.
Canonical completed restriction norms identify the intrinsic filtration
of that term with the ambient filtration above its level.
-/

namespace ArakelovGeometry

noncomputable section

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace AdelicVectorBundle

variable [S.IsProper] (V : AdelicVectorBundle S E)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)

/-- The term at an actual ordered jump has that jump as its actual minimum.
The rank cut proves positive rank before the true minimum is lifted to a real. -/
theorem minimalSlope_restrict_generalHNFiltration_orderedSlope
    (j : Fin (Module.finrank K E)) :
    (V.restrictOfMeasurableBase
      (V.generalHNFiltration hS hN (V.generalHNOrderedSlope hS hN j)) hS).minimalSlope
        hS hN = (V.generalHNOrderedSlope hS hN j : EReal) := by
  let μ := V.generalHNOrderedSlope hS hN j
  let U := V.generalHNFiltration hS hN μ
  have hj : j.val < Module.finrank K U :=
    V.lt_finrank_generalHNFiltration_orderedSlope hS hN j
  have hpos : 0 < Module.finrank K U := (Nat.zero_le j.val).trans_lt hj
  obtain ⟨c, hc⟩ := (V.restrictOfMeasurableBase U hS).exists_minimalSlope_eq_coe hS hN hpos
  have hlo : (μ : EReal) ≤ (V.restrictOfMeasurableBase U hS).minimalSlope hS hN :=
    V.le_minimalSlope_restrict_generalHNFiltration hS hN μ
  have hle : U ≤ V.generalHNFiltration hS hN c :=
    V.le_generalHNFiltration_of_le_minimalSlope_restrict hS hN U c hc.ge
  have hcμ : c ≤ μ :=
    (V.le_generalHNOrderedSlope_iff_lt_filtration_finrank hS hN c j).mpr
      (hj.trans_le (Submodule.finrank_mono hle))
  change (V.restrictOfMeasurableBase U hS).minimalSlope hS hN = (μ : EReal)
  rw [hc] at hlo ⊢
  exact le_antisymm (EReal.coe_le_coe hcμ) hlo

/-- Canonical nested restrictions have identical actual minimal slopes.
The comparison is the completed norm identity for the canonical subtype equivalence. -/
theorem minimalSlope_restrict_restrict (U W : Submodule K E) (hUW : U ≤ W) :
    ((V.restrictOfMeasurableBase W hS).restrictOfMeasurableBase
      (U.comap W.subtype) hS).minimalSlope hS hN =
      (V.restrictOfMeasurableBase U hS).minimalSlope hS hN := by
  apply minimalSlope_eq_of_completed_isometry _ _ (Submodule.comapSubtypeEquivOfLe hUW)
    hS hN
  intro ω z
  exact (V.toNormFamily.restrict_restrict_norm_eq U W hUW ω z).symm

/-- The actual canonical inclusion contracts every completed vector, so
the intrinsic filtration of any restriction maps into the ambient one. -/
theorem map_generalHNFiltration_restrict_le (U : Submodule K E) (s : ℝ) :
    ((V.restrictOfMeasurableBase U hS).generalHNFiltration hS hN s).map U.subtype ≤
      V.generalHNFiltration hS hN s := by
  by_cases hf : U.subtype = 0
  · simp only [hf, Submodule.map_zero]
    exact bot_le
  · have hh : (V.restrictOfMeasurableBase U hS).mapHeight V U.subtype ≤ 0 := by
      apply mapHeight_le_zero_of_completed_contraction
      intro ω z
      exact le_rfl
    simpa only [sub_zero] using
      (V.restrictOfMeasurableBase U hS).map_generalHNFiltration_le_of_mapHeight_le
        V hS hN U.subtype hf 0 hh s

/-- The intrinsic actual filtration of an ambient term is its whole
space below that term's level, including a zero ambient term. -/
theorem generalHNFiltration_restrict_term_eq_top (t s : ℝ) (hst : s ≤ t) :
    (V.restrictOfMeasurableBase (V.generalHNFiltration hS hN t) hS).generalHNFiltration
      hS hN s = ⊤ := by
  apply generalHNFiltration_eq_top_of_le_minimalSlope
  exact (EReal.coe_le_coe hst).trans
    (V.le_minimalSlope_restrict_generalHNFiltration hS hN t)

/-- Above an ambient term's level, its intrinsic actual filtration is
exactly the ambient one under the canonical subtype map. -/
theorem map_generalHNFiltration_restrict_term_eq (t s : ℝ) (hts : t ≤ s) :
    ((V.restrictOfMeasurableBase (V.generalHNFiltration hS hN t) hS).generalHNFiltration
      hS hN s).map (V.generalHNFiltration hS hN t).subtype =
        V.generalHNFiltration hS hN s := by
  apply le_antisymm (V.map_generalHNFiltration_restrict_le hS hN _ s)
  let U := V.generalHNFiltration hS hN t
  let B := V.generalHNFiltration hS hN s
  have hBU : B ≤ U := V.antitone_generalHNFiltration hS hN hts
  have hmin : (s : EReal) ≤
      ((V.restrictOfMeasurableBase U hS).restrictOfMeasurableBase
        (B.comap U.subtype) hS).minimalSlope hS hN := by
    rw [V.minimalSlope_restrict_restrict hS hN B U hBU]
    exact V.le_minimalSlope_restrict_generalHNFiltration hS hN s
  have hle := le_generalHNFiltration_of_le_minimalSlope_restrict
    (V.restrictOfMeasurableBase U hS) hS hN (B.comap U.subtype) s hmin
  have hmap := Submodule.map_mono hle (f := U.subtype)
  rw [Submodule.map_comap_subtype, inf_eq_right.mpr hBU] at hmap
  exact hmap

variable {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- A genuine injection with any real upper bound on its actual height
compares the corresponding actual ordered slots. Injectivity and an
attained nonzero source slot prove that the map is nonzero. -/
theorem generalHNOrderedSlope_le_of_injective_of_mapHeight_le
    (W : AdelicVectorBundle S F) (f : E →ₗ[K] F) (hi : Function.Injective f)
    (c : ℝ) (hh : V.mapHeight W f ≤ (c : EReal)) (j : Fin (Module.finrank K E)) :
    V.generalHNOrderedSlope hS hN j ≤
      W.generalHNOrderedSlope hS hN
        (j.castLE (LinearMap.finrank_le_finrank_of_injective hi)) + c := by
  let μ := V.generalHNOrderedSlope hS hN j
  let U := V.generalHNFiltration hS hN μ
  have hj : j.val < Module.finrank K U :=
    V.lt_finrank_generalHNFiltration_orderedSlope hS hN j
  have hm : Module.finrank K U ≤ Module.finrank K (U.map f) :=
    LinearMap.finrank_le_finrank_of_injective (f.submoduleMap_injective hi U)
  have hf : f ≠ 0 := by
    intro hz
    have hp := hj.trans_le hm
    rw [hz, Submodule.map_zero, finrank_bot] at hp
    exact Nat.not_lt_zero j.val hp
  have hle := V.map_generalHNFiltration_le_of_mapHeight_le W hS hN f hf c hh μ
  have hr := hj.trans_le (hm.trans (Submodule.finrank_mono hle))
  have hs := (W.le_generalHNOrderedSlope_iff_lt_filtration_finrank hS hN (μ - c)
    (j.castLE (LinearMap.finrank_le_finrank_of_injective hi))).mpr hr
  exact sub_le_iff_le_add.mp hs

/-- Source finite-height injection comparison using the actual extended
height. Its negative-infinite endpoint is excluded by the genuine nonzero
map before lifting the height to a real number. -/
theorem generalHNOrderedSlope_le_of_injective
    (W : AdelicVectorBundle S F) (f : E →ₗ[K] F) (hi : Function.Injective f)
    (hh : V.mapHeight W f ≠ ⊤) (j : Fin (Module.finrank K E)) :
    (V.generalHNOrderedSlope hS hN j : EReal) ≤
      (W.generalHNOrderedSlope hS hN
        (j.castLE (LinearMap.finrank_le_finrank_of_injective hi)) : EReal) +
          V.mapHeight W f := by
  have hf : f ≠ 0 := by
    intro hz
    have hm : Module.finrank K (⊤ : Submodule K E) ≤
        Module.finrank K ((⊤ : Submodule K E).map f) :=
      LinearMap.finrank_le_finrank_of_injective (f.submoduleMap_injective hi ⊤)
    rw [hz, Submodule.map_zero, finrank_bot, finrank_top] at hm
    exact (Nat.not_lt_zero j.val) (j.isLt.trans_le hm)
  have hb : V.mapHeight W f ≠ ⊥ := (V.bot_lt_mapHeight W hf).ne'
  obtain ⟨c, hc⟩ : ∃ c : ℝ, V.mapHeight W f = (c : EReal) := by
    lift V.mapHeight W f to ℝ using ⟨hh, hb⟩ with c
    exact ⟨c, rfl⟩
  rw [hc, ← EReal.coe_add]
  exact EReal.coe_le_coe
    (V.generalHNOrderedSlope_le_of_injective_of_mapHeight_le hS hN W f hi c hc.le j)

/-- Every actual restricted bundle has each ordered slope at most the
same ambient slot. The completed canonical inclusion gives height at
most zero, with no height or Hermitianity hypothesis supplied. -/
theorem generalHNOrderedSlope_restrict_le (U : Submodule K E)
    (j : Fin (Module.finrank K U)) :
    (V.restrictOfMeasurableBase U hS).generalHNOrderedSlope hS hN j ≤
      V.generalHNOrderedSlope hS hN (j.castLE U.finrank_le) := by
  have hh : (V.restrictOfMeasurableBase U hS).mapHeight V U.subtype ≤ 0 := by
    apply mapHeight_le_zero_of_completed_contraction
    intro ω z
    exact le_rfl
  simpa only [add_zero] using
    (V.restrictOfMeasurableBase U hS).generalHNOrderedSlope_le_of_injective_of_mapHeight_le
      hS hN V U.subtype U.subtype_injective 0 hh j

end AdelicVectorBundle

end

end ArakelovGeometry
