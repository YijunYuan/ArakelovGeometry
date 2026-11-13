/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Ordered
public import ArakelovGeometry.AdelicVectorBundle.Operator.Height
public import ArakelovGeometry.AdelicVectorBundle.Slope.Subquotient

import ArakelovGeometry.AdelicVectorBundle.Degree.Supermodular
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Functoriality
import ArakelovGeometry.AdelicVectorBundle.Slope.Finite
import ArakelovGeometry.AdelicVectorBundle.Subquotient.Restriction.Functor
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Actual slopes and intrinsic filtrations of general filtration terms

An ordered jump is the actual minimum slope of its filtration term.
Canonical completed restriction norms identify the intrinsic filtration
of that term with the ambient filtration above its level.
-/

@[expose] public section

namespace ArakelovGeometry

noncomputable section

universe u w w'

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace AdelicVectorBundle

variable [S.IsProper] (V : AdelicVectorBundle S)
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]

/-- The term at an actual ordered jump has that jump as its actual minimum.
The rank cut proves positive rank before the true minimum is lifted to a real. -/
theorem minimalSlope_restrict_hnFiltration_orderedSlope
    (j : Fin (Module.finrank K V)) :
    (V.restrictOfNormMeasurability
      (V.hnFiltration (V.hnSlope j))).minimalSlope
        = (V.hnSlope j : EReal) := by
  let μ := V.hnSlope j
  let U := V.hnFiltration μ
  have hj : j.val < Module.finrank K U :=
    V.lt_finrank_hnFiltration_orderedSlope j
  have hpos : 0 < Module.finrank K U := (Nat.zero_le j.val).trans_lt hj
  obtain ⟨c, hc⟩ := (V.restrictOfNormMeasurability U).exists_minimalSlope_eq_coe hpos
  have hlo : (μ : EReal) ≤ (V.restrictOfNormMeasurability U).minimalSlope :=
    V.le_minimalSlope_restrict_hnFiltration μ
  have hle : U ≤ V.hnFiltration c :=
    V.le_hnFiltration_of_le_minimalSlope_restrict U c hc.ge
  have hcμ : c ≤ μ :=
    (V.le_hnSlope_iff_lt_filtration_finrank c j).mpr
      (hj.trans_le (Submodule.finrank_mono hle))
  change (V.restrictOfNormMeasurability U).minimalSlope = (μ : EReal)
  rw [hc] at hlo ⊢
  exact le_antisymm (EReal.coe_le_coe hcμ) hlo


/-- The actual canonical inclusion contracts every completed vector, so
the intrinsic filtration of any restriction maps into the ambient one. -/
theorem map_hnFiltration_restrict_le (U : Submodule K V) (s : ℝ) :
    ((V.restrictOfNormMeasurability U).hnFiltration s).map U.subtype ≤
      V.hnFiltration s := by
  by_cases hf : U.subtype = 0
  · simp only [hf, Submodule.map_zero]
    exact bot_le
  · have hh : (V.restrictOfNormMeasurability U).mapHeight V U.subtype ≤ 0 := by
      apply mapHeight_le_zero_of_completed_contraction
      intro ω z
      exact le_rfl
    simpa only [sub_zero] using
      (V.restrictOfNormMeasurability U).map_hnFiltration_le_of_mapHeight_le
        V U.subtype hf 0 hh s

/-- The intrinsic actual filtration of an ambient term is its whole
space below that term's level, including a zero ambient term. -/
theorem hnFiltration_restrict_term_eq_top (t s : ℝ) (hst : s ≤ t) :
    (V.restrictOfNormMeasurability (V.hnFiltration t)).hnFiltration
      s = ⊤ := by
  apply hnFiltration_eq_top_of_le_minimalSlope
  exact (EReal.coe_le_coe hst).trans
    (V.le_minimalSlope_restrict_hnFiltration t)

/-- Above an ambient term's level, its intrinsic actual filtration is
exactly the ambient one under the canonical subtype map. -/
theorem map_hnFiltration_restrict_term_eq (t s : ℝ) (hts : t ≤ s) :
    ((V.restrictOfNormMeasurability (V.hnFiltration t)).hnFiltration
      s).map (V.hnFiltration t).subtype =
        V.hnFiltration s := by
  apply le_antisymm (V.map_hnFiltration_restrict_le _ s)
  let U := V.hnFiltration t
  let B := V.hnFiltration s
  have hBU : B ≤ U := V.antitone_hnFiltration hts
  have hmin : (s : EReal) ≤
      ((V.restrictOfNormMeasurability U).restrictOfNormMeasurability
        (B.comap U.subtype)).minimalSlope := by
    rw [V.minimalSlope_restrict_restrict B U hBU]
    exact V.le_minimalSlope_restrict_hnFiltration s
  have hle := le_hnFiltration_of_le_minimalSlope_restrict
    (V.restrictOfNormMeasurability U) (B.comap U.subtype) s hmin
  have hmap := Submodule.map_mono hle (f := U.subtype)
  rw [Submodule.map_comap_subtype, inf_eq_right.mpr hBU] at hmap
  exact hmap

variable {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- A genuine injection with any real upper bound on its actual height
compares the corresponding actual ordered slots. Injectivity and an
attained nonzero source slot prove that the map is nonzero. -/
theorem hnSlope_le_of_injective_of_mapHeight_le
    (W : AdelicVectorBundle S) (f : V →ₗ[K] W) (hi : Function.Injective f)
    (c : ℝ) (hh : V.mapHeight W f ≤ (c : EReal)) (j : Fin (Module.finrank K V)) :
    V.hnSlope j ≤
      W.hnSlope
        (j.castLE (LinearMap.finrank_le_finrank_of_injective hi)) + c := by
  let μ := V.hnSlope j
  let U := V.hnFiltration μ
  have hj : j.val < Module.finrank K U :=
    V.lt_finrank_hnFiltration_orderedSlope j
  have hm : Module.finrank K U ≤ Module.finrank K (U.map f) :=
    LinearMap.finrank_le_finrank_of_injective (f.submoduleMap_injective hi U)
  have hf : f ≠ 0 := by
    intro hz
    have hp := hj.trans_le hm
    rw [hz, Submodule.map_zero, finrank_bot] at hp
    exact Nat.not_lt_zero j.val hp
  have hle := V.map_hnFiltration_le_of_mapHeight_le W f hf c hh μ
  have hr := hj.trans_le (hm.trans (Submodule.finrank_mono hle))
  have hs := (W.le_hnSlope_iff_lt_filtration_finrank (μ - c)
    (j.castLE (LinearMap.finrank_le_finrank_of_injective hi))).mpr hr
  exact sub_le_iff_le_add.mp hs

/-- Source finite-height injection comparison using the actual extended
height. Its negative-infinite endpoint is excluded by the genuine nonzero
map before lifting the height to a real number. -/
theorem hnSlope_le_of_injective
    (W : AdelicVectorBundle S) (f : V →ₗ[K] W) (hi : Function.Injective f)
    (hh : V.mapHeight W f ≠ ⊤) (j : Fin (Module.finrank K V)) :
    (V.hnSlope j : EReal) ≤
      (W.hnSlope
        (j.castLE (LinearMap.finrank_le_finrank_of_injective hi)) : EReal) +
          V.mapHeight W f := by
  have hf : f ≠ 0 := by
    intro hz
    have hm : Module.finrank K (⊤ : Submodule K V) ≤
        Module.finrank K ((⊤ : Submodule K V).map f) :=
      LinearMap.finrank_le_finrank_of_injective (f.submoduleMap_injective hi ⊤)
    rw [hz, Submodule.map_zero, finrank_bot, finrank_top] at hm
    exact (Nat.not_lt_zero j.val) (j.isLt.trans_le hm)
  have hb : V.mapHeight W f ≠ ⊥ := (V.bot_lt_mapHeight W hf).ne'
  obtain ⟨c, hc⟩ : ∃ c : ℝ, V.mapHeight W f = (c : EReal) := by
    lift V.mapHeight W f to ℝ using ⟨hh, hb⟩ with c
    exact ⟨c, rfl⟩
  rw [hc, ← EReal.coe_add]
  exact EReal.coe_le_coe
    (V.hnSlope_le_of_injective_of_mapHeight_le W f hi c hc.le j)

/-- Every actual restricted bundle has each ordered slope at most the
same ambient slot. The completed canonical inclusion gives height at
most zero, with no height or Hermitianity hypothesis supplied. -/
theorem hnSlope_restrict_le (U : Submodule K V)
    (j : Fin (Module.finrank K U)) :
    (V.restrictOfNormMeasurability U).hnSlope j ≤
      V.hnSlope (j.castLE U.finrank_le) := by
  have hh : (V.restrictOfNormMeasurability U).mapHeight V U.subtype ≤ 0 := by
    apply mapHeight_le_zero_of_completed_contraction
    intro ω z
    exact le_rfl
  simpa only [add_zero] using
    (V.restrictOfNormMeasurability U).hnSlope_le_of_injective_of_mapHeight_le
      V U.subtype U.subtype_injective 0 hh j

end AdelicVectorBundle

end

end ArakelovGeometry
