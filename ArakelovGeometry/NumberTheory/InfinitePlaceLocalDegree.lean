/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.ExternalResults.AbsoluteValueLocal
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Actual local degrees at infinite number-field places

The intrinsic degree of the actual completed scalar map is the number
of complex embeddings inducing the given place, hence its multiplicity.
-/

@[expose] public section

noncomputable section

namespace NumberField

/-- The usual complex norm has the canonical rational restriction. -/
theorem complexNormAbsoluteValue_restriction_rat :
    (NormedField.toAbsoluteValue ℂ).under ℚ = Rat.AbsoluteValue.real := by
  ext q
  change ‖(q : ℂ)‖ = Rat.AbsoluteValue.real q
  rw [Complex.norm_ratCast, Rat.AbsoluteValue.real_eq_abs, Rat.cast_abs]

namespace InfinitePlace

variable {K : Type*} [Field K] [NumberField K]

/-- Every usual infinite-place modulus restricts to the usual rational one. -/
theorem restriction_rat (w : InfinitePlace K) :
    w.val.under ℚ = Rat.AbsoluteValue.real := by
  ext q
  change w (q : K) = Rat.AbsoluteValue.real q
  rw [InfinitePlace.map_ratCast, Rat.AbsoluteValue.real_eq_abs,
    ← Rat.norm_cast_real, Real.norm_eq_abs, Rat.cast_abs]


/-- The intrinsic completed scalar degree equals the actual infinite multiplicity. -/
theorem localDegree_rat (w : InfinitePlace K) : w.val.localDegree ℚ = w.mult := by
  classical
  let u := NormedField.toAbsoluteValue ℂ
  have hu : u.under ℚ = w.val.under ℚ :=
    complexNormAbsoluteValue_restriction_rat.trans w.restriction_rat.symm
  have hcard := AbsoluteValue.card_embeddings_eq_localDegree_of_isAlgClosed w.val u hu
  let e : {σ : K →ₐ[ℚ] ℂ // u.comp σ.toRingHom.injective = w.val} ≃
      {σ : K →+* ℂ // InfinitePlace.mk σ = w} :=
    (RingHom.equivRatAlgHom K ℂ).symm.subtypeEquiv (fun σ => by
      change (place σ.toRingHom = w.val) ↔ (InfinitePlace.mk σ.toRingHom = w)
      constructor
      · exact fun h => Subtype.ext h
      · exact fun h => congrArg Subtype.val h)
  calc
    w.val.localDegree ℚ = Nat.card {σ : K →ₐ[ℚ] ℂ // u.comp σ.toRingHom.injective = w.val} :=
      hcard.symm
    _ = Nat.card {σ : K →+* ℂ // InfinitePlace.mk σ = w} := Nat.card_congr e
    _ = w.mult := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, card_filter_mk_eq]

/-- Actual local degree one at a real infinite place. -/
theorem IsReal.localDegree_rat_eq_one {w : InfinitePlace K} (hw : w.IsReal) :
    w.val.localDegree ℚ = 1 := by
  rw [localDegree_rat, hw.mult_eq_one]

/-- Actual local degree two at a complex infinite place. -/
theorem IsComplex.localDegree_rat_eq_two {w : InfinitePlace K} (hw : w.IsComplex) :
    w.val.localDegree ℚ = 2 := by
  rw [localDegree_rat, hw.mult_eq_two]

end InfinitePlace

end NumberField
