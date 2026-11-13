/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Slope.Extension
public import ArakelovGeometry.AdelicVectorBundle.Subquotient.Quotient.Restriction

import ArakelovGeometry.AdelicVectorBundle.Degree.Supermodular
import ArakelovGeometry.AdelicVectorBundle.Slope.Quotient
import ArakelovGeometry.AdelicVectorBundle.Subquotient.Restriction.Functor

/-!
# Slopes of canonical subquotients

Completed isometries identify slopes under nested restrictions and quotient maps.
These lemmas use no Harder–Narasimhan construction.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S)
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]

/-- The actual top restriction has the original minimum, including rank zero. -/
theorem minimalSlope_restrict_top :
    (V.restrictOfMeasurableBase ⊤).minimalSlope = V.minimalSlope := by
  apply minimalSlope_eq_of_completed_isometry _ _ Submodule.topEquiv
  intro ω z
  rfl

/-- Canonical nested restrictions have identical actual minimal slopes.
The comparison is the completed norm identity for the canonical subtype equivalence. -/
theorem minimalSlope_restrict_restrict (U W : Submodule K V) (hUW : U ≤ W) :
    ((V.restrictOfMeasurableBase W).restrictOfMeasurableBase
      (U.comap W.subtype)).minimalSlope =
      (V.restrictOfMeasurableBase U).minimalSlope := by
  apply minimalSlope_eq_of_completed_isometry _ _ (Submodule.comapSubtypeEquivOfLe hUW)
  intro ω z
  exact (V.toNormFamily.restrict_restrict_norm_eq U W hUW ω z).symm

/-- An actual completed quotient isometry transports the genuine minimum. -/
theorem minimalSlope_quotient_restrict_range_eq (U A : Submodule K V) (hA : A ≤ U) :
    ((V.restrictOfMeasurableBase U).quotientOfMeasurableBase
      (A.mkQ.comp U.subtype).ker).minimalSlope =
    ((V.quotientOfMeasurableBase A).restrictOfMeasurableBase
      (A.mkQ.comp U.subtype).range).minimalSlope := by
  apply minimalSlope_eq_of_completed_isometry _ _ (A.mkQ.comp U.subtype).quotKerEquivRange
  intro ω z
  exact (V.toNormFamily.quotient_restrict_range_norm_eq U A hA ω z).symm

/-- The actual extension minimum bound on the genuine preimage of a quotient subspace. -/
theorem min_minimalSlope_restrict_le_minimalSlope_preimage
    (A : Submodule K V) (G : Submodule K (V ⧸ A)) :
    min ((V.restrictOfMeasurableBase A).minimalSlope)
      (((V.quotientOfMeasurableBase A).restrictOfMeasurableBase G).minimalSlope) ≤
    (V.restrictOfMeasurableBase (G.comap A.mkQ)).minimalSlope := by
  let U := G.comap A.mkQ
  have hAU : A ≤ U := A.le_comap_mkQ G
  let P := V.restrictOfMeasurableBase A
  let W := V.restrictOfMeasurableBase U
  let f : A →ₗ[K] U := Submodule.inclusion hAU
  have hh : P.mapHeight W f ≤ 0 := by
    apply P.mapHeight_le_zero_of_completed_contraction W f
    intro ω z
    have hc : U.subtype.comp f = A.subtype := Submodule.subtype_comp_inclusion _ _ _
    have ht := DFunLike.congr_fun
      (congrArg (fun g ↦ g.baseChange (S.ϕ ω).Completion) hc) z
    simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at ht
    change V.norm ω (U.subtype.baseChange (S.ϕ ω).Completion
      (f.baseChange (S.ϕ ω).Completion z)) ≤
      V.norm ω (A.subtype.baseChange (S.ϕ ω).Completion z)
    rw [ht]
  have hExt := P.minimalSlope_extension_lowerBound W f
  have hMin : P.minimalSlope ≤ P.minimalSlope - P.mapHeight W f := by
    simpa only [sub_zero] using EReal.sub_le_sub (le_refl (P.minimalSlope)) hh
  have hRange : (A.mkQ.comp U.subtype).range = G := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    exact Submodule.map_comap_eq_of_surjective A.mkQ_surjective G
  have hq := V.minimalSlope_quotient_restrict_range_eq U A hAU
  rw [LinearMap.ker_comp, Submodule.ker_mkQ] at hq
  have hQr := congrArg
    (fun J : Submodule K (V ⧸ A) ↦
      ((V.quotientOfMeasurableBase A).restrictOfMeasurableBase J).minimalSlope)
    hRange
  have hfR : f.range = A.comap U.subtype := Submodule.range_inclusion A U hAU
  have hQf := congrArg
    (fun J : Submodule K U ↦ (W.quotientOfMeasurableBase J).minimalSlope) hfR
  rw [hQf.trans (hq.trans hQr)] at hExt
  exact (min_le_min hMin le_rfl).trans hExt

/-- A subspace of a subspace has the same true minimum on its actual ambient image. -/
theorem minimalSlope_restrict_map_subtype (B : Submodule K V) (G : Submodule K B) :
    ((V.restrictOfMeasurableBase B).restrictOfMeasurableBase G).minimalSlope =
      (V.restrictOfMeasurableBase (G.map B.subtype)).minimalSlope := by
  have h := V.minimalSlope_restrict_restrict (G.map B.subtype) B
    (Submodule.map_subtype_le B G)
  rw [Submodule.comap_map_eq_of_injective B.subtype_injective G] at h
  exact h

omit [S.IsProper] [FiniteDimensional K E] in
/-- The canonical quotient map on a nested restriction has exactly the
pulled-back lower-subspace kernel. -/
theorem nested_restrict_quotient_map_ker (A B C : Submodule K E) (hBC : B ≤ C) :
    ((A.comap B.subtype).mkQ.comp
      (Submodule.comapSubtypeEquivOfLe hBC).toLinearMap).ker =
        (A.comap C.subtype).comap (B.comap C.subtype).subtype := by
  ext x
  change (A.comap B.subtype).mkQ ((Submodule.comapSubtypeEquivOfLe hBC) x) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

omit [S.IsProper] in
omit hS hN in
/-- Taking a factor after restricting through an intermediate subspace
preserves the actual completed norm under the canonical quotient equivalence. -/
theorem nested_restrict_quotient_norm_eq (ξ : NormFamily S E)
    (A B C : Submodule K E) (hBC : B ≤ C) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      ((B.comap C.subtype) ⧸
        ((A.comap B.subtype).mkQ.comp
          (Submodule.comapSubtypeEquivOfLe hBC).toLinearMap).ker)) :
    let e := Submodule.comapSubtypeEquivOfLe hBC
    let π := (A.comap B.subtype).mkQ.comp e.toLinearMap
    let hπ := (A.comap B.subtype).mkQ_surjective.comp e.surjective
    ((ξ.restrict B).quotient (A.comap B.subtype)).norm ω
      ((π.quotKerEquivOfSurjective hπ).toLinearMap.baseChange (S.ϕ ω).Completion z) =
        (((ξ.restrict C).restrict (B.comap C.subtype)).quotient π.ker).norm ω z := by
  let e := Submodule.comapSubtypeEquivOfLe hBC
  let T := A.comap B.subtype
  let π := T.mkQ.comp e.toLinearMap
  let hπ := T.mkQ_surjective.comp e.surjective
  let η := (ξ.restrict C).restrict (B.comap C.subtype)
  have hp : η.pushforward e.toLinearMap e.surjective = ξ.restrict B := by
    ext ω y
    obtain ⟨x, rfl⟩ := LinearMap.baseChange_surjective (S.ϕ ω).Completion e.surjective y
    rw [η.pushforward_norm_of_injective e.toLinearMap e.surjective e.injective]
    exact ξ.restrict_restrict_norm_eq B C hBC ω x
  change ((ξ.restrict B).quotient T).norm ω
    ((π.quotKerEquivOfSurjective hπ).toLinearMap.baseChange (S.ϕ ω).Completion z) =
      (η.quotient π.ker).norm ω z
  rw [← hp]
  change ((η.pushforward e.toLinearMap e.surjective).pushforward T.mkQ T.mkQ_surjective).norm ω
    ((π.quotKerEquivOfSurjective hπ).toLinearMap.baseChange (S.ϕ ω).Completion z) = _
  rw [η.pushforward_comp_norm]
  exact η.quotient_ker_equiv_norm_eq π hπ ω z

/-- Restricting an actual subquotient to an intermediate subspace gives
that intermediate subquotient with its actual completed norms. -/
theorem minimalSlope_subquotient_restrict_range (A U B : Submodule K V)
    (hAU : A ≤ U) (hUB : U ≤ B) :
    let T := A.comap B.subtype
    let R := U.comap B.subtype
    (((V.restrictOfMeasurableBase B).quotientOfMeasurableBase T).restrictOfMeasurableBase
      (T.mkQ.comp R.subtype).range).minimalSlope =
        ((V.restrictOfMeasurableBase U).quotientOfMeasurableBase
          (A.comap U.subtype)).minimalSlope := by
  let T := A.comap B.subtype
  let R := U.comap B.subtype
  have hTR : T ≤ R := Submodule.comap_mono hAU
  have hq := (V.restrictOfMeasurableBase B).minimalSlope_quotient_restrict_range_eq
    R T hTR
  rw [LinearMap.ker_comp, Submodule.ker_mkQ] at hq
  change _ = _
  rw [← hq]
  rw [← nested_restrict_quotient_map_ker A U B hUB]
  let e := Submodule.comapSubtypeEquivOfLe hUB
  let π := (A.comap U.subtype).mkQ.comp e.toLinearMap
  let hπ := (A.comap U.subtype).mkQ_surjective.comp e.surjective
  apply minimalSlope_eq_of_completed_isometry _ _ (π.quotKerEquivOfSurjective hπ)
  intro ω z
  exact nested_restrict_quotient_norm_eq V.toNormFamily A U B hUB ω z

end

end ArakelovGeometry.AdelicVectorBundle
