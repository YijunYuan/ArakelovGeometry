/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DegreeSupermodular
public import ArakelovGeometry.AdelicVectorBundle.SlopesQuotient

/-!
# Actual quotient and restriction norms

The canonical quotient by the kernel is compared with the actual image
restriction. When the original subspace contains the kernel, every ambient
lift stays in the completed subspace and the comparison is an equality.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

noncomputable section

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

omit [FiniteDimensional K F] in
/-- The canonical first-isomorphism map identifies the actual kernel quotient
with pushforward to the actual range, on all completed vectors. -/
theorem quotKerEquivRange_norm_eq (ξ : NormFamily S E) (f : E →ₗ[K] F)
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] (E ⧸ f.ker)) :
    (ξ.quotient f.ker).norm ω z =
      (ξ.pushforward f.rangeRestrict f.surjective_rangeRestrict).norm ω
        (f.quotKerEquivRange.toLinearMap.baseChange (S.ϕ ω).Completion z) := by
  let e := f.quotKerEquivRange
  have hc : e.toLinearMap.comp f.ker.mkQ = f.rangeRestrict := by
    ext x
    rfl
  have h := ξ.pushforward_comp_norm f.ker.mkQ f.ker.mkQ_surjective
    e.toLinearMap e.surjective ω (e.toLinearMap.baseChange (S.ϕ ω).Completion z)
  simp only [hc] at h
  exact ((ξ.quotient f.ker).pushforward_norm_of_injective e.toLinearMap
    e.surjective e.injective ω z).symm.trans h

omit [FiniteDimensional K F] in
/-- A completed contraction descends through its actual kernel quotient
to the actual restricted range, including zero source or target. -/
theorem quotKerEquivRange_norm_le (ξ : NormFamily S E) (η : NormFamily S F)
    (f : E →ₗ[K] F)
    (hf : ∀ ω x, η.norm ω (f.baseChange (S.ϕ ω).Completion x) ≤ ξ.norm ω x)
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] (E ⧸ f.ker)) :
    (η.restrict f.range).norm ω
        (f.quotKerEquivRange.toLinearMap.baseChange (S.ϕ ω).Completion z) ≤
      (ξ.quotient f.ker).norm ω z := by
  have hc : f.range.subtype.comp
      (f.quotKerEquivRange.toLinearMap.comp f.ker.mkQ) = f := by
    ext x
    rfl
  apply (ξ.le_quotientSeminorm_iff f.ker.mkQ f.ker.mkQ_surjective ω z _).mpr
  intro x hx
  have he := DFunLike.congr_fun
    (congrArg (fun g ↦ g.baseChange (S.ϕ ω).Completion) hc) x
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at he
  simp only [restrict_norm]
  rw [← hx, he]
  exact hf ω x

/-- A restriction's quotient by its intersection with `W` contracts into
its actual image in the ambient quotient by `W`. -/
theorem quotient_restrict_range_norm_le (ξ : NormFamily S E) (U W : Submodule K E)
    (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (U ⧸ (W.mkQ.comp U.subtype).ker)) :
    ((ξ.quotient W).restrict (W.mkQ.comp U.subtype).range).norm ω
        ((W.mkQ.comp U.subtype).quotKerEquivRange.toLinearMap.baseChange
          (S.ϕ ω).Completion z) ≤
      ((ξ.restrict U).quotient (W.mkQ.comp U.subtype).ker).norm ω z := by
  apply quotKerEquivRange_norm_le
  intro ω x
  simpa only [LinearMap.baseChange_comp, LinearMap.comp_apply, restrict_norm] using
    ξ.quotient_norm_mk_le W ω (U.subtype.baseChange (S.ϕ ω).Completion x)

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- If a rational subspace contains the kernel, every completed lift of its
quotient image belongs to the completed subspace. No norm-minimizing lift is used. -/
theorem exists_completed_restrict_lift_of_ker_le (π : E →ₗ[K] F)
    (U : Submodule K E) (hU : π.ker ≤ U) (ω : S.Ω)
    (y : (S.ϕ ω).Completion ⊗[K] (π.comp U.subtype).range)
    (x : (S.ϕ ω).Completion ⊗[K] E)
    (hx : π.baseChange (S.ϕ ω).Completion x =
      (π.comp U.subtype).range.subtype.baseChange (S.ϕ ω).Completion y) :
    ∃ u, U.subtype.baseChange (S.ϕ ω).Completion u = x ∧
      (π.comp U.subtype).rangeRestrict.baseChange (S.ϕ ω).Completion u = y := by
  let g : U →ₗ[K] F := π.comp U.subtype
  let L := (S.ϕ ω).Completion
  obtain ⟨u₀, hu₀⟩ := LinearMap.baseChange_surjective L g.surjective_rangeRestrict y
  have hc : g.range.subtype.comp g.rangeRestrict = π.comp U.subtype := by
    ext u
    rfl
  have hπu : π.baseChange L (U.subtype.baseChange L u₀) =
      g.range.subtype.baseChange L y := by
    have ht := DFunLike.congr_fun (congrArg (fun f ↦ f.baseChange L) hc) u₀
    simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at ht
    exact ht.symm.trans (congrArg (g.range.subtype.baseChange L) hu₀)
  have hk : x - U.subtype.baseChange L u₀ ∈ (π.baseChange L).ker := by
    change π.baseChange L (x - U.subtype.baseChange L u₀) = 0
    rw [map_sub, hx, hπu, sub_self]
  rw [baseChange_ker π ω] at hk
  obtain ⟨w, hw⟩ := hk
  let i : π.ker →ₗ[K] U := Submodule.inclusion hU
  have hi : U.subtype.comp i = π.ker.subtype := by
    ext w
    rfl
  let u : L ⊗[K] U := u₀ + i.baseChange L w
  have hu : U.subtype.baseChange L u = x := by
    have ht := DFunLike.congr_fun (congrArg (fun f ↦ f.baseChange L) hi) w
    simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at ht
    dsimp only [u]
    rw [map_add, ht, hw]
    abel
  refine ⟨u, hu, ?_⟩
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := L) g.range.subtype
    g.range.subtype_injective
  have ht := DFunLike.congr_fun (congrArg (fun f ↦ f.baseChange L) hc) u
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at ht
  exact ht.trans (by rw [hu]; exact hx)

omit [FiniteDimensional K F] in
/-- Restriction followed by pushforward to its actual image is the restriction
of the ambient pushforward if the subspace contains the rational kernel. -/
theorem pushforward_restrict_range_norm_eq (ξ : NormFamily S E)
    (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (U : Submodule K E) (hU : π.ker ≤ U) (ω : S.Ω)
    (y : (S.ϕ ω).Completion ⊗[K] (π.comp U.subtype).range) :
    ((ξ.restrict U).pushforward (π.comp U.subtype).rangeRestrict
      (π.comp U.subtype).surjective_rangeRestrict).norm ω y =
      ((ξ.pushforward π hπ).restrict (π.comp U.subtype).range).norm ω y := by
  let g : U →ₗ[K] F := π.comp U.subtype
  let L := (S.ϕ ω).Completion
  have hc : g.range.subtype.comp g.rangeRestrict = π.comp U.subtype := by
    ext u
    rfl
  apply le_antisymm
  · apply (ξ.le_quotientSeminorm_iff π hπ ω
      (g.range.subtype.baseChange L y) _).mpr
    intro x hx
    obtain ⟨u, hu, hgu⟩ := exists_completed_restrict_lift_of_ker_le π U hU ω y x hx
    have hb := (ξ.restrict U).pushforward_norm_le g.rangeRestrict
      g.surjective_rangeRestrict ω u
    change g.rangeRestrict.baseChange L u = y at hgu
    rw [hgu] at hb
    simpa only [restrict_norm, hu] using hb
  · apply ((ξ.restrict U).le_quotientSeminorm_iff g.rangeRestrict
      g.surjective_rangeRestrict ω y _).mpr
    intro u hu
    have ht := DFunLike.congr_fun (congrArg (fun f ↦ f.baseChange L) hc) u
    simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at ht
    change (ξ.pushforward π hπ).norm ω (g.range.subtype.baseChange L y) ≤
      ξ.norm ω (U.subtype.baseChange L u)
    rw [← hu, ht]
    exact ξ.pushforward_norm_le π hπ ω _

/-- If `W ≤ U`, the canonical quotient-restriction map is an actual
completed isometry, including zero factors. -/
theorem quotient_restrict_range_norm_eq (ξ : NormFamily S E) (U W : Submodule K E)
    (hWU : W ≤ U) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (U ⧸ (W.mkQ.comp U.subtype).ker)) :
    ((ξ.restrict U).quotient (W.mkQ.comp U.subtype).ker).norm ω z =
      ((ξ.quotient W).restrict (W.mkQ.comp U.subtype).range).norm ω
        ((W.mkQ.comp U.subtype).quotKerEquivRange.toLinearMap.baseChange
          (S.ϕ ω).Completion z) := by
  rw [(ξ.restrict U).quotKerEquivRange_norm_eq]
  exact ξ.pushforward_restrict_range_norm_eq W.mkQ W.mkQ_surjective U
    (by simpa only [Submodule.ker_mkQ] using hWU) ω _

end

end ArakelovGeometry.NormFamily
