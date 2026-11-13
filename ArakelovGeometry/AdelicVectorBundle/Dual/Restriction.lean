/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Dual.Basic
public import ArakelovGeometry.AdelicVectorBundle.Subquotient.Quotient.Basic

import ArakelovGeometry.AdelicVectorBundle.Dual.Map
import ArakelovGeometry.Analysis.Dual.DualRestrictionInfimum
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Quotient norms on duals of completed restrictions

The actual completed pullback fibre identifies isometrically with the range
of its completed inclusion. The minimal-extension formula for functionals
then identifies its dual norm with the quotient of the original dual norm.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

/-- Precomposition with an isometric linear equivalence preserves the
algebraic operator seminorm, also over trivially valued complete fields. -/
theorem linearMapOperatorSeminorm_comp_linearIsometryEquiv
    {L V W : Type*} [NormedField L] [CompleteSpace L]
    [NormedAddCommGroup V] [NormedSpace L V] [FiniteDimensional L V]
    [NormedAddCommGroup W] [NormedSpace L W] [FiniteDimensional L W]
    (e : V ≃ₗᵢ[L] W) (f : W →ₗ[L] L) :
    linearMapOperatorSeminorm (f.comp e.toLinearMap) = linearMapOperatorSeminorm f := by
  apply le_antisymm
  · apply linearMapOperatorSeminorm_le _ (apply_nonneg _ f)
    intro x
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearIsometryEquiv.coe_toLinearEquiv, e.norm_map] using norm_linearMap_apply_le f (e x)
  · apply linearMapOperatorSeminorm_le _ (apply_nonneg _ (f.comp e.toLinearMap))
    intro y
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearIsometryEquiv.coe_toLinearEquiv, e.apply_symm_apply, e.symm.norm_map] using
      norm_linearMap_apply_le (f.comp e.toLinearMap) (e.symm y)

namespace NormFamily

universe u w w'

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  (ξ : NormFamily S E)

/-- The completed pulled-back fibre is the actual completed range with
its inherited norm, under the canonical injective scalar-extension map. -/
def completedPullbackRangeIsometry (f : F →ₗ[K] E) (hf : Function.Injective f)
    (ω : S.Ω) :
    let := ξ.fibreNormedAddCommGroup ω
    let := ξ.fibreNormedSpace ω
    let := (ξ.pullback f hf).fibreNormedAddCommGroup ω
    let := (ξ.pullback f hf).fibreNormedSpace ω
    (S.ϕ ω).Completion ⊗[K] F ≃ₗᵢ[(S.ϕ ω).Completion]
      LinearMap.range (f.baseChange (S.ϕ ω).Completion) := by
  have : Module.Free K (S.ϕ ω).Completion := Module.Free.of_divisionRing K _
  have : Module.Flat K (S.ϕ ω).Completion := Module.Flat.of_free
  intro aE nE aF nF
  let := aE
  let := nE
  let := aF
  let := nF
  exact
    { LinearEquiv.ofInjective (f.baseChange (S.ϕ ω).Completion)
        (Module.Flat.lTensor_preserves_injective_linearMap f hf) with
      norm_map' := fun _ => rfl }

/-- At a usual Archimedean completion, or for an ultrametric original fibre,
the dual of the actual restricted norm is the quotient of the actual dual norm. -/
theorem pullback_dual_norm_eq_of_isRCLike_or_ultrametric
    (f : F →ₗ[K] E) (hf : Function.Injective f) (ω : S.Ω)
    (hω : IsRCLikeNormedField (S.ϕ ω).Completion ∨
      ∀ x y, ξ.norm ω (x + y) ≤ max (ξ.norm ω x) (ξ.norm ω y))
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K F) :
    (ξ.pullback f hf).dual.norm ω z =
      (ξ.dual.pushforward f.dualMap (LinearMap.dualMap_surjective_of_injective hf)).norm ω z := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := (ξ.pullback f hf).fibreNormedAddCommGroup ω
  let := (ξ.pullback f hf).fibreNormedSpace ω
  let fC := f.baseChange (S.ϕ ω).Completion
  let P := LinearMap.range fC
  let e := ξ.completedPullbackRangeIsometry f hf ω
  let ℓ := dualBaseChangeEquiv K (S.ϕ ω).Completion F z
  let ℓP := ℓ.comp e.symm.toLinearMap
  have he (x : (S.ϕ ω).Completion ⊗[K] F) :
      (e x : (S.ϕ ω).Completion ⊗[K] E) = fC x := rfl
  have hn : linearMapOperatorSeminorm ℓP = linearMapOperatorSeminorm ℓ :=
    linearMapOperatorSeminorm_comp_linearIsometryEquiv e.symm ℓ
  have hc (g : (S.ϕ ω).Completion ⊗[K] E →ₗ[(S.ϕ ω).Completion] (S.ϕ ω).Completion) :
      g.comp P.subtype = ℓP ↔ g.comp fC = ℓ := by
    constructor
    · intro h
      apply LinearMap.ext
      intro x
      have hx := congrArg (fun q : P →ₗ[(S.ϕ ω).Completion] (S.ϕ ω).Completion => q (e x)) h
      simpa only [ℓP, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
        Submodule.subtype_apply, he] using hx
    · intro h
      apply LinearMap.ext
      intro y
      obtain ⟨x, rfl⟩ := e.surjective y
      simpa only [ℓP, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
        Submodule.subtype_apply, he] using
        congrArg (fun q : (S.ϕ ω).Completion ⊗[K] F →ₗ[(S.ϕ ω).Completion]
          (S.ϕ ω).Completion => q x) h
  have hs : (linearMapOperatorSeminorm ''
      {g : (S.ϕ ω).Completion ⊗[K] E →ₗ[(S.ϕ ω).Completion] (S.ϕ ω).Completion |
        g.comp P.subtype = ℓP}) =
      (ξ.dual.norm ω '' {t | f.dualMap.baseChange (S.ϕ ω).Completion t = z}) := by
    ext r
    constructor
    · rintro ⟨g, hg, hr⟩
      refine ⟨(dualBaseChangeEquiv K (S.ϕ ω).Completion E).symm g, ?_, ?_⟩
      · apply (dualBaseChangeEquiv K (S.ϕ ω).Completion F).injective
        rw [dualBaseChangeEquiv_dualMap, LinearEquiv.apply_symm_apply]
        exact (hc g).mp hg
      · change linearMapOperatorSeminorm
          (dualBaseChangeEquiv K (S.ϕ ω).Completion E
            ((dualBaseChangeEquiv K (S.ϕ ω).Completion E).symm g)) = r
        rw [LinearEquiv.apply_symm_apply]
        exact hr
    · rintro ⟨t, ht, rfl⟩
      refine ⟨dualBaseChangeEquiv K (S.ϕ ω).Completion E t, ?_, rfl⟩
      apply (hc _).mpr
      have h := congrArg (dualBaseChangeEquiv K (S.ϕ ω).Completion F) ht
      rw [dualBaseChangeEquiv_dualMap] at h
      exact h
  have hi : linearMapOperatorSeminorm ℓP =
      sInf (linearMapOperatorSeminorm ''
        {g : (S.ϕ ω).Completion ⊗[K] E →ₗ[(S.ϕ ω).Completion] (S.ϕ ω).Completion |
          g.comp P.subtype = ℓP}) := by
    rcases hω with hA | hU
    · let := hA
      let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
      exact linearMapOperatorSeminorm_eq_sInf_extensions_archimedean P ℓP
    · let : IsUltrametricDist ((S.ϕ ω).Completion ⊗[K] E) :=
        IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm hU
      exact linearMapOperatorSeminorm_eq_sInf_extensions_ultrametric P ℓP
  calc
    _ = linearMapOperatorSeminorm ℓ := rfl
    _ = linearMapOperatorSeminorm ℓP := hn.symm
    _ = sInf (linearMapOperatorSeminorm ''
        {g : (S.ϕ ω).Completion ⊗[K] E →ₗ[(S.ϕ ω).Completion] (S.ϕ ω).Completion |
          g.comp P.subtype = ℓP}) := hi
    _ = sInf (ξ.dual.norm ω '' {t | f.dualMap.baseChange (S.ϕ ω).Completion t = z}) :=
      congrArg sInf hs
    _ = _ := (ξ.dual.pushforward_norm_eq_sInf f.dualMap
      (LinearMap.dualMap_surjective_of_injective hf) ω z).symm

/-- Under the source local hypotheses, duality turns pullback into
pushforward along the transpose, as equality of actual norm families. -/
theorem pullback_dual [hξ : ξ.IsUltrametricAtFinitePlaces]
    [hS : S.IsArchimedeanNormalized]
    (f : F →ₗ[K] E) (hf : Function.Injective f) :
    (ξ.pullback f hf).dual =
      ξ.dual.pushforward f.dualMap (LinearMap.dualMap_surjective_of_injective hf) := by
  ext ω z
  apply ξ.pullback_dual_norm_eq_of_isRCLike_or_ultrametric f hf ω ?_ z
  by_cases hω : ω ∈ S.Ωfin
  · exact Or.inr (hξ ω hω)
  · exact Or.inl (hS ω hω)

/-- The actual dual of a subspace restriction has exactly the quotient norm
along the algebraic restriction of functionals. -/
theorem restrict_dual [hξ : ξ.IsUltrametricAtFinitePlaces]
    [hS : S.IsArchimedeanNormalized]
    (V : Submodule K E) :
    (ξ.restrict V).dual = ξ.dual.pushforward V.subtype.dualMap
      (LinearMap.dualMap_surjective_of_injective V.subtype_injective) :=
  ξ.pullback_dual V.subtype V.subtype_injective

/-- Pullback of quotient functionals identifies their actual completed norm
with the restricted dual norm on the canonical algebraic annihilator. -/
theorem quotient_dual_annihilator_norm_eq (V : Submodule K E) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K (E ⧸ V)) :
    (ξ.quotient V).dual.norm ω z =
      (ξ.dual.restrict V.dualAnnihilator).norm ω
        ((V.dualQuotEquivDualAnnihilator.baseChange K (S.ϕ ω).Completion) z) := by
  have h : V.dualAnnihilator.subtype.comp
      V.dualQuotEquivDualAnnihilator.toLinearMap = V.mkQ.dualMap := by
    apply LinearMap.ext
    intro ℓ
    apply LinearMap.ext
    intro x
    rfl
  rw [restrict_norm]
  change (ξ.quotient V).dual.norm ω z = ξ.dual.norm ω
    ((V.dualAnnihilator.subtype.baseChange (S.ϕ ω).Completion).comp
      (V.dualQuotEquivDualAnnihilator.toLinearMap.baseChange
        (S.ϕ ω).Completion) z)
  rw [← LinearMap.baseChange_comp, h]
  exact ξ.pushforward_dual_norm_eq V.mkQ V.mkQ_surjective ω z

/-- The canonical quotient-dual/annihilator equivalence preserves the actual
norm family at every place, without a local Hahn--Banach hypothesis. -/
theorem quotient_dual_annihilator (V : Submodule K E) :
    (ξ.quotient V).dual =
      (ξ.dual.restrict V.dualAnnihilator).pullback
        V.dualQuotEquivDualAnnihilator.toLinearMap
        V.dualQuotEquivDualAnnihilator.injective := by
  ext ω z
  exact ξ.quotient_dual_annihilator_norm_eq V ω z

/-- The canonical algebraic quotient-dual/annihilator equivalence becomes
an actual linear isometry of the completed normed fibres. -/
def completedQuotientDualAnnihilatorIsometry (V : Submodule K E) (ω : S.Ω) :
    let := (ξ.quotient V).dual.fibreNormedAddCommGroup ω
    let := (ξ.quotient V).dual.fibreNormedSpace ω
    let := (ξ.dual.restrict V.dualAnnihilator).fibreNormedAddCommGroup ω
    let := (ξ.dual.restrict V.dualAnnihilator).fibreNormedSpace ω
    (S.ϕ ω).Completion ⊗[K] Module.Dual K (E ⧸ V) ≃ₗᵢ[(S.ϕ ω).Completion]
      (S.ϕ ω).Completion ⊗[K] V.dualAnnihilator := by
  intro aQ nQ aA nA
  let := aQ
  let := nQ
  let := aA
  let := nA
  exact
    { V.dualQuotEquivDualAnnihilator.baseChange K (S.ϕ ω).Completion with
      norm_map' := fun z => (ξ.quotient_dual_annihilator_norm_eq V ω z).symm }

omit [FiniteDimensional K E] in
/-- The actual scalar extensions of the quotient transpose and inclusion
transpose form a short exact sequence, including either zero end. -/
theorem completed_dual_exact_sequence (V : Submodule K E) (ω : S.Ω) :
    Function.Injective (V.mkQ.dualMap.baseChange (S.ϕ ω).Completion) ∧
      Function.Exact (V.mkQ.dualMap.baseChange (S.ϕ ω).Completion)
        (V.subtype.dualMap.baseChange (S.ϕ ω).Completion) ∧
      Function.Surjective (V.subtype.dualMap.baseChange (S.ϕ ω).Completion) := by
  have h : Function.Exact V.mkQ.dualMap V.subtype.dualMap := by
    apply LinearMap.exact_iff.mpr
    rw [V.range_dualMap_mkQ_eq]
    exact V.dualRestrict_ker_eq_dualAnnihilator
  exact ⟨Module.Flat.lTensor_preserves_injective_linearMap _
      (LinearMap.dualMap_injective_of_surjective V.mkQ_surjective),
    Module.Flat.lTensor_exact (S.ϕ ω).Completion h,
    LinearMap.baseChange_surjective _
      (LinearMap.dualMap_surjective_of_injective V.subtype_injective)⟩

omit [FiniteDimensional K E] in
/-- The completed quotient-dual image is exactly the scalar extension of the
canonical annihilator, equivalently the kernel of completed restriction. -/
theorem completed_dual_annihilator_range (V : Submodule K E) (ω : S.Ω) :
    (V.mkQ.dualMap.baseChange (S.ϕ ω).Completion).range =
      (V.dualAnnihilator.subtype.baseChange (S.ϕ ω).Completion).range := by
  calc
    _ = (V.subtype.dualMap.baseChange (S.ϕ ω).Completion).ker :=
      (LinearMap.exact_iff.mp (completed_dual_exact_sequence (S := S) V ω).2.1).symm
    _ = _ := baseChange_ker V.subtype.dualMap ω

/-- Duality gives the actual completed short exact sequence its induced
restriction and quotient norms under the source local hypotheses. No rank
positivity is required for the ambient space or either end. -/
theorem dual_normed_exact_sequence [hξ : ξ.IsUltrametricAtFinitePlaces]
    [hS : S.IsArchimedeanNormalized]
    (V : Submodule K E) :
    (∀ ω : S.Ω,
      Function.Injective (V.mkQ.dualMap.baseChange (S.ϕ ω).Completion) ∧
        Function.Exact (V.mkQ.dualMap.baseChange (S.ϕ ω).Completion)
          (V.subtype.dualMap.baseChange (S.ϕ ω).Completion) ∧
        Function.Surjective (V.subtype.dualMap.baseChange (S.ϕ ω).Completion)) ∧
      (ξ.quotient V).dual = ξ.dual.pullback V.mkQ.dualMap
        (LinearMap.dualMap_injective_of_surjective V.mkQ_surjective) ∧
      (ξ.restrict V).dual = ξ.dual.pushforward V.subtype.dualMap
        (LinearMap.dualMap_surjective_of_injective V.subtype_injective) := by
  exact ⟨completed_dual_exact_sequence V,
    ξ.pushforward_dual V.mkQ V.mkQ_surjective, ξ.restrict_dual V⟩

/-- The canonical quotient of the dual by the annihilator has the actual
restricted-space dual norm, under the local extension hypothesis. -/
theorem dual_quotient_annihilator_norm_eq_of_isRCLike_or_ultrametric
    (V : Submodule K E) (ω : S.Ω)
    (hω : IsRCLikeNormedField (S.ϕ ω).Completion ∨
      ∀ x y, ξ.norm ω (x + y) ≤ max (ξ.norm ω x) (ξ.norm ω y))
    (z : (S.ϕ ω).Completion ⊗[K] (Module.Dual K E ⧸ V.dualAnnihilator)) :
    (ξ.dual.quotient V.dualAnnihilator).norm ω z =
      (ξ.restrict V).dual.norm ω
        (((Subspace.quotAnnihilatorEquiv V).baseChange K (S.ϕ ω).Completion) z) := by
  let e := (Subspace.quotAnnihilatorEquiv V).baseChange K (S.ϕ ω).Completion
  have h : (Subspace.quotAnnihilatorEquiv V).toLinearMap.comp V.dualAnnihilator.mkQ =
      V.subtype.dualMap := by
    apply LinearMap.ext
    intro ℓ
    exact Subspace.quotAnnihilatorEquiv_apply V ℓ
  have he (t : (S.ϕ ω).Completion ⊗[K] Module.Dual K E) :
      e (V.dualAnnihilator.mkQ.baseChange (S.ϕ ω).Completion t) =
        V.subtype.dualMap.baseChange (S.ϕ ω).Completion t := by
    change (((Subspace.quotAnnihilatorEquiv V).toLinearMap.baseChange
      (S.ϕ ω).Completion).comp
      (V.dualAnnihilator.mkQ.baseChange (S.ϕ ω).Completion)) t = _
    rw [← LinearMap.baseChange_comp, h]
  have hs : {t | V.dualAnnihilator.mkQ.baseChange (S.ϕ ω).Completion t = z} =
      {t | V.subtype.dualMap.baseChange (S.ϕ ω).Completion t = e z} := by
    ext t
    constructor
    · intro ht
      exact (he t).symm.trans (congrArg e ht)
    · intro ht
      exact e.injective ((he t).trans ht)
  calc
    _ = sInf (ξ.dual.norm ω ''
        {t | V.dualAnnihilator.mkQ.baseChange (S.ϕ ω).Completion t = z}) :=
      ξ.dual.pushforward_norm_eq_sInf V.dualAnnihilator.mkQ
        V.dualAnnihilator.mkQ_surjective ω z
    _ = sInf (ξ.dual.norm ω ''
        {t | V.subtype.dualMap.baseChange (S.ϕ ω).Completion t = e z}) :=
      congrArg (fun T => sInf (ξ.dual.norm ω '' T)) hs
    _ = (ξ.dual.pushforward V.subtype.dualMap
        (LinearMap.dualMap_surjective_of_injective V.subtype_injective)).norm ω (e z) :=
      (ξ.dual.pushforward_norm_eq_sInf V.subtype.dualMap
        (LinearMap.dualMap_surjective_of_injective V.subtype_injective) ω (e z)).symm
    _ = _ := (ξ.pullback_dual_norm_eq_of_isRCLike_or_ultrametric V.subtype
      V.subtype_injective ω hω (e z)).symm

/-- The canonical quotient-by-annihilator norm identity at every adelic
place under the source ultrametric and usual-Archimedean hypotheses. -/
theorem dual_quotient_annihilator_norm_eq [hξ : ξ.IsUltrametricAtFinitePlaces]
    [hS : S.IsArchimedeanNormalized]
    (V : Submodule K E) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (Module.Dual K E ⧸ V.dualAnnihilator)) :
    (ξ.dual.quotient V.dualAnnihilator).norm ω z =
      (ξ.restrict V).dual.norm ω
        (((Subspace.quotAnnihilatorEquiv V).baseChange K (S.ϕ ω).Completion) z) := by
  apply ξ.dual_quotient_annihilator_norm_eq_of_isRCLike_or_ultrametric V ω ?_ z
  by_cases hω : ω ∈ S.Ωfin
  · exact Or.inr (hξ ω hω)
  · exact Or.inl (hS ω hω)

/-- The canonical algebraic quotient-by-annihilator equivalence identifies
the actual quotient dual family with the actual restricted-space dual family. -/
theorem dual_quotient_annihilator [hξ : ξ.IsUltrametricAtFinitePlaces]
    [hS : S.IsArchimedeanNormalized]
    (V : Submodule K E) :
    ξ.dual.quotient V.dualAnnihilator =
      (ξ.restrict V).dual.pullback (Subspace.quotAnnihilatorEquiv V).toLinearMap
        (Subspace.quotAnnihilatorEquiv V).injective := by
  ext ω z
  exact ξ.dual_quotient_annihilator_norm_eq V ω z

/-- The canonical quotient-by-annihilator equivalence is an actual completed
linear isometry under the local extension hypothesis, including zero ends. -/
def completedDualQuotientRestrictionIsometry (V : Submodule K E) (ω : S.Ω)
    (hω : IsRCLikeNormedField (S.ϕ ω).Completion ∨
      ∀ x y, ξ.norm ω (x + y) ≤ max (ξ.norm ω x) (ξ.norm ω y)) :
    let := (ξ.dual.quotient V.dualAnnihilator).fibreNormedAddCommGroup ω
    let := (ξ.dual.quotient V.dualAnnihilator).fibreNormedSpace ω
    let := (ξ.restrict V).dual.fibreNormedAddCommGroup ω
    let := (ξ.restrict V).dual.fibreNormedSpace ω
    (S.ϕ ω).Completion ⊗[K] (Module.Dual K E ⧸ V.dualAnnihilator)
      ≃ₗᵢ[(S.ϕ ω).Completion] (S.ϕ ω).Completion ⊗[K] Module.Dual K V := by
  intro aQ nQ aR nR
  let := aQ
  let := nQ
  let := aR
  let := nR
  exact
    { (Subspace.quotAnnihilatorEquiv V).baseChange K (S.ϕ ω).Completion with
      norm_map' := fun z =>
        (ξ.dual_quotient_annihilator_norm_eq_of_isRCLike_or_ultrametric V ω hω z).symm }

end NormFamily

end ArakelovGeometry
