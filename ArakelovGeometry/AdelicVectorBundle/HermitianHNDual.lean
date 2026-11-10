/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.HermitianSemistability
import ArakelovGeometry.AdelicVectorBundle.HermitianHNUniqueness

/-!
# Hermitian HN duality

Restriction of functionals identifies the quotient of two nested annihilators
with the dual of the corresponding actual subquotient. The completed norm
comparison uses all quotient lifts and the accepted local dual extension API.
-/

open scoped TensorProduct

noncomputable section

universe u v w

variable {K : Type u} [Field K] {E : Type w} [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

namespace Submodule

/-- Restrict functionals annihilating `U` to `W`. -/
def annihilatorRestriction (U W : Submodule K E) :
    U.dualAnnihilator →ₗ[K] Module.Dual K W :=
  W.subtype.dualMap.comp U.dualAnnihilator.subtype

omit [FiniteDimensional K E] in
/-- Restriction vanishes precisely on the larger subspace's annihilator. -/
theorem annihilatorRestriction_ker (U W : Submodule K E) :
    (annihilatorRestriction U W).ker = W.dualAnnihilator.comap U.dualAnnihilator.subtype := by
  ext ℓ
  rfl

omit [FiniteDimensional K E] in
/-- For nested subspaces every functional on `W` annihilating `U` extends
to an ambient functional still annihilating `U`. -/
theorem annihilatorRestriction_range (U W : Submodule K E) (hUW : U ≤ W) :
    (annihilatorRestriction U W).range = (U.comap W.subtype).dualAnnihilator := by
  ext ℓ
  constructor
  · rintro ⟨f, rfl⟩
    apply (mem_dualAnnihilator _).mpr
    intro x hx
    exact (mem_dualAnnihilator f.val).mp f.property x.val hx
  · intro hℓ
    obtain ⟨f, hf⟩ := LinearMap.dualMap_surjective_of_injective W.subtype_injective ℓ
    have hfU : f ∈ U.dualAnnihilator := by
      apply (mem_dualAnnihilator _).mpr
      intro x hx
      have hz := (mem_dualAnnihilator ℓ).mp hℓ ⟨x, hUW hx⟩ hx
      exact (DFunLike.congr_fun hf ⟨x, hUW hx⟩).trans hz
    exact ⟨⟨f, hfU⟩, hf⟩

/-- The canonical rational annihilator-factor / subquotient-dual isomorphism. -/
def annihilatorSubquotientEquivDual (U W : Submodule K E) (hUW : U ≤ W) :
    (U.dualAnnihilator ⧸ W.dualAnnihilator.comap U.dualAnnihilator.subtype) ≃ₗ[K]
      Module.Dual K (W ⧸ U.comap W.subtype) :=
  (quotEquivOfEq _ _ (annihilatorRestriction_ker U W).symm).trans
    ((annihilatorRestriction U W).quotKerEquivRange.trans
      ((LinearEquiv.ofEq _ _ (annihilatorRestriction_range U W hUW)).trans
        (U.comap W.subtype).dualQuotEquivDualAnnihilator.symm))

omit [FiniteDimensional K E] in
/-- The canonical reversed annihilator flag. -/
def reverseAnnihilatorFlag {n : ℕ} (F : Fin (n + 1) → Submodule K E) :
    Fin (n + 1) → Submodule K (Module.Dual K E) :=
  fun i => (F i.rev).dualAnnihilator

omit [FiniteDimensional K E] in
/-- Annihilator order reversal preserves the strictness of the reversed flag. -/
theorem strictMono_reverseAnnihilatorFlag {n : ℕ}
    (F : Fin (n + 1) → Submodule K E) (hF : StrictMono F) :
    StrictMono (reverseAnnihilatorFlag F) := by
  intro i j hij
  have hf := hF (Fin.rev_lt_rev.mpr hij)
  refine lt_of_le_of_ne (dualAnnihilator_anti hf.le) ?_
  intro he
  have hi := Subspace.dualAnnihilator_inj.mp he
  exact hf.ne hi.symm

omit [FiniteDimensional K E] in
theorem reverseAnnihilatorFlag_zero {n : ℕ}
    (F : Fin (n + 1) → Submodule K E) (htop : F (Fin.last n) = ⊤) :
    reverseAnnihilatorFlag F 0 = ⊥ := by
  simp [reverseAnnihilatorFlag, htop]

omit [FiniteDimensional K E] in
theorem reverseAnnihilatorFlag_last {n : ℕ}
    (F : Fin (n + 1) → Submodule K E) (hzero : F 0 = ⊥) :
    reverseAnnihilatorFlag F (Fin.last n) = ⊤ := by
  simp [reverseAnnihilatorFlag, hzero]

end Submodule

namespace ArakelovGeometry.NormFamily

variable {S : AdelicStructure.{u, v} K}

private theorem quotient_norm_quotEquivOfEq (ξ : NormFamily S E)
    (U W : Submodule K E) (h : U = W) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⧸ U)) :
    (ξ.quotient W).norm ω
        ((Submodule.quotEquivOfEq U W h).toLinearMap.baseChange (S.ϕ ω).Completion z) =
      (ξ.quotient U).norm ω z := by
  subst W
  have he : (Submodule.quotEquivOfEq U U rfl).toLinearMap = LinearMap.id := by
    ext x
    rfl
  rw [he, LinearMap.baseChange_id, LinearMap.id_apply]

omit [FiniteDimensional K E] in
private theorem restrict_norm_ofEq (ξ : NormFamily S E)
    (U W : Submodule K E) (h : U = W) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] U) :
    (ξ.restrict W).norm ω
        ((LinearEquiv.ofEq U W h).toLinearMap.baseChange (S.ϕ ω).Completion z) =
      (ξ.restrict U).norm ω z := by
  have hc : W.subtype.comp (LinearEquiv.ofEq U W h).toLinearMap = U.subtype := by
    ext x
    exact LinearEquiv.coe_ofEq_apply h x
  simp only [restrict_norm]
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hc]

/-- The canonical annihilator-factor map preserves the actual completed
quotient norms at every place, including coincident and zero subspaces. -/
theorem annihilatorSubquotientEquivDual_norm_eq (ξ : NormFamily S E)
    (hξ : ξ.IsUltrametric)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (U W : Submodule K E) (hUW : U ≤ W) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      (U.dualAnnihilator ⧸ W.dualAnnihilator.comap U.dualAnnihilator.subtype)) :
    ((ξ.restrict W).quotient (U.comap W.subtype)).dual.norm ω
        ((Submodule.annihilatorSubquotientEquivDual U W hUW).toLinearMap.baseChange
          (S.ϕ ω).Completion z) =
      ((ξ.dual.restrict U.dualAnnihilator).quotient
        (W.dualAnnihilator.comap U.dualAnnihilator.subtype)).norm ω z := by
  let g := Submodule.annihilatorRestriction U W
  let e₀ := Submodule.quotEquivOfEq _ _ (Submodule.annihilatorRestriction_ker U W).symm
  let e₁ := g.quotKerEquivRange
  let e₂ := LinearEquiv.ofEq _ _ (Submodule.annihilatorRestriction_range U W hUW)
  let e₃ := (U.comap W.subtype).dualQuotEquivDualAnnihilator
  let z₀ := e₀.toLinearMap.baseChange (S.ϕ ω).Completion z
  let z₁ := e₁.toLinearMap.baseChange (S.ϕ ω).Completion z₀
  let z₂ := e₂.toLinearMap.baseChange (S.ϕ ω).Completion z₁
  have hker : W.subtype.dualMap.ker ≤ U.dualAnnihilator := by
    change W.dualAnnihilator ≤ U.dualAnnihilator
    exact Submodule.dualAnnihilator_anti hUW
  have h₀ := quotient_norm_quotEquivOfEq (ξ.dual.restrict U.dualAnnihilator)
    _ _ (Submodule.annihilatorRestriction_ker U W).symm ω z
  have h₁ := (ξ.dual.restrict U.dualAnnihilator).quotKerEquivRange_norm_eq g ω z₀
  have h₂ := ξ.dual.pushforward_restrict_range_norm_eq W.subtype.dualMap
    (LinearMap.dualMap_surjective_of_injective W.subtype_injective)
    U.dualAnnihilator hker ω z₁
  rw [← ξ.restrict_dual hξ hN W] at h₂
  have h₃ := restrict_norm_ofEq (ξ.restrict W).dual _ _
    (Submodule.annihilatorRestriction_range U W hUW) ω z₁
  have h₄ := (ξ.restrict W).quotient_dual_annihilator_norm_eq
    (U.comap W.subtype) ω (e₃.symm.toLinearMap.baseChange (S.ϕ ω).Completion z₂)
  have hi : e₃.toLinearMap.comp e₃.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact e₃.apply_symm_apply x
  change ((ξ.restrict W).quotient (U.comap W.subtype)).dual.norm ω
      (e₃.symm.toLinearMap.baseChange (S.ϕ ω).Completion z₂) =
    ((ξ.restrict W).dual.restrict (U.comap W.subtype).dualAnnihilator).norm ω
      (e₃.toLinearMap.baseChange (S.ϕ ω).Completion
        (e₃.symm.toLinearMap.baseChange (S.ϕ ω).Completion z₂)) at h₄
  have hiω := DFunLike.congr_fun
    (congrArg (fun f => f.baseChange (S.ϕ ω).Completion) hi) z₂
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply,
    LinearMap.baseChange_id, LinearMap.id_apply] at hiω
  rw [hiω] at h₄
  change ((ξ.dual.restrict U.dualAnnihilator).quotient g.ker).norm ω z₀ = _ at h₀
  change _ = ((ξ.dual.restrict U.dualAnnihilator).pushforward g.rangeRestrict
    g.surjective_rangeRestrict).norm ω z₁ at h₁
  change ((ξ.dual.restrict U.dualAnnihilator).pushforward g.rangeRestrict
    g.surjective_rangeRestrict).norm ω z₁ = _ at h₂
  change ((ξ.restrict W).dual.restrict (U.comap W.subtype).dualAnnihilator).norm ω z₂ =
    ((ξ.restrict W).dual.restrict g.range).norm ω z₁ at h₃
  have he : (Submodule.annihilatorSubquotientEquivDual U W hUW).toLinearMap =
      e₃.symm.toLinearMap.comp (e₂.toLinearMap.comp (e₁.toLinearMap.comp e₀.toLinearMap)) := rfl
  rw [he]
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply]
  exact h₄.trans (h₃.trans (h₂.symm.trans (h₁.symm.trans h₀)))

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.AdelicVectorBundle

variable {S : AdelicStructure.{u, v} K} [S.IsProper]

/-- An actual semistable Hermitian subquotient gives a semistable factor of
the reversed annihilator flag, with the negative actual mean slope. -/
theorem annihilatorSubquotient_semistable_slope (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN)
    (U W : Submodule K E) (hUW : U ≤ W)
    (hsemi : ((V.restrictOfMeasurableBase W hS).quotientOfMeasurableBase
      (U.comap W.subtype) hS).IsMeanSlopeSemistable hS hN) :
    (((V.dualOfMeasurableBase hS).restrictOfMeasurableBase
      U.dualAnnihilator hS).quotientOfMeasurableBase
        (W.dualAnnihilator.comap U.dualAnnihilator.subtype) hS).IsMeanSlopeSemistable hS hN ∧
    (((V.dualOfMeasurableBase hS).restrictOfMeasurableBase
      U.dualAnnihilator hS).quotientOfMeasurableBase
        (W.dualAnnihilator.comap U.dualAnnihilator.subtype) hS).slope hS hN =
      -((V.restrictOfMeasurableBase W hS).quotientOfMeasurableBase
        (U.comap W.subtype) hS).slope hS hN := by
  let Q := (V.restrictOfMeasurableBase W hS).quotientOfMeasurableBase
    (U.comap W.subtype) hS
  let A := ((V.dualOfMeasurableBase hS).restrictOfMeasurableBase
    U.dualAnnihilator hS).quotientOfMeasurableBase
      (W.dualAnnihilator.comap U.dualAnnihilator.subtype) hS
  let e := Submodule.annihilatorSubquotientEquivDual U W hUW
  have hQ : Q.toNormFamily.IsHermitian hN := (hV.restrict W).quotient _
  have hQD := (Q.isMeanSlopeSemistable_dual_iff_of_isHermitian hS hN hQ hsemi.1).mpr hsemi
  have hn : ∀ ω z, (Q.dualOfMeasurableBase hS).toNormFamily.norm ω
      (e.toLinearMap.baseChange (S.ϕ ω).Completion z) = A.toNormFamily.norm ω z :=
    V.toNormFamily.annihilatorSubquotientEquivDual_norm_eq hV.1 hN U W hUW
  have hs := A.slope_eq_of_completed_isometry (Q.dualOfMeasurableBase hS) e hS hN hn
  have hm := A.maximalSlope_eq_of_completed_isometry (Q.dualOfMeasurableBase hS) e hS hN hn
  have hr : 0 < Module.finrank K
      (U.dualAnnihilator ⧸ W.dualAnnihilator.comap U.dualAnnihilator.subtype) := by
    rw [e.finrank_eq]
    exact hQD.1
  have hmax := ((Q.dualOfMeasurableBase hS).isMeanSlopeSemistable_iff_maximalSlope_eq_slope
    hS hN hQD.1).mp hQD
  change A.IsMeanSlopeSemistable hS hN ∧ A.slope hS hN = -Q.slope hS hN
  refine ⟨(A.isMeanSlopeSemistable_iff_maximalSlope_eq_slope hS hN hr).mpr
    ((hm.trans hmax).trans (congrArg (fun x : ℝ => (x : EReal)) hs.symm)), ?_⟩
  have hmean := Q.slope_add_slope_dual_eq_zero_of_isHermitian hS hN hQ
  linarith

/-- The actual factors of a reversed annihilator flag are semistable with
the reversed negative primal means. No factor norm identification is assumed. -/
theorem reverseAnnihilatorFlag_semistable_slope (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN)
    {n : ℕ} (F : Fin (n + 1) → Submodule K E) (hF : Monotone F)
    (hsemi : ∀ i, (V.flagQuotientOfMeasurableBase F hS i).IsMeanSlopeSemistable hS hN)
    (i : Fin n) :
    ((V.dualOfMeasurableBase hS).flagQuotientOfMeasurableBase
      (Submodule.reverseAnnihilatorFlag F) hS i).IsMeanSlopeSemistable hS hN ∧
    ((V.dualOfMeasurableBase hS).flagQuotientOfMeasurableBase
      (Submodule.reverseAnnihilatorFlag F) hS i).slope hS hN =
      -(V.flagQuotientOfMeasurableBase F hS i.rev).slope hS hN := by
  have hUW := hF (Fin.castSucc_le_succ i.rev)
  let P (p : Fin (n + 1) × Fin (n + 1)) : Prop :=
    (((V.dualOfMeasurableBase hS).restrictOfMeasurableBase
      (F p.1).dualAnnihilator hS).quotientOfMeasurableBase
        ((F p.2).dualAnnihilator.comap
          (F p.1).dualAnnihilator.subtype) hS).IsMeanSlopeSemistable hS hN ∧
    (((V.dualOfMeasurableBase hS).restrictOfMeasurableBase
      (F p.1).dualAnnihilator hS).quotientOfMeasurableBase
        ((F p.2).dualAnnihilator.comap (F p.1).dualAnnihilator.subtype) hS).slope hS hN =
      -(V.flagQuotientOfMeasurableBase F hS i.rev).slope hS hN
  have hp : (i.succ.rev, i.castSucc.rev) = (i.rev.castSucc, i.rev.succ) := by
    simp only [Fin.rev_succ, Fin.rev_castSucc]
  change P (i.succ.rev, i.castSucc.rev)
  apply Eq.mpr (congrArg P hp)
  change _ ∧ _
  exact
    (V.annihilatorSubquotient_semistable_slope hS hN hV
      (F i.rev.castSucc) (F i.rev.succ) hUW (hsemi i.rev))

/-- The actual Hermitian dual HN flag is the reversed annihilator flag.
The proof supplies its factor semistability and strict decrease from the
completed factor isometry before invoking finite-flag uniqueness. -/
theorem hermitianHN_dual_flag (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) :
    V.hermitianHNLength hS hN hV =
      (V.dualOfMeasurableBase hS).hermitianHNLength hS hN hV.dual ∧
    ∀ j : Fin (V.hermitianHNLength hS hN hV + 1),
      (V.hermitianHNFlag hS hN hV j.rev).dualAnnihilator =
        (V.dualOfMeasurableBase hS).hermitianHNTerm hS hN hV.dual j.val := by
  let F := V.hermitianHNFlag hS hN hV
  have hF := V.hermitianHNFlag_strictMono hS hN hV
  have hsemi : ∀ i,
      (V.flagQuotientOfMeasurableBase F hS i).IsMeanSlopeSemistable hS hN := by
    intro i
    let U := V.hermitianHNTerm hS hN hV (i.val + 1)
    let W := V.hermitianHNTerm hS hN hV i.val
    have hk : (W.mkQ.comp U.subtype).ker = W.comap U.subtype := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    have he := congrArg (fun I : Submodule K U =>
      ((V.restrictOfMeasurableBase U hS).quotientOfMeasurableBase
        I hS).IsMeanSlopeSemistable hS hN) hk
    exact Eq.mp he (V.hermitianHNSubquotient_semistable_slope hS hN hV i).1
  have hfac := V.reverseAnnihilatorFlag_semistable_slope hS hN hV F hF.monotone hsemi
  have hβ : StrictAnti (fun i => (V.flagQuotientOfMeasurableBase F hS i).slope hS hN) := by
    intro i j hij
    change (V.flagQuotientOfMeasurableBase (V.hermitianHNFlag hS hN hV) hS j).slope hS hN <
      (V.flagQuotientOfMeasurableBase (V.hermitianHNFlag hS hN hV) hS i).slope hS hN
    rw [V.slope_hermitianHNFlag_quotient_eq_factor hS hN hV i,
      V.slope_hermitianHNFlag_quotient_eq_factor hS hN hV j]
    exact V.hermitianHNFactor_slope_strictAnti hS hN hV hij
  have hβD : StrictAnti (fun i => ((V.dualOfMeasurableBase hS).flagQuotientOfMeasurableBase
      (Submodule.reverseAnnihilatorFlag F) hS i).slope hS hN) := by
    intro i j hij
    change ((V.dualOfMeasurableBase hS).flagQuotientOfMeasurableBase
      (Submodule.reverseAnnihilatorFlag F) hS j).slope hS hN <
        ((V.dualOfMeasurableBase hS).flagQuotientOfMeasurableBase
          (Submodule.reverseAnnihilatorFlag F) hS i).slope hS hN
    rw [(hfac i).2, (hfac j).2]
    exact neg_lt_neg (hβ (Fin.rev_lt_rev.mpr hij))
  exact (V.dualOfMeasurableBase hS).semistableFlag_eq_hermitianHNTerm hS hN hV.dual
    (Submodule.reverseAnnihilatorFlag F)
    (Submodule.strictMono_reverseAnnihilatorFlag F hF)
    (Submodule.reverseAnnihilatorFlag_zero F (V.hermitianHNFlag_last hS hN hV))
    (Submodule.reverseAnnihilatorFlag_last F (V.hermitianHNFlag_zero hS hN hV))
    (fun i => (hfac i).1) hβD

/-- Each actual dual HN factor has the reversed negative primal mean.
The length cast is supplied by actual dual-flag uniqueness. -/
theorem slope_hermitianHNFactor_dual (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN)
    (i : Fin (V.hermitianHNLength hS hN hV)) :
    ((V.dualOfMeasurableBase hS).hermitianHNFactor hS hN hV.dual
      (Fin.cast (V.hermitianHN_dual_flag hS hN hV).1 i)).slope hS hN =
        -(V.hermitianHNFactor hS hN hV i.rev).slope hS hN := by
  let F := V.hermitianHNFlag hS hN hV
  let G := Submodule.reverseAnnihilatorFlag F
  let D := V.dualOfMeasurableBase hS
  have hflag := V.hermitianHN_dual_flag hS hN hV
  have hpair : (G i.castSucc, G i.succ) =
      (D.hermitianHNTerm hS hN hV.dual i.val,
        D.hermitianHNTerm hS hN hV.dual (i.val + 1)) :=
    Prod.ext (hflag.2 i.castSucc) (hflag.2 i.succ)
  let mean (p : Submodule K (Module.Dual K E) × Submodule K (Module.Dual K E)) : ℝ :=
    ((D.restrictOfMeasurableBase p.2 hS).quotientOfMeasurableBase
      (p.1.comap p.2.subtype) hS).slope hS hN
  have hm := congrArg mean hpair
  have hmD := D.slope_hermitianHNFlag_quotient_eq_factor hS hN hV.dual
    (Fin.cast hflag.1 i)
  have hfac : (D.flagQuotientOfMeasurableBase G hS i).slope hS hN =
      -(V.flagQuotientOfMeasurableBase F hS i.rev).slope hS hN := by
    have hsemi : ∀ j,
        (V.flagQuotientOfMeasurableBase F hS j).IsMeanSlopeSemistable hS hN := by
      intro j
      let U := V.hermitianHNTerm hS hN hV (j.val + 1)
      let W := V.hermitianHNTerm hS hN hV j.val
      have hk : (W.mkQ.comp U.subtype).ker = W.comap U.subtype := by
        rw [LinearMap.ker_comp, Submodule.ker_mkQ]
      have he := congrArg (fun I : Submodule K U =>
        ((V.restrictOfMeasurableBase U hS).quotientOfMeasurableBase
          I hS).IsMeanSlopeSemistable hS hN) hk
      exact Eq.mp he (V.hermitianHNSubquotient_semistable_slope hS hN hV j).1
    exact (V.reverseAnnihilatorFlag_semistable_slope hS hN hV F
      (V.hermitianHNFlag_strictMono hS hN hV).monotone hsemi i).2
  have hf := V.slope_hermitianHNFlag_quotient_eq_factor hS hN hV i.rev
  exact hmD.symm.trans (hm.symm.trans (hfac.trans (congrArg Neg.neg hf)))

/-- The actual canonical dual HN flag factors are isometric on every
completed vector to the actual duals of the reversed primal flag factors. -/
theorem exists_hermitianHNFlag_dual_factor_isometry (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN)
    (i : Fin (V.hermitianHNLength hS hN hV)) :
    ∃ e :
      ((V.dualOfMeasurableBase hS).hermitianHNTerm hS hN hV.dual (i.val + 1) ⧸
        ((V.dualOfMeasurableBase hS).hermitianHNTerm hS hN hV.dual i.val).comap
          ((V.dualOfMeasurableBase hS).hermitianHNTerm hS hN hV.dual (i.val + 1)).subtype) ≃ₗ[K]
      Module.Dual K
        (V.hermitianHNTerm hS hN hV (i.rev.val + 1) ⧸
          (V.hermitianHNTerm hS hN hV i.rev.val).comap
            (V.hermitianHNTerm hS hN hV (i.rev.val + 1)).subtype),
      ∀ ω z,
        (V.flagQuotientOfMeasurableBase (V.hermitianHNFlag hS hN hV) hS
          i.rev).toNormFamily.dual.norm ω (e.toLinearMap.baseChange (S.ϕ ω).Completion z) =
        ((V.dualOfMeasurableBase hS).flagQuotientOfMeasurableBase
          ((V.dualOfMeasurableBase hS).hermitianHNFlag hS hN hV.dual) hS
            (Fin.cast (V.hermitianHN_dual_flag hS hN hV).1 i)).toNormFamily.norm ω z := by
  let F := V.hermitianHNFlag hS hN hV
  let D := V.dualOfMeasurableBase hS
  let U := F i.rev.castSucc
  let W := F i.rev.succ
  have hflag := V.hermitianHN_dual_flag hS hN hV
  have hL : D.hermitianHNTerm hS hN hV.dual i.val = W.dualAnnihilator :=
    (hflag.2 i.castSucc).symm.trans
      (congrArg (fun j => (F j).dualAnnihilator) (Fin.rev_castSucc i))
  have hU : D.hermitianHNTerm hS hN hV.dual (i.val + 1) = U.dualAnnihilator :=
    (hflag.2 i.succ).symm.trans
      (congrArg (fun j => (F j).dualAnnihilator) (Fin.rev_succ i))
  let P (p : Submodule K (Module.Dual K E) × Submodule K (Module.Dual K E)) : Prop :=
    ∃ e : (p.2 ⧸ p.1.comap p.2.subtype) ≃ₗ[K] Module.Dual K (W ⧸ U.comap W.subtype),
      ∀ ω z, ((V.toNormFamily.restrict W).quotient (U.comap W.subtype)).dual.norm ω
        (e.toLinearMap.baseChange (S.ϕ ω).Completion z) =
          ((D.toNormFamily.restrict p.2).quotient (p.1.comap p.2.subtype)).norm ω z
  change P (D.hermitianHNTerm hS hN hV.dual i.val,
    D.hermitianHNTerm hS hN hV.dual (i.val + 1))
  have hp : (D.hermitianHNTerm hS hN hV.dual i.val,
      D.hermitianHNTerm hS hN hV.dual (i.val + 1)) =
    (W.dualAnnihilator, U.dualAnnihilator) := Prod.ext hL hU
  apply Eq.mpr (congrArg P hp)
  have hUW : U ≤ W := (V.hermitianHNFlag_strictMono hS hN hV).monotone
    (Fin.castSucc_le_succ i.rev)
  exact ⟨Submodule.annihilatorSubquotientEquivDual U W hUW,
    V.toNormFamily.annihilatorSubquotientEquivDual_norm_eq hV.1 hN U W hUW⟩

/-- Actual Hermitian ordered slopes reverse and negate under duality.
The rank cast uses the canonical finite-dimensional dual rank equality. -/
theorem hermitianHNOrderedSlope_dual (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) (j : Fin (Module.finrank K E)) :
    (V.dualOfMeasurableBase hS).hermitianHNOrderedSlope hS hN hV.dual
      (Fin.cast Subspace.dual_finrank_eq.symm j) =
        -V.hermitianHNOrderedSlope hS hN hV j.rev := by
  let D := V.dualOfMeasurableBase hS
  let i := V.hermitianHNFactorIndex hS hN hV j.rev
  let k := i.rev
  have hflag := V.hermitianHN_dual_flag hS hN hV
  have hu : V.hermitianHNFlag hS hN hV k.castSucc.rev =
      V.hermitianHNTerm hS hN hV (i.val + 1) := by
    simp only [k, Fin.rev_castSucc, Fin.rev_rev, hermitianHNFlag, Fin.val_succ]
  have hl : V.hermitianHNFlag hS hN hV k.succ.rev =
      V.hermitianHNTerm hS hN hV i.val := by
    simp only [k, Fin.rev_succ, Fin.rev_rev, hermitianHNFlag, Fin.val_castSucc]
  have hlow := congrArg (fun U : Submodule K (Module.Dual K E) => Module.finrank K U)
    ((congrArg Submodule.dualAnnihilator hu).symm.trans (hflag.2 k.castSucc))
  have hupp := congrArg (fun U : Submodule K (Module.Dual K E) => Module.finrank K U)
    ((congrArg Submodule.dualAnnihilator hl).symm.trans (hflag.2 k.succ))
  have hpi := V.hermitianHNFactorIndex_rank_interval hS hN hV j.rev
  have hdimU := Subspace.finrank_add_finrank_dualAnnihilator_eq
    (V.hermitianHNTerm hS hN hV (i.val + 1))
  have hdimL := Subspace.finrank_add_finrank_dualAnnihilator_eq
    (V.hermitianHNTerm hS hN hV i.val)
  have hint : Module.finrank K
        (D.hermitianHNTerm hS hN hV.dual (Fin.cast hflag.1 k).val) ≤
      (Fin.cast Subspace.dual_finrank_eq.symm j).val ∧
    (Fin.cast Subspace.dual_finrank_eq.symm j).val < Module.finrank K
      (D.hermitianHNTerm hS hN hV.dual ((Fin.cast hflag.1 k).val + 1)) := by
    change Module.finrank K (D.hermitianHNTerm hS hN hV.dual k.val) ≤ j.val ∧
      j.val < Module.finrank K (D.hermitianHNTerm hS hN hV.dual (k.val + 1))
    change _ = Module.finrank K (D.hermitianHNTerm hS hN hV.dual k.val) at hlow
    change _ = Module.finrank K (D.hermitianHNTerm hS hN hV.dual (k.val + 1)) at hupp
    rw [← hlow, ← hupp]
    change Module.finrank K (V.hermitianHNTerm hS hN hV i.val) ≤ j.rev.val ∧
      j.rev.val < Module.finrank K (V.hermitianHNTerm hS hN hV (i.val + 1)) at hpi
    have hj : j.rev.val = Module.finrank K E - 1 - j.val := by
      simp only [Fin.rev]
      omega
    have hjlt := j.isLt
    omega
  rw [D.hermitianHNOrderedSlope_eq_of_rank_interval hS hN hV.dual
    (Fin.cast Subspace.dual_finrank_eq.symm j) (Fin.cast hflag.1 k) hint,
    V.slope_hermitianHNFactor_dual hS hN hV k]
  exact congrArg (fun l => -(V.hermitianHNFactor hS hN hV l).slope hS hN) (Fin.rev_rev i)

/-- The last actual ordered Hermitian slope is the extended-real minimum.
Positive rank excludes the empty source list. -/
theorem hermitianHNOrderedSlope_last_eq_minimalSlope (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) (hr : 0 < Module.finrank K E) :
    (V.hermitianHNOrderedSlope hS hN hV (⟨0, hr⟩ : Fin (Module.finrank K E)).rev : EReal) =
      V.minimalSlope hS hN := by
  let D := V.dualOfMeasurableBase hS
  have hrD : 0 < Module.finrank K (Module.Dual K E) := by
    rwa [Subspace.dual_finrank_eq]
  have hb : (D.dualOfMeasurableBase hS).minimalSlope hS hN = V.minimalSlope hS hN := by
    symm
    apply V.minimalSlope_eq_of_completed_isometry _ (Module.evalEquiv K E) hS hN
    intro ω x
    simp only [dualOfMeasurableBase_toNormFamily, Module.evalEquiv_toLinearMap]
    by_cases hω : ω ∈ S.Ωfin
    · exact hV.1.dual_dual_norm_eval ω hω x
    · exact V.toNormFamily.dual_dual_norm_eval_eq_of_isRCLike ω (hN ω hω) x
  have hext := D.minimalSlope_dual_add_maximalSlope_eq_zero_of_isHermitian
    hS hN hV.dual hrD
  rw [hb] at hext
  obtain ⟨a, ha⟩ := V.exists_minimalSlope_eq_coe hS hN hr
  have hfirst := D.hermitianHNOrderedSlope_zero_eq_maximalSlope hS hN hV.dual hrD
  have hreverse := V.hermitianHNOrderedSlope_dual hS hN hV ⟨0, hr⟩
  change D.hermitianHNOrderedSlope hS hN hV.dual ⟨0, hrD⟩ =
    -V.hermitianHNOrderedSlope hS hN hV (⟨0, hr⟩ : Fin (Module.finrank K E)).rev at hreverse
  rw [ha, ← hfirst, ← EReal.coe_add, ← EReal.coe_zero, EReal.coe_eq_coe_iff] at hext
  have he : a = V.hermitianHNOrderedSlope hS hN hV
      (⟨0, hr⟩ : Fin (Module.finrank K E)).rev := by linarith
  exact (congrArg (fun x : ℝ => (x : EReal)) he).symm.trans ha.symm

/-- The final actual HN factor itself has mean equal to the ambient minimum. -/
theorem slope_hermitianHNFactor_last_eq_minimalSlope (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) (hr : 0 < Module.finrank K E) :
    ((V.hermitianHNFactor hS hN hV
      (⟨0, V.hermitianHNLength_pos_of_finrank_pos hS hN hV hr⟩ :
        Fin (V.hermitianHNLength hS hN hV)).rev).slope hS hN : EReal) =
      V.minimalSlope hS hN := by
  let j : Fin (Module.finrank K E) := ⟨0, hr⟩
  let i : Fin (V.hermitianHNLength hS hN hV) :=
    (⟨0, V.hermitianHNLength_pos_of_finrank_pos hS hN hV hr⟩ :
      Fin (V.hermitianHNLength hS hN hV)).rev
  have hi : i.val + 1 = V.hermitianHNLength hS hN hV := by
    simp only [i, Fin.val_rev]
    have hn := V.hermitianHNLength_pos_of_finrank_pos hS hN hV hr
    omega
  have hj : j.rev.val + 1 = Module.finrank K E := by
    simp only [j, Fin.val_rev]
    omega
  have hlt := V.hermitianHNTerm_lt hS hN hV i.val (i.val + 1) (by omega) (by omega)
  have hd := Submodule.finrank_lt_finrank_of_lt hlt
  have htop : V.hermitianHNTerm hS hN hV (i.val + 1) = ⊤ := by
    rw [hi]
    exact V.hermitianHNTerm_length_eq_top hS hN hV
  have hm := V.hermitianHNOrderedSlope_eq_of_rank_interval hS hN hV j.rev i
    (by rw [htop, finrank_top] at hd ⊢; omega)
  exact (congrArg (fun x : ℝ => (x : EReal)) hm).symm.trans
    (V.hermitianHNOrderedSlope_last_eq_minimalSlope hS hN hV hr)

end ArakelovGeometry.AdelicVectorBundle

end
