/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldFullLatticeGlobalBall
public import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldLineIndex
public import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldPurity

/-!
# Actual completed gauges and the original integral-line index

The literal completed full-lattice gauges are pure. In dimension one their
finite logarithmic sum reads the cyclic quotient of the original integral
lattice, with positive finite cardinality proved independently of the logarithm.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct nonZeroDivisors
noncomputable section

namespace ArakelovGeometry.NumberFieldLineIndex

variable {K : Type*} [Field K] [NumberField K]

/-- Every nonzero element of an actual integral ideal has positive cyclic index. -/
theorem ideal_cyclicQuotient_card_pos (I : Ideal (𝓞 K)) (x : I) (hx : x ≠ 0) :
    0 < Nat.card (I ⧸ Submodule.span (𝓞 K) {x}) := by
  have hxR : (x : 𝓞 K) ≠ 0 := fun h => hx (Subtype.ext h)
  have hN : Ideal.absNorm (Ideal.span {(x : 𝓞 K)}) ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr (by simpa using hxR)
  have hprod := ideal_cyclicQuotient_card_mul_absNorm I x
  apply Nat.pos_of_ne_zero
  intro hz
  apply hN
  rw [← hprod, hz, zero_mul]

/-- Finiteness is derived for the literal quotient, rather than inferred from its logarithm. -/
theorem ideal_cyclicQuotient_finite (I : Ideal (𝓞 K)) (x : I) (hx : x ≠ 0) :
    Finite (I ⧸ Submodule.span (𝓞 K) {x}) :=
  Nat.finite_of_card_ne_zero (ideal_cyclicQuotient_card_pos I x hx).ne'

/-- Denominator clearing proves positive index for every nonzero fractional-ideal element. -/
theorem fractionalIdeal_cyclicQuotient_card_pos (J : FractionalIdeal (𝓞 K)⁰ K)
    (x : J.val) (hx : x ≠ 0) :
    0 < Nat.card (J.val ⧸ Submodule.span (𝓞 K) {x}) := by
  let e : J.val ≃ₗ[𝓞 K] J.num := J.equivNumOfIsLocalization
  rw [NumberFieldBoundedIndex.cyclicQuotient_card_eq e x]
  exact ideal_cyclicQuotient_card_pos J.num (e x)
    (fun h => hx (e.injective (h.trans (map_zero e).symm)))

/-- The original fractional-ideal cyclic quotient is finite for every nonzero element. -/
theorem fractionalIdeal_cyclicQuotient_finite (J : FractionalIdeal (𝓞 K)⁰ K)
    (x : J.val) (hx : x ≠ 0) :
    Finite (J.val ⧸ Submodule.span (𝓞 K) {x}) :=
  Nat.finite_of_card_ne_zero (fractionalIdeal_cyclicQuotient_card_pos J x hx).ne'

end ArakelovGeometry.NumberFieldLineIndex

namespace ArakelovGeometry.NumberFieldFullLattice

open AdelicStructure ActualPrimeIndexing NumberFieldLineIndex
attribute [local instance 2000] Algebra.toModule Algebra.toSMul

variable {K : Type*} [Field K] [NumberField K]
  {E : Type*} [AddCommGroup E] [Module K E]

/-- All finite norms of the actual full-lattice family are in the completed value group. -/
theorem fullLatticeGaugeFamily_isPureAtFinitePlaces (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤)
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) E) :
    (fullLatticeGaugeFamily L hfg hspan η).IsPureAtFinitePlaces := by
  intro ω hω z hz
  obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
  rw [fullLatticeGaugeFamily_norm_prime, scalarLatticeGauge_eq_localBasisNorm]
  exact NormFamily.ofBasis_isPureAtFinitePlaces
    (rationalLocalGenericBasis L hfg hspan p) _ (normalizedPrimeParameter_mem_fin p) z hz

/-- The literal completed full-lattice family has zero impurity in every dimension. -/
theorem fullLatticeGaugeFamily_globalImpurity_eq_zero (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤)
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) E) :
    (fullLatticeGaugeFamily L hfg hspan η).globalImpurity = 0 :=
  (fullLatticeGaugeFamily_isPureAtFinitePlaces L hfg hspan η).globalImpurity_eq_zero

variable [FiniteDimensional K E]

/-- The original finitely generated integral line has positive index at every nonzero vector. -/
theorem line_cyclicQuotient_card_pos (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hrank : Module.finrank K E = 1) (x : L) (hx : x ≠ 0) :
    0 < Nat.card (L ⧸ Submodule.span (𝓞 K) {x}) := by
  let e : K ≃ₗ[K] E := (Module.nonempty_linearEquiv_of_finrank_eq_one hrank).some
  let J : FractionalIdeal (𝓞 K)⁰ K :=
    ⟨L.map (e.symm.toLinearMap.restrictScalars (𝓞 K)),
      FractionalIdeal.isFractional_of_fg (hfg.map _)⟩
  let g : L ≃ₗ[𝓞 K] J.val :=
    Submodule.equivMapOfInjective (e.symm.toLinearMap.restrictScalars (𝓞 K))
      e.symm.injective L
  rw [NumberFieldBoundedIndex.cyclicQuotient_card_eq g x]
  exact fractionalIdeal_cyclicQuotient_card_pos J (g x)
    (fun h => hx (g.injective (h.trans (map_zero g).symm)))

/-- Finiteness of the original integral-line quotient is proved without any norm assumptions. -/
theorem line_cyclicQuotient_finite (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hrank : Module.finrank K E = 1) (x : L) (hx : x ≠ 0) :
    Finite (L ⧸ Submodule.span (𝓞 K) {x}) :=
  Nat.finite_of_card_ne_zero (line_cyclicQuotient_card_pos L hfg hrank x hx).ne'

/-- The original completed scalar-infimum gauges give the original integral-line index. -/
theorem line_completedGauge_finite_log_index (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (hrank : Module.finrank K E = 1)
    (x : L) (hx : x ≠ 0) :
    (∑' p : HeightOneSpectrum (𝓞 K),
      (normalizedNumberFieldAdelicStructure K).v.real {normalizedPrimeParameter p} *
        (-Real.log (scalarLatticeGauge
          (F := ((normalizedNumberFieldAdelicStructure K).ϕ
            (normalizedPrimeParameter p)).Completion)
          (NumberFieldModel.completedLatticeSpan L p : Set _)
          ((1 : ((normalizedNumberFieldAdelicStructure K).ϕ
            (normalizedPrimeParameter p)).Completion) ⊗ₜ[K] (x : E))))) =
      Real.log (Nat.card (L ⧸ Submodule.span (𝓞 K) {x})) := by
  let η := NormFamily.ofBasis (normalizedNumberFieldAdelicStructure K) E (Module.finBasis K E)
  let ξ := fullLatticeGaugeFamily L hfg hspan η
  have hU : ξ.IsUltrametric := fullLatticeGaugeFamily_isUltrametric L hfg hspan η
  have hL : ξ.globalUnitBallModule hU = L :=
    fullLatticeGaugeFamily_globalUnitBallModule_eq L hfg hspan η hU
  let e : ξ.globalUnitBallModule hU ≃ₗ[𝓞 K] L := LinearEquiv.ofEq _ _ hL
  let y := e.symm x
  have hy : y ≠ 0 := fun h => hx (e.symm.injective (h.trans (map_zero e.symm).symm))
  have hfgξ : (ξ.globalUnitBallModule hU).FG := hL.symm ▸ hfg
  have hfinite := (fullLatticeGaugeFamily_coherent_and_dominated L hfg hspan η).1
  have hσ := fullLatticeGaugeFamily_globalImpurity_eq_zero L hfg hspan η
  have h := ξ.normalizedLineGlobalUnitBall_finite_log_index hU hfinite hfgξ hσ hrank y hy
  rw [NumberFieldBoundedIndex.cyclicQuotient_card_eq e y, e.apply_symm_apply] at h
  convert h using 1
  apply tsum_congr
  intro p
  rw [NormFamily.logNorm, fullLatticeGaugeFamily_norm_prime]
  rfl

/-- A nonzero vector in an actual full integral line has finite logarithmic-gauge support. -/
theorem line_completedGauge_log_support_finite (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (hrank : Module.finrank K E = 1)
    (x : L) (hx : x ≠ 0) :
    (Function.support fun p : HeightOneSpectrum (𝓞 K) =>
      Real.log (scalarLatticeGauge
        (F := ((normalizedNumberFieldAdelicStructure K).ϕ
          (normalizedPrimeParameter p)).Completion)
        (NumberFieldModel.completedLatticeSpan L p : Set _)
        ((1 : ((normalizedNumberFieldAdelicStructure K).ϕ
          (normalizedPrimeParameter p)).Completion) ⊗ₜ[K] (x : E)))).Finite := by
  classical
  let η := NormFamily.ofBasis (normalizedNumberFieldAdelicStructure K) E (Module.finBasis K E)
  let ξ := fullLatticeGaugeFamily L hfg hspan η
  have hU : ξ.IsUltrametric := fullLatticeGaugeFamily_isUltrametric L hfg hspan η
  have hL : ξ.globalUnitBallModule hU = L :=
    fullLatticeGaugeFamily_globalUnitBallModule_eq L hfg hspan η hU
  have hfgξ : (ξ.globalUnitBallModule hU).FG := hL.symm ▸ hfg
  have hfinite := (fullLatticeGaugeFamily_coherent_and_dominated L hfg hspan η).1
  have hσ := fullLatticeGaugeFamily_globalImpurity_eq_zero L hfg hspan η
  let e : K ≃ₗ[K] E := (Module.nonempty_linearEquiv_of_finrank_eq_one hrank).some
  let J := ξ.normalizedLineCoordinateIdeal hU hfgξ e
  let P := FractionalIdeal.spanSingleton (𝓞 K)⁰ (e.symm (x : E))
  have hxE : (x : E) ≠ 0 := fun h => hx (Subtype.ext h)
  have ha : e.symm (x : E) ≠ 0 :=
    fun h => hxE (e.symm.injective (h.trans (map_zero e.symm).symm))
  have hJ : {p : HeightOneSpectrum (𝓞 K) | FractionalIdeal.count K p J ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors J)
  have hP : {p : HeightOneSpectrum (𝓞 K) | FractionalIdeal.count K p P ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors P)
  apply (hJ.union hP).subset
  intro p hp
  by_contra hout
  have h0 := not_or.mp hout
  have hcJ : FractionalIdeal.count K p J = 0 := not_not.mp h0.1
  have hcP : FractionalIdeal.count K p P = 0 := not_not.mp h0.2
  have hprincipal := fractionalIdeal_count_spanSingleton p ha
  change FractionalIdeal.count K p P = _ at hprincipal
  have hlog : ξ.logNorm (x : E) (normalizedPrimeParameter p) = 0 := by
    rw [ξ.normalizedLineCoordinateIdeal_logNorm hU hfinite hfgξ hσ e p hxE]
    change normalizedPrimeLogScale p *
      (((p.valuation K (e.symm (x : E))).log : ℝ) + FractionalIdeal.count K p J) = 0
    rw [hcJ]
    have hv : (p.valuation K (e.symm (x : E))).log = 0 := by
      rw [hcP] at hprincipal
      omega
    simp only [hv, Int.cast_zero, add_zero, mul_zero]
  apply hp
  rw [NormFamily.logNorm, fullLatticeGaugeFamily_norm_prime] at hlog
  exact hlog

end ArakelovGeometry.NumberFieldFullLattice
