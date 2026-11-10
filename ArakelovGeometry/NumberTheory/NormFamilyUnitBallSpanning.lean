/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.Rational
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Rational unit balls of actual completed-fibre norm families

The rational unit ball is the literal set of original vectors whose norm in
the actual completed tensor fibre is at most one. At a genuinely nontrivial
nonarchimedean number-field place, powers of a nonzero algebraic integer move
every rational vector into this ball, proving Claim 4.4.3(b)'s spanning step.
-/

open scoped TensorProduct NumberField

namespace ArakelovGeometry.NormFamily

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E]

/-- The source's rational local unit ball, evaluated in the actual completed tensor fibre. -/
def rationalUnitBall (ξ : NormFamily S E) (ω : S.Ω) : Set E :=
  {x | ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) ≤ 1}

@[simp]
theorem mem_rationalUnitBall (ξ : NormFamily S E) (ω : S.Ω) (x : E) :
    x ∈ ξ.rationalUnitBall ω ↔
      ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) ≤ 1 := Iff.rfl

@[simp]
theorem zero_mem_rationalUnitBall (ξ : NormFamily S E) (ω : S.Ω) :
    (0 : E) ∈ ξ.rationalUnitBall ω := by
  simp [rationalUnitBall]

/-- Powers of one genuinely contracting rational scalar absorb each original vector. -/
theorem exists_pow_smul_mem_rationalUnitBall (ξ : NormFamily S E) (ω : S.Ω)
    {a : K} (ha : (S.ϕ ω) a < 1) (x : E) :
    ∃ n : ℕ, (a ^ n) • x ∈ ξ.rationalUnitBall ω := by
  let c := ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x)
  by_cases hc : c = 0
  · refine ⟨0, ?_⟩
    change ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ((a ^ 0) • x)) ≤ 1
    rw [pow_zero, one_smul]
    change c ≤ 1
    rw [hc]
    exact zero_le_one
  · have hcpos : 0 < c := lt_of_le_of_ne (ξ.norm_nonneg ω _) (Ne.symm hc)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hcpos) ha
    refine ⟨n, ?_⟩
    change ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ((a ^ n) • x)) ≤ 1
    rw [ξ.norm_rational_smul, map_pow]
    calc
      ((S.ϕ ω) a) ^ n * c ≤ c⁻¹ * c :=
        mul_le_mul_of_nonneg_right hn.le hcpos.le
      _ = 1 := inv_mul_cancel₀ hc

/-- A nontrivial nonarchimedean absolute value on a number field has a genuinely
contracting nonzero algebraic integer, obtained from its actual finite prime. -/
theorem exists_integral_absValue_lt_one [NumberField K] (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ (S.ϕ ω) (algebraMap (𝓞 K) K a) < 1 := by
  obtain ⟨p, hp⟩ := NumberField.exists_finitePlace_of_isNonarchimedean hnt hω
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot p.maximalIdeal.ne_bot
  refine ⟨a, ha0, (hp : (S.ϕ ω).IsEquiv p.val).lt_one_iff.mpr ?_⟩
  have h := (NumberField.FinitePlace.norm_lt_one_iff_mem
    (K := K) (v := p.maximalIdeal) (x := a)).mpr ha
  rwa [NumberField.FinitePlace.norm_embedding_eq] at h

/-- Every rational vector admits a nonzero actual integral scalar carrying it into
the literal completed-norm unit ball. -/
theorem exists_integral_smul_mem_rationalUnitBall [NumberField K]
    (ξ : NormFamily S E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hnt : (S.ϕ ω).IsNontrivial) (x : E) :
    ∃ a : 𝓞 K, a ≠ 0 ∧
      (algebraMap (𝓞 K) K a) • x ∈ ξ.rationalUnitBall ω := by
  obtain ⟨a, ha0, ha⟩ := exists_integral_absValue_lt_one ω hω hnt
  obtain ⟨n, hn⟩ := ξ.exists_pow_smul_mem_rationalUnitBall ω ha x
  exact ⟨a ^ n, pow_ne_zero _ ha0, by simpa only [map_pow] using hn⟩

/-- The actual rational local unit ball spans the entire original vector space. -/
theorem span_rationalUnitBall_eq_top [NumberField K] (ξ : NormFamily S E)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) :
    Submodule.span K (ξ.rationalUnitBall ω) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, ha, hx⟩ := ξ.exists_integral_smul_mem_rationalUnitBall ω hω hnt x
  have haK : algebraMap (𝓞 K) K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha
  have hmem := (Submodule.span K (ξ.rationalUnitBall ω)).smul_mem
    (algebraMap (𝓞 K) K a)⁻¹ (Submodule.subset_span hx)
  simpa only [smul_smul, inv_mul_cancel₀ haK, one_smul] using hmem

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.AdelicStructure

universe u v

variable {K : Type u} [Field K] (S : AdelicStructure.{u, v} K)

/-- The given nonarchimedean real absolute value, regarded canonically as an
NNReal-valued valuation of the original field. -/
def rationalValuation (ω : S.Ω) (hω : ω ∈ S.Ωfin) : Valuation K NNReal where
  toFun a := ⟨(S.ϕ ω) a, (S.ϕ ω).nonneg a⟩
  map_zero' := Subtype.ext (map_zero (S.ϕ ω))
  map_one' := Subtype.ext (map_one (S.ϕ ω))
  map_mul' a b := Subtype.ext ((S.ϕ ω).map_mul a b)
  map_add_le_max' a b := hω a b

@[simp]
theorem rationalValuation_coe (ω : S.Ω) (hω : ω ∈ S.Ωfin) (a : K) :
    (S.rationalValuation ω hω a : ℝ) = (S.ϕ ω) a := rfl

/-- The source's actual rational local coefficient ring `{a : K | |a|_ω ≤ 1}`. -/
noncomputable def rationalLocalRing (ω : S.Ω) (hω : ω ∈ S.Ωfin) : Subring K :=
  (S.rationalValuation ω hω).integer

@[simp]
theorem mem_rationalLocalRing (ω : S.Ω) (hω : ω ∈ S.Ωfin) (a : K) :
    a ∈ S.rationalLocalRing ω hω ↔ (S.ϕ ω) a ≤ 1 := Iff.rfl

/-- The actual field is the fraction field of its actual rational valuation ring. -/
instance rationalLocalRing_isFractionRing (ω : S.Ω) (hω : ω ∈ S.Ωfin) :
    IsFractionRing (S.rationalLocalRing ω hω) K :=
  (Valuation.integer.integers (S.rationalValuation ω hω)).isFractionRing

end ArakelovGeometry.AdelicStructure

namespace ArakelovGeometry.NormFamily

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E]

/-- The literal rational unit ball, with its genuine module structure over the
actual rational local valuation ring. -/
def rationalUnitBallModule (ξ : NormFamily S E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hξ : ξ.IsUltrametric) : Submodule (S.rationalLocalRing ω hω) E where
  carrier := ξ.rationalUnitBall ω
  zero_mem' := ξ.zero_mem_rationalUnitBall ω
  add_mem' {x y} hx hy := by
    change ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (x + y)) ≤ 1
    rw [TensorProduct.tmul_add]
    exact (hξ ω hω _ _).trans (max_le hx hy)
  smul_mem' r {x} hx := by
    change ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ((r : K) • x)) ≤ 1
    rw [ξ.norm_rational_smul]
    have hr : (S.ϕ ω) (r : K) ≤ 1 :=
      (S.mem_rationalLocalRing ω hω _).mp r.property
    exact (mul_le_mul_of_nonneg_right hr (ξ.norm_nonneg ω _)).trans
      (by simpa only [one_mul] using (ξ.mem_rationalUnitBall ω x).mp hx)

@[simp]
theorem coe_rationalUnitBallModule (ξ : NormFamily S E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hξ : ξ.IsUltrametric) :
    (ξ.rationalUnitBallModule ω hω hξ : Set E) = ξ.rationalUnitBall ω := rfl

/-- The inclusion of the actual rational unit ball is a genuine localization
at the nonzero elements of the actual rational local coefficient ring. -/
theorem isLocalizedModule_rationalUnitBallModule [NumberField K]
    (ξ : NormFamily S E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric) :
    IsLocalizedModule (nonZeroDivisors (S.rationalLocalRing ω hω))
      (ξ.rationalUnitBallModule ω hω hξ).subtype := by
  let R := S.rationalLocalRing ω hω
  let : IsLocalizedModule (nonZeroDivisors R) (LinearMap.id : E →ₗ[R] E) :=
    isLocalizedModule_id (nonZeroDivisors R) E K
  refine ⟨?_, ?_, ?_⟩
  · exact IsLocalizedModule.map_units (LinearMap.id : E →ₗ[R] E)
  · intro x
    obtain ⟨a, ha, hax⟩ := ξ.exists_integral_smul_mem_rationalUnitBall ω hω hnt x
    have haK : algebraMap (𝓞 K) K a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha
    let d : R := ⟨algebraMap (𝓞 K) K a,
      (S.mem_rationalLocalRing ω hω _).mpr
        (NumberField.abs_le_one_of_isIntegral hω (NumberField.RingOfIntegers.isIntegral_coe a))⟩
    have hd : d ≠ 0 := fun h ↦ haK (congrArg (fun r : R ↦ (r : K)) h)
    refine ⟨(⟨algebraMap (𝓞 K) K a • x, hax⟩,
      ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩), ?_⟩
    rfl
  · intro x y h
    have hxy : x = y := Subtype.ext h
    exact ⟨1, congrArg (fun z ↦ (1 : nonZeroDivisors R) • z) hxy⟩

/-- Claim 4.4.3(b): scalar extension of the actual rational local unit-ball
module to the actual number field recovers the original vector space. -/
noncomputable def rationalUnitBallGenericFibreEquiv [NumberField K]
    (ξ : NormFamily S E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric) :
    K ⊗[S.rationalLocalRing ω hω] (ξ.rationalUnitBallModule ω hω hξ) ≃ₗ[K] E := by
  letI := ξ.isLocalizedModule_rationalUnitBallModule ω hω hnt hξ
  exact (IsLocalizedModule.isBaseChange (nonZeroDivisors (S.rationalLocalRing ω hω))
    K (ξ.rationalUnitBallModule ω hω hξ).subtype).equiv

@[simp]
theorem rationalUnitBallGenericFibreEquiv_tmul [NumberField K]
    (ξ : NormFamily S E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric) (c : K)
    (x : ξ.rationalUnitBallModule ω hω hξ) :
    ξ.rationalUnitBallGenericFibreEquiv ω hω hnt hξ
      (c ⊗ₜ[S.rationalLocalRing ω hω] x) = c • (x : E) := by
  let := ξ.isLocalizedModule_rationalUnitBallModule ω hω hnt hξ
  exact IsBaseChange.equiv_tmul
    (IsLocalizedModule.isBaseChange (nonZeroDivisors (S.rationalLocalRing ω hω))
      K (ξ.rationalUnitBallModule ω hω hξ).subtype) c x

end ArakelovGeometry.NormFamily
