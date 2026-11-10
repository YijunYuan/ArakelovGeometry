/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NormalizedNumberFieldCurve
public import ArakelovGeometry.NumberTheory.NumberFieldLocalCoefficientRingLocalization

/-!
# Actual local unit-ball finite generation

A finite completed dual basis gives an actual scaled coefficient embedding
of the literal rational local unit ball into a finite free module over its
actual coefficient ring. The proved prime localization makes that ring
Noetherian. No global domination, coherence or coordinate-bound certificate
is assumed.
-/

@[expose] public section

open scoped TensorProduct NumberField

noncomputable section

namespace ArakelovGeometry.AdelicStructure

universe u v

variable {K : Type u} [Field K] [NumberField K] (S : AdelicStructure.{u, v} K)

/-- Actual finite-prime classification and the proved prime localization make
the intrinsic rational local coefficient ring Noetherian. -/
theorem isNoetherianRing_rationalLocalRing (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hnt : (S.ϕ ω).IsNontrivial) : IsNoetherianRing (S.rationalLocalRing ω hω) := by
  obtain ⟨p, _, hloc⟩ := S.exists_finitePlace_rationalLocalRing_localization ω hω hnt
  let := hloc
  exact IsLocalization.isNoetherianRing p.maximalIdeal.asIdeal.primeCompl
    (S.rationalLocalRing ω hω) inferInstance

end ArakelovGeometry.AdelicStructure

namespace ArakelovGeometry.NormFamily

open AdelicStructure

universe u v w

variable {K : Type u} [Field K] [NumberField K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- One produced nonzero actual integer uniformly bounds the actual completed
norms of all the finite rational dual coordinates. -/
theorem exists_integral_dualBasis_unitBound {ι : Type*} [Finite ι]
    (ξ : NormFamily S E) (b : Module.Basis ι K E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hnt : (S.ϕ ω).IsNontrivial) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ i,
      ξ.dual.norm ω (1 ⊗ₜ[K] (algebraMap (𝓞 K) K a • b.coord i)) ≤ 1 := by
  obtain ⟨C, hC⟩ := Finite.exists_le (fun i => ξ.dual.norm ω (1 ⊗ₜ[K] b.coord i))
  have hCpos : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨f, hf0, hf⟩ := exists_integral_absValue_lt_one ω hω hnt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hCpos) hf
  refine ⟨f ^ n, pow_ne_zero _ hf0, fun i => ?_⟩
  rw [ξ.dual.norm_rational_smul, map_pow, map_pow]
  calc
    (S.ϕ ω (algebraMap (𝓞 K) K f)) ^ n * ξ.dual.norm ω (1 ⊗ₜ[K] b.coord i) ≤
        (max C 1)⁻¹ * max C 1 :=
      mul_le_mul hn.le ((hC i).trans (le_max_left _ _))
        (ξ.dual.norm_nonneg _ _) (inv_nonneg.mpr hCpos.le)
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hCpos)

omit [NumberField K] in
/-- The actual dual evaluation inequality forces every produced scaled basis
coordinate of a literal unit-ball vector into the literal coefficient ring. -/
theorem scaledCoordinate_mem_rationalLocalRing {ι : Type*}
    (ξ : NormFamily S E) (b : Module.Basis ι K E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (a : 𝓞 K) (ha : ∀ i,
      ξ.dual.norm ω (1 ⊗ₜ[K] (algebraMap (𝓞 K) K a • b.coord i)) ≤ 1)
    {x : E} (hx : x ∈ ξ.rationalUnitBall ω) (i : ι) :
    algebraMap (𝓞 K) K a * b.coord i x ∈ S.rationalLocalRing ω hω := by
  rw [S.mem_rationalLocalRing]
  have heval := ξ.norm_dual_tmul_apply_tmul_le ω 1 1
    (algebraMap (𝓞 K) K a • b.coord i) x
  have hb : S.ϕ ω (algebraMap (𝓞 K) K a * b.coord i x) ≤
      ξ.dual.norm ω (1 ⊗ₜ[K] (algebraMap (𝓞 K) K a • b.coord i)) *
      ξ.norm ω (1 ⊗ₜ[K] x) := by
    simpa only [one_mul, AdelicStructure.norm_algebraMap_eq_absValue,
      LinearMap.smul_apply, smul_eq_mul] using heval
  exact hb.trans ((mul_le_mul (ha i) hx (ξ.norm_nonneg _ _) zero_le_one).trans_eq (mul_one 1))

/-- The actual literal local unit ball embeds in a finite coefficient module
using produced scaled dual coordinates. -/
def localUnitBallCoefficientEmbedding {ι : Type*}
    (ξ : NormFamily S E) (b : Module.Basis ι K E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hξ : ξ.IsUltrametric) (a : 𝓞 K) (ha : ∀ i,
      ξ.dual.norm ω (1 ⊗ₜ[K] (algebraMap (𝓞 K) K a • b.coord i)) ≤ 1) :
    ξ.rationalUnitBallModule ω hω hξ →ₗ[S.rationalLocalRing ω hω]
      (ι → S.rationalLocalRing ω hω) where
  toFun x i := ⟨algebraMap (𝓞 K) K a * b.coord i x,
    ξ.scaledCoordinate_mem_rationalLocalRing b ω hω a ha x.property i⟩
  map_add' x y := by
    funext i
    apply Subtype.ext
    exact (congrArg (fun t : K => algebraMap (𝓞 K) K a * t)
      ((b.coord i).map_add (x : E) (y : E))).trans (mul_add _ _ _)
  map_smul' r x := by
    funext i
    apply Subtype.ext
    change algebraMap (𝓞 K) K a * b.coord i ((r : K) • (x : E)) =
      (r : K) * (algebraMap (𝓞 K) K a * b.coord i (x : E))
    rw [(b.coord i).map_smul]
    change algebraMap (𝓞 K) K a * ((r : K) * b.coord i (x : E)) = _
    ring

omit [NumberField K] in
@[simp]
theorem localUnitBallCoefficientEmbedding_coe {ι : Type*}
    (ξ : NormFamily S E) (b : Module.Basis ι K E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hξ : ξ.IsUltrametric) (a : 𝓞 K) (ha : ∀ i,
      ξ.dual.norm ω (1 ⊗ₜ[K] (algebraMap (𝓞 K) K a • b.coord i)) ≤ 1)
    (x : ξ.rationalUnitBallModule ω hω hξ) (i : ι) :
    (ξ.localUnitBallCoefficientEmbedding b ω hω hξ a ha x i : K) =
      algebraMap (𝓞 K) K a * b.coord i (x : E) := rfl

/-- Nonzero scaling preserves actual basis-coordinate injectivity. -/
theorem localUnitBallCoefficientEmbedding_injective {ι : Type*}
    (ξ : NormFamily S E) (b : Module.Basis ι K E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hξ : ξ.IsUltrametric) (a : 𝓞 K) (ha0 : a ≠ 0) (ha : ∀ i,
      ξ.dual.norm ω (1 ⊗ₜ[K] (algebraMap (𝓞 K) K a • b.coord i)) ≤ 1) :
    Function.Injective (ξ.localUnitBallCoefficientEmbedding b ω hω hξ a ha) := by
  have haK : algebraMap (𝓞 K) K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha0
  intro x y h
  apply Subtype.ext
  apply b.ext_elem
  intro i
  exact mul_left_cancel₀ haK (congrArg (fun z => (z i).val) h)

/-- A genuine finite dual basis and actual coefficient-ring Noetherianity
produce finite generation of the literal local unit ball. -/
theorem fg_rationalUnitBallModule_of_basis {ι : Type*} [Finite ι]
    (ξ : NormFamily S E) (b : Module.Basis ι K E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric) :
    (ξ.rationalUnitBallModule ω hω hξ).FG := by
  let := S.isNoetherianRing_rationalLocalRing ω hω hnt
  obtain ⟨a, ha0, ha⟩ := ξ.exists_integral_dualBasis_unitBound b ω hω hnt
  have hfinite : Module.Finite (S.rationalLocalRing ω hω)
      (ξ.rationalUnitBallModule ω hω hξ) :=
    Module.Finite.of_injective (ξ.localUnitBallCoefficientEmbedding b ω hω hξ a ha)
      (ξ.localUnitBallCoefficientEmbedding_injective b ω hω hξ a ha0 ha)
  exact Module.Finite.iff_fg.mp hfinite

/-- Every finite-dimensional literal rational local unit ball is finitely
generated at a genuine nontrivial finite number-field place, without any
global coherence or domination hypothesis. -/
theorem fg_rationalUnitBallModule (ξ : NormFamily S E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric) :
    (ξ.rationalUnitBallModule ω hω hξ).FG :=
  ξ.fg_rationalUnitBallModule_of_basis (Module.finBasis K E) ω hω hnt hξ

/-- The actual normalized number-field curve has pointwise nontrivial values,
so every finite-place literal local unit ball is actually finitely generated. -/
theorem fg_normalizedRationalUnitBallModule
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) (hξ : ξ.IsUltrametric) :
    (ξ.rationalUnitBallModule ω hω hξ).FG :=
  ξ.fg_rationalUnitBallModule ω hω
    (NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω)) hξ

end ArakelovGeometry.NormFamily

end
