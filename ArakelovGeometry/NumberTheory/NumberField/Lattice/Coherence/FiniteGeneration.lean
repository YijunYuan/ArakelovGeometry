/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Basic
public import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.Basic
public import ArakelovGeometry.NumberTheory.NumberField.Lattice.UnitBall.Global

import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Rational
import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.PrimeIndexing

/-!
# Finite generation of the actual normalized global unit ball

Actual completed dual norms construct rank-one coefficient norm families.
Their lower domination and the actual evaluation inequality embed the literal
global integral unit ball into a finite product of produced rank-one modules.
-/

@[expose] public section

open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The scalar norm family defined by the one-element basis of the base field. -/
def scalarBasisFamily : NormFamily S K :=
  ofBasis S K (Module.Basis.singleton PUnit.{1} K)

private theorem scalarBasisFamily_norm_rational (ω : S.Ω) (a : K) :
    (scalarBasisFamily (S := S)).norm ω (1 ⊗ₜ[K] a) = S.ϕ ω a := by
  have hunit : (scalarBasisFamily (S := S)).norm ω (1 ⊗ₜ[K] (1 : K)) = 1 := by
    change (ofBasis S K (Module.Basis.singleton PUnit.{1} K)).norm ω
      (1 ⊗ₜ[K] (1 : K)) = 1
    simpa using ofBasis_norm_tmul_basis S K (Module.Basis.singleton PUnit.{1} K)
      ω (1 : (S.ϕ ω).Completion) PUnit.unit
  have h := (scalarBasisFamily (S := S)).norm_rational_smul ω a (1 : K)
  have ha : (scalarBasisFamily (S := S)).norm ω (1 ⊗ₜ[K] a) =
      S.ϕ ω a * (scalarBasisFamily (S := S)).norm ω (1 ⊗ₜ[K] (1 : K)) := by
    simpa only [smul_eq_mul, mul_one] using h
  exact ha.trans ((congrArg (fun r : ℝ => S.ϕ ω a * r) hunit).trans (mul_one _))

private theorem scalarBasisFamily_isUltrametric :
    (scalarBasisFamily (S := S)).IsUltrametric := by
  constructor
  intro ω hω x y
  change (ofBasis S K (Module.Basis.singleton PUnit.{1} K)).norm ω (x + y) ≤
    max ((ofBasis S K (Module.Basis.singleton PUnit.{1} K)).norm ω x)
      ((ofBasis S K (Module.Basis.singleton PUnit.{1} K)).norm ω y)
  have h := ofBasisMixed_isUltrametric (S := S)
    (Module.Basis.singleton PUnit.{1} K) ω hω x y
  simpa only [ofBasisMixed_norm_of_finite (Module.Basis.singleton PUnit.{1} K) ω hω] using h

/-- The genuine completed rank-one norm, divided by the actual completed dual
norm of a nonzero rational functional. -/
def dualCoefficientFamily (ξ : NormFamily S E) (ℓ : Module.Dual K E) (hℓ : ℓ ≠ 0) :
    NormFamily S K :=
  (scalarBasisFamily (S := S)).scale
    (fun ω => (ξ.dual.norm ω (1 ⊗ₜ[K] ℓ))⁻¹)
    (fun ω => inv_pos.mpr (ξ.dual.norm_rational_pos ω hℓ))

/-- Literal rational coefficient norms are the actual absolute value divided
by the actual completed dual norm, including the zero scalar. -/
theorem dualCoefficientFamily_norm_rational
    (ξ : NormFamily S E) (ℓ : Module.Dual K E) (hℓ : ℓ ≠ 0) (ω : S.Ω) (a : K) :
    (ξ.dualCoefficientFamily ℓ hℓ).norm ω (1 ⊗ₜ[K] a) =
      S.ϕ ω a / ξ.dual.norm ω (1 ⊗ₜ[K] ℓ) := by
  rw [dualCoefficientFamily, scale_norm, scalarBasisFamily_norm_rational]
  exact inv_mul_eq_div _ _

/-- The exact actual logarithmic coefficient formula for nonzero scalars. -/
theorem dualCoefficientFamily_logNorm
    (ξ : NormFamily S E) (ℓ : Module.Dual K E) (hℓ : ℓ ≠ 0) {a : K} (ha : a ≠ 0)
    (ω : S.Ω) :
    (ξ.dualCoefficientFamily ℓ hℓ).logNorm a ω =
      Real.log (S.ϕ ω a) - ξ.dual.logNorm ℓ ω := by
  change Real.log ((ξ.dualCoefficientFamily ℓ hℓ).norm ω (1 ⊗ₜ[K] a)) = _
  rw [dualCoefficientFamily_norm_rational,
    Real.log_div (ne_of_gt ((S.ϕ ω).pos ha)) (ne_of_gt (ξ.dual.norm_rational_pos ω hℓ))]
  rfl

/-- Actual finite coefficient norms are ultrametric, independently of the
ultrametricity of the original norm family. -/
instance dualCoefficientFamily_isUltrametric
    (ξ : NormFamily S E) (ℓ : Module.Dual K E) (hℓ : ℓ ≠ 0) :
    (ξ.dualCoefficientFamily ℓ hℓ).IsUltrametric :=
  (scale_isUltrametric_iff _ _ _).mpr scalarBasisFamily_isUltrametric

/-- Upper domination of the genuine dual produces lower domination of every
actual nonzero-functional coefficient family. -/
theorem IsUpperDominated.dualCoefficientFamily_isLowerDominated
    {ξ : NormFamily S E} (hdual : ξ.dual.IsUpperDominated)
    (ℓ : Module.Dual K E) (hℓ : ℓ ≠ 0) :
    (ξ.dualCoefficientFamily ℓ hℓ).IsLowerDominated := by
  constructor
  intro a ha
  obtain ⟨A, hAi, hA⟩ := hdual ℓ hℓ
  refine ⟨fun ω => Real.log (S.ϕ ω a) - A ω, (S.integrable_log a ha).sub hAi, ?_⟩
  filter_upwards [hA] with ω hω
  rw [dualCoefficientFamily_logNorm ξ ℓ hℓ ha]
  exact sub_le_sub_left hω _

/-- The actual dual evaluation inequality puts every global vector's coefficient
in the corresponding literal rank-one global ball. -/
theorem dualCoefficientFamily_eval_mem_globalUnitBall
    (ξ : NormFamily S E) (ℓ : Module.Dual K E) (hℓ : ℓ ≠ 0)
    {x : E} (hx : x ∈ ξ.globalUnitBall) :
    ℓ x ∈ (ξ.dualCoefficientFamily ℓ hℓ).globalUnitBall := by
  intro ω hω
  change (ξ.dualCoefficientFamily ℓ hℓ).norm ω (1 ⊗ₜ[K] ℓ x) ≤ 1
  rw [dualCoefficientFamily_norm_rational,
    div_le_iff₀ (ξ.dual.norm_rational_pos ω hℓ), one_mul]
  have heval := ξ.norm_dual_tmul_apply_tmul_le ω 1 1 ℓ x
  have heval' : S.ϕ ω (ℓ x) ≤
      ξ.dual.norm ω (1 ⊗ₜ[K] ℓ) * ξ.norm ω (1 ⊗ₜ[K] x) := by
    simpa only [one_mul, AdelicStructure.norm_algebraMap_eq_absValue] using heval
  exact heval'.trans ((mul_le_mul_of_nonneg_left (hx ω hω)
    (ξ.dual.norm_nonneg ω _)).trans_eq (mul_one _))

variable [NumberField K]

open AdelicStructure ActualPrimeIndexing

omit [FiniteDimensional K E] in
/-- Every basis coordinate functional is nonzero, including when the basis
index type is empty and this statement has no instances. -/
theorem basisCoordinate_ne_zero {ι : Type*} (b : Module.Basis ι K E) (i : ι) :
    b.coord i ≠ 0 := by
  classical
  intro h
  have he := congrArg (fun ℓ : Module.Dual K E => ℓ (b i)) h
  simp [Module.Basis.coord_apply] at he

/-- The literal rank-one global coefficient module of an actual finite dual basis. -/
def normalizedBasisCoefficientModule {ι : Type*}
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (b : Module.Basis ι K E) (i : ι) : Submodule (𝓞 K) K :=
  (ξ.dualCoefficientFamily (b.coord i) (basisCoordinate_ne_zero b i)).globalUnitBallModule
    (hξ := (ξ.dualCoefficientFamily_isUltrametric (b.coord i) (basisCoordinate_ne_zero b i)))

/-- Actual dual upper domination and the native arithmetic rank-one theorem
produce finite generation of each basis coefficient module. -/
theorem IsUpperDominated.fg_normalizedBasisCoefficientModule {ι : Type*}
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hdual : ξ.dual.IsUpperDominated) (b : Module.Basis ι K E) (i : ι) :
    (ξ.normalizedBasisCoefficientModule b i).FG :=
  fg_globalUnitBallModule_rank_one _
    (hdom := (hdual.dualCoefficientFamily_isLowerDominated (b.coord i) (basisCoordinate_ne_zero b
        i)))

/-- The actual global unit-ball module maps linearly into the actual finite
product of its dual-basis coefficient modules. -/
def normalizedGlobalCoefficientEmbedding {ι : Type*}
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) [hξ : ξ.IsUltrametric]
    (b : Module.Basis ι K E) :
    ξ.globalUnitBallModule →ₗ[𝓞 K] (∀ i, ξ.normalizedBasisCoefficientModule b i) where
  toFun x i := ⟨b.coord i x.1,
    ξ.dualCoefficientFamily_eval_mem_globalUnitBall (b.coord i)
      (basisCoordinate_ne_zero b i) x.2⟩
  map_add' := by
    intro x y
    funext i
    apply Subtype.ext
    exact (b.coord i).map_add x.1 y.1
  map_smul' := by
    intro r x
    funext i
    apply Subtype.ext
    change b.coord i (algebraMap (𝓞 K) K r • x.1) =
      algebraMap (𝓞 K) K r • b.coord i x.1
    exact (b.coord i).map_smul _ _

/-- Equality of all actual basis coefficients forces equality of global vectors. -/
theorem normalizedGlobalCoefficientEmbedding_injective {ι : Type*}
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) [hξ : ξ.IsUltrametric]
    (b : Module.Basis ι K E) :
    Function.Injective (ξ.normalizedGlobalCoefficientEmbedding b) := by
  intro x y h
  apply Subtype.ext
  apply b.ext_elem
  intro i
  exact congrArg (fun z => (z i).val) h

/-- The genuine dual basis embeds the literal global ball into a finite product
of produced finite modules, so Noetherianity gives actual global finite generation. -/
theorem IsUpperDominated.fg_normalizedGlobalUnitBallModule_of_basis {ι : Type*} [Finite ι]
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hdual : ξ.dual.IsUpperDominated) (hξ : ξ.IsUltrametric) (b : Module.Basis ι K E) :
    (ξ.globalUnitBallModule).FG := by
  let : ∀ i, Module.Finite (𝓞 K) (ξ.normalizedBasisCoefficientModule b i) :=
    fun i => Module.Finite.iff_fg.mpr (hdual.fg_normalizedBasisCoefficientModule b i)
  have hfinite : Module.Finite (𝓞 K) (ξ.globalUnitBallModule) :=
    Module.Finite.of_injective (ξ.normalizedGlobalCoefficientEmbedding b)
      (ξ.normalizedGlobalCoefficientEmbedding_injective b)
  exact Module.Finite.iff_fg.mp hfinite

/-- Source Proposition 4.4.6 for the actual normalized number-field curve:
the literal global integral unit-ball module of a dominated finite-dimensional
family is finitely generated, without assuming coherence or spanning. -/
theorem IsDominated.fg_normalizedGlobalUnitBallModule
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hdom : ξ.IsDominated) (hξ : ξ.IsUltrametric) : (ξ.globalUnitBallModule).FG :=
  hdom.2.fg_normalizedGlobalUnitBallModule_of_basis hξ (Module.finBasis K E)

end ArakelovGeometry.NormFamily

end
