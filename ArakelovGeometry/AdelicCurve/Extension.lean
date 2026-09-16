/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Defs
import ArakelovGeometry.ExternalResults.AbsoluteValueFinite
import ArakelovGeometry.ExternalResults.AbsoluteValueExtension
import ArakelovGeometry.ExternalResults.AbsoluteValueLocal
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Basic


/-!
This file records the statement-level formalization of algebraic extensions of adelic
structures (Chen–Moriwaki, §3.3–§3.4): the fibre product parameter space of extensions of the
base absolute values, integration along fibres and its properties (§3.3.1–§3.3.2), the induced
measure on a finite separable extension (§3.3.3), finite extensions via the separable closure
(§3.4.1), and general algebraic extensions as projective limits (§3.4.2), including the
projective-limit fibre probability measures and the transitivity of the construction.
-/

namespace ArakelovGeometry

open MeasureTheory AbsoluteValue
open scoped ENNReal

universe u v w

/-! ### Equivalences of adelic structures -/

/-- An equivalence between two adelic structures on the same field: a measurable equivalence
of the parameter spaces matching the families of absolute values and transporting one measure
to the other. This packages the meaning of the equalities of adelic curves in Chen–Moriwaki,
Proposition 3.4.4 and Theorem 3.4.12. -/
structure AdelicStructure.Equiv {K : Type u} [Field K] (S : AdelicStructure.{u, v} K)
    (T : AdelicStructure.{u, w} K) where
  /-- The underlying measurable equivalence of parameter spaces. -/
  toMeasurableEquiv : S.Ω ≃ᵐ T.Ω
  /-- The equivalence matches the families of absolute values. -/
  ϕ_comp : ∀ x : S.Ω, T.ϕ (toMeasurableEquiv x) = S.ϕ x
  /-- The equivalence transports the measure of `S` to the measure of `T`. -/
  map_v : MeasureTheory.Measure.map toMeasurableEquiv S.v = T.v

/-! ### Power sums and maxima of absolute values -/

/-- Every power of a member of a finite distinct family is a fixed linear combination
of consecutive power sums of that family. The coefficients come from the inverse Vandermonde
matrix. -/
theorem exists_pow_eq_sum_shifted_sum_pow {F : Type*} [Field F] {d : ℕ} (α : Fin d → F)
    (hα : Function.Injective α) :
    ∃ c : Matrix (Fin d) (Fin d) F, ∀ i N, α i ^ N =
      ∑ r : Fin d, c i r * ∑ j, α j ^ (N + r.val) := by
  classical
  let V := (Matrix.vandermonde α).transpose
  have hV : IsUnit V.det := by
    change IsUnit (Matrix.vandermonde α).transpose.det
    rw [Matrix.det_transpose, isUnit_iff_ne_zero, Matrix.det_vandermonde_ne_zero_iff]
    exact hα
  refine ⟨V⁻¹, fun i N ↦ ?_⟩
  have hs : (fun r : Fin d ↦ ∑ j, α j ^ (N + r.val)) =
      V.mulVec (fun j ↦ α j ^ N) := by
    ext r
    simp [V, Matrix.mulVec, dotProduct, pow_add, mul_comm]
  change α i ^ N = ((V⁻¹).mulVec (fun r : Fin d ↦ ∑ j, α j ^ (N + r.val))) i
  rw [hs, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hV, Matrix.one_mulVec]

open Filter Topology in
/-- If the power sums of a finite distinct family in a normed field tend to zero, then each
individual power sequence tends to zero. -/
theorem tendsto_pow_zero_of_tendsto_sum_pow_zero {F : Type*} [NormedField F] {d : ℕ} (α : Fin d → F)
    (hα : Function.Injective α)
    (hs : Tendsto (fun N : ℕ ↦ ∑ i, α i ^ N) atTop (𝓝 0)) (i : Fin d) :
    Tendsto (fun N : ℕ ↦ α i ^ N) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := exists_pow_eq_sum_shifted_sum_pow α hα
  have ht (r : Fin d) : Tendsto (fun N : ℕ ↦ c i r * ∑ j, α j ^ (N + r.val))
      atTop (𝓝 (c i r * 0)) :=
    tendsto_const_nhds.mul (hs.comp (tendsto_add_atTop_nat r.val))
  have h := tendsto_finsetSum Finset.univ (fun r _ ↦ ht r)
  simpa only [mul_zero, Finset.sum_const_zero, ← hc] using h

open Filter Topology in
/-- Chen--Moriwaki, Lemma 3.3.5(1), formula (3.5): for finitely many distinct elements of a
field with an absolute value, the maximum of their absolute values is recovered from power
sums: `max_j |α_j| = limsup_N |α_1^N + ⋯ + α_d^N|^{1/N}`. -/
theorem _root_.AbsoluteValue.iSup_eq_limsup_sum_pow_rpow {F : Type*} [Field F]
    (v : AbsoluteValue F ℝ) {d : ℕ} (hd : 1 ≤ d) {α : Fin d → F}
    (hα : Function.Injective α) :
    (⨆ i, v (α i)) =
      Filter.limsup (fun N : ℕ ↦ (v (∑ i, α i ^ N)) ^ ((N : ℝ)⁻¹)) Filter.atTop := by
  let := v.toNormedField
  change (⨆ i, ‖α i‖) = limsup (fun N : ℕ ↦ ‖∑ i, α i ^ N‖ ^ ((N : ℝ)⁻¹)) atTop
  classical
  let i₀ : Fin d := ⟨0, hd⟩
  let : Nonempty (Fin d) := ⟨i₀⟩
  let M := ⨆ i, ‖α i‖
  let u (N : ℕ) := ‖∑ i, α i ^ N‖ ^ ((N : ℝ)⁻¹)
  let g (N : ℕ) := (d : ℝ) ^ ((N : ℝ)⁻¹) * M
  have hM : 0 ≤ M :=
    (norm_nonneg (α i₀)).trans (le_ciSup (Finite.bddAbove_range (fun j ↦ ‖α j‖)) i₀)
  have hbound (N : ℕ) : ‖∑ i, α i ^ N‖ ≤ (d : ℝ) * M ^ N := by
    calc
      ‖∑ i, α i ^ N‖ ≤ ∑ i, ‖α i ^ N‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin d, M ^ N := Finset.sum_le_sum fun i _ ↦ by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _)
          (le_ciSup (Finite.bddAbove_range (fun j ↦ ‖α j‖)) i) N
      _ = (d : ℝ) * M ^ N := by simp
  have hug : u ≤ᶠ[atTop] g := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : N ≠ 0 := by omega
    dsimp [u, g]
    calc
      _ ≤ ((d : ℝ) * M ^ N) ^ ((N : ℝ)⁻¹) :=
        Real.rpow_le_rpow (norm_nonneg _) (hbound N) (by positivity)
      _ = (d : ℝ) ^ ((N : ℝ)⁻¹) * M := by
        rw [Real.mul_rpow (Nat.cast_nonneg _) (pow_nonneg hM _),
          Real.pow_rpow_inv_natCast hM hN0]
  have hg : Tendsto g atTop (𝓝 M) := by
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    have ht := (Real.continuous_const_rpow hd0).continuousAt.tendsto.comp
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    simpa [g] using ht.mul_const M
  have hu_bdd := hg.isBoundedUnder_le.mono_le hug
  have hu_cobdd : IsCoboundedUnder (· ≤ ·) atTop u :=
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall
      (fun N : ℕ ↦ Real.rpow_nonneg (norm_nonneg (∑ i, α i ^ N)) ((N : ℝ)⁻¹)))).isCoboundedUnder_le
  apply le_antisymm
  · apply le_limsup_of_le hu_bdd
    intro b hb
    have hb0 : 0 ≤ b := by
      obtain ⟨N, hN⟩ := hb.exists
      exact (Real.rpow_nonneg (norm_nonneg _) _).trans hN
    refine ciSup_le fun i ↦ ?_
    by_contra hi
    have hib : b < ‖α i‖ := lt_of_not_ge hi
    have hi0 : 0 < ‖α i‖ := lt_of_le_of_lt hb0 hib
    have hia : α i ≠ 0 := norm_pos_iff.mp hi0
    have hβ : Function.Injective (fun j ↦ α j / α i) :=
      fun _ _ h ↦ hα ((div_left_inj' hia).mp h)
    have hp : ∀ᶠ N : ℕ in atTop, ‖∑ j, α j ^ N‖ ≤ b ^ N := by
      filter_upwards [hb, eventually_ge_atTop 1] with N hNb hN
      have hN0 : N ≠ 0 := by omega
      have hh := pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _) hNb N
      simpa only [u, Real.rpow_inv_natCast_pow (norm_nonneg _) hN0] using hh
    have hβnorm : ∀ᶠ N : ℕ in atTop,
        ‖∑ j, (α j / α i) ^ N‖ ≤ (b / ‖α i‖) ^ N := by
      filter_upwards [hp] with N hN
      simp_rw [div_pow]
      rw [← Finset.sum_div, norm_div, norm_pow]
      exact div_le_div_of_nonneg_right hN (pow_nonneg (norm_nonneg _) _)
    have ht : Tendsto (fun N : ℕ ↦ ∑ j, (α j / α i) ^ N) atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      exact squeeze_zero' (Eventually.of_forall (fun N ↦ norm_nonneg _)) hβnorm
        (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hb0 (norm_nonneg _))
          ((div_lt_one hi0).mpr hib))
    have ht' := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp
      (tendsto_pow_zero_of_tendsto_sum_pow_zero (fun j ↦ α j / α i) hβ ht i)
    simp [div_self hia] at ht'
  · exact (limsup_le_limsup hug hu_cobdd hg.isBoundedUnder_le).trans_eq hg.limsup_eq

/-! ### Algebraic extensions of adelic structures -/

section Extensions

namespace AdelicStructure

variable {K : Type u} [Field K] (AS : AdelicStructure.{u, v} K)
variable (L : Type w) [Field L] [Algebra K L]

/-- The parameter space for an extension of an adelic structure from `K` to an extension field
`L`: a point is a base parameter `ω : Ω_K` together with an absolute value on `L` whose
restriction to `K` is the base absolute value `|·|_ω`.

This is the fibre product `Ω_K ×_{M_K} M_L` appearing in Chen–Moriwaki, §3.3 and §3.4. -/
structure ParameterSpaceExtension : Type _ where
  /-- The underlying point of the base parameter space. -/
  base : AS.Ω
  /-- The extended absolute value on `L`. -/
  abv : AbsoluteValue L ℝ
  /-- The extended absolute value restricts to the base absolute value. -/
  restrict_eq : abv.restriction K = AS.ϕ base

namespace ParameterSpaceExtension

/-- Extension places are equal when their base point and extended absolute value agree. -/
@[ext]
theorem ext {x y : ParameterSpaceExtension AS L} (hbase : x.base = y.base) (habv : x.abv = y.abv) :
    x = y := by
  cases x
  cases y
  simp_all

/-- The projection `Ω_L → Ω_K`. -/
def proj {AS : AdelicStructure.{u, v} K} {L : Type w} [Field L] [Algebra K L]
    (x : ParameterSpaceExtension AS L) : AS.Ω :=
  x.base

/-- The parameter map `Ω_L → M_L`. -/
def ϕ {AS : AdelicStructure.{u, v} K} {L : Type w} [Field L] [Algebra K L]
    (x : ParameterSpaceExtension AS L) : AbsoluteValue L ℝ :=
  x.abv

/-- The fibre of the projection above a base point `ω`. -/
def fiber {AS : AdelicStructure.{u, v} K} (L : Type w) [Field L] [Algebra K L]
    (ω : AS.Ω) : Set (ParameterSpaceExtension AS L) :=
  {x | proj x = ω}

/-- The defining restriction property of the extended absolute value. -/
theorem ϕ_restriction (x : ParameterSpaceExtension AS L) :
    (ϕ x).restriction K = AS.ϕ (proj x) :=
  x.restrict_eq

/-- The σ-algebra on `Ω_L` generated by the projection to `Ω_K` and all evaluation maps
`x ↦ |a|_x`, `a : L` (Chen–Moriwaki, §3.3, p. 178). -/
instance instMeasurableSpace : MeasurableSpace (ParameterSpaceExtension AS L) :=
  MeasurableSpace.comap (proj (AS := AS) (L := L)) AS.A ⊔
    ⨆ a : L, MeasurableSpace.comap (fun x : ParameterSpaceExtension AS L ↦ (ϕ x) a)
      inferInstance

/-- The projection to the base parameter space is measurable by construction. -/
theorem measurable_proj : Measurable (proj (AS := AS) (L := L)) :=
  Measurable.of_comap_le le_sup_left

/-- For every `a : L`, the evaluation map `x ↦ |a|_x` is measurable by construction. -/
theorem measurable_eval (a : L) :
    Measurable fun x : ParameterSpaceExtension AS L ↦ (ϕ x) a := by
  refine Measurable.of_comap_le ?_
  exact le_trans
    (le_iSup (fun a : L ↦
      MeasurableSpace.comap (fun x : ParameterSpaceExtension AS L ↦ (ϕ x) a) inferInstance) a)
    le_sup_right

/-- For every `a : L`, the logarithmic evaluation map `x ↦ log |a|_x` is measurable. -/
theorem measurable_log (a : L) :
    Measurable fun x : ParameterSpaceExtension AS L ↦ Real.log ((ϕ x) a) :=
  (measurable_eval AS L a).log

/-- Restrict an extension place on `L` to a finite or algebraic intermediate field of `L/K`. -/
def restrict (x : ParameterSpaceExtension AS L) (F : IntermediateField K L) :
    ParameterSpaceExtension AS F where
  base := x.base
  abv := x.abv.restriction F
  restrict_eq := by
    ext a
    change x.abv (algebraMap F L (algebraMap K F a)) = (AS.ϕ x.base) a
    rw [← IsScalarTower.algebraMap_apply K F L a]
    change (x.abv.restriction K) a = (AS.ϕ x.base) a
    rw [x.restrict_eq]

/-- Restrict an extension place along an inclusion of intermediate fields. This is the map
`proj_{K₂/K₁} : Ω_{K₂} → Ω_{K₁}` in §3.4.2 when `K₁ ⊆ K₂`. -/
def restrictOfLE {F G : IntermediateField K L} (hFG : F ≤ G)
    (x : ParameterSpaceExtension AS G) : ParameterSpaceExtension AS F where
  base := x.base
  abv := x.abv.pullback (IntermediateField.inclusion hFG).toRingHom
  restrict_eq := by
    ext a
    have hmap :
        (IntermediateField.inclusion hFG (algebraMap K F a) : G) = algebraMap K G a := by
      apply Subtype.ext
      simp
    change x.abv ((IntermediateField.inclusion hFG) (algebraMap K F a)) = (AS.ϕ x.base) a
    rw [hmap]
    change (x.abv.restriction K) a = (AS.ϕ x.base) a
    rw [x.restrict_eq]

/-- Restriction of places to an intermediate field is measurable. -/
theorem measurable_restrict (F : IntermediateField K L) :
    Measurable fun x : ParameterSpaceExtension AS L ↦ restrict AS L x F := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap _ (_ ⊔ ⨆ a : F, _) ≤ _
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
  refine sup_le ?_ (iSup_le fun a ↦ ?_)
  · rw [MeasurableSpace.comap_comp]
    exact (measurable_proj AS L).comap_le
  · rw [MeasurableSpace.comap_comp]
    exact (measurable_eval AS L (a : L)).comap_le

/-- Restriction along an inclusion of intermediate fields is measurable. -/
theorem measurable_restrictOfLE {F G : IntermediateField K L} (hFG : F ≤ G) :
    Measurable (restrictOfLE AS L hFG) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap _ (_ ⊔ ⨆ a : F, _) ≤ _
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
  refine sup_le ?_ (iSup_le fun a ↦ ?_)
  · rw [MeasurableSpace.comap_comp]
    exact (measurable_proj AS G).comap_le
  · rw [MeasurableSpace.comap_comp]
    exact (measurable_eval AS G (IntermediateField.inclusion hFG a)).comap_le

/-- Restriction to a smaller intermediate stage factors through any larger one. This is the
compatibility `π_{L/K₁} = π_{K₂/K₁} ∘ π_{L/K₂}` of §3.4.2, formula (3.16). -/
theorem restrictOfLE_restrict {F G : IntermediateField K L} (hFG : F ≤ G)
    (x : ParameterSpaceExtension AS L) :
    restrictOfLE AS L hFG (restrict AS L x G) = restrict AS L x F := by
  rfl

end ParameterSpaceExtension

variable (K) in
/-- The power sums of the embeddings of a finite separable extension are traces. -/
theorem sum_pow_embeddings_eq_trace {E : Type*} [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E] (b : E) (N : ℕ) :
    (∑ σ : E →ₐ[K] AlgebraicClosure K, (σ b) ^ N) =
      algebraMap K (AlgebraicClosure K) (Algebra.trace K E (b ^ N)) := by
  simpa only [map_pow] using (trace_eq_sum_embeddings (AlgebraicClosure K)
    (x := b ^ N)).symm

variable (K) in
/-- Every embedding of a simple subextension of an algebraic closure extends to an
automorphism of the algebraic closure. -/
theorem adjoin_restrict_aut_surjective (c : AlgebraicClosure K) :
    Function.Surjective (fun τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K ↦
      τ.toAlgHom.comp (IntermediateField.adjoin K {c}).val) := by
  intro σ
  let f := σ.liftNormal (AlgebraicClosure K)
  let e := AlgEquiv.ofBijective f (AlgHom.normal_bijective K (AlgebraicClosure K)
    (AlgebraicClosure K) f)
  refine ⟨e, ?_⟩
  ext x
  exact σ.liftNormal_commutes (AlgebraicClosure K) x

variable (K) in
/-- Embeddings of a simple extension are determined by the image of its generator. -/
theorem adjoin_embeddings_gen_injective (c : AlgebraicClosure K) :
    Function.Injective (fun σ : (IntermediateField.adjoin K {c}) →ₐ[K] AlgebraicClosure K ↦
      σ (IntermediateField.AdjoinSimple.gen K c)) := by
  intro σ τ h
  apply (IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral c)).algHom_ext
  simpa only [IntermediateField.adjoin.powerBasis_gen] using h

/-- Chen--Moriwaki, Lemma 3.3.5(2): given any choice of extensions of the base absolute
values to an algebraic closure of `K`, the maximal absolute value on the Galois orbit of a
separable element is a measurable function of the base point. -/
theorem measurable_iSup_abv_aut (s : AS.Ω → ParameterSpaceExtension AS (AlgebraicClosure K))
    (hs : ∀ ω, (s ω).proj = ω) {c : AlgebraicClosure K} (hc : IsSeparable K c) :
    Measurable fun ω : AS.Ω ↦
      ⨆ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, (s ω).ϕ (τ c) := by
 classical
  let E := IntermediateField.adjoin K {c}
  let : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hc.isIntegral
  let : Algebra.IsSeparable K E :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K (AlgebraicClosure K)).mpr hc
  let e : Fin (Module.finrank K E) ≃ (E →ₐ[K] AlgebraicClosure K) :=
    (Fintype.equivFinOfCardEq (AlgHom.card K E (AlgebraicClosure K))).symm
  let b : E := IntermediateField.AdjoinSimple.gen K c
  let α (i : Fin (Module.finrank K E)) := e i b
  have hα : Function.Injective α := (adjoin_embeddings_gen_injective K c).comp e.injective
  have hd : 1 ≤ Module.finrank K E := Module.finrank_pos
  have hsum (N : ℕ) : (∑ i, α i ^ N) =
      algebraMap K (AlgebraicClosure K) (Algebra.trace K E (b ^ N)) := by
    calc
      _ = ∑ σ : E →ₐ[K] AlgebraicClosure K, σ b ^ N :=
        Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
      _ = _ := sum_pow_embeddings_eq_trace K b N
  have hrest (ω : AS.Ω) (a : K) :
      (s ω).ϕ (algebraMap K (AlgebraicClosure K) a) = AS.ϕ ω a := by
    have h := (ParameterSpaceExtension.ϕ_restriction AS (AlgebraicClosure K) (s ω)).trans
      (congrArg AS.ϕ (hs ω))
    exact congrArg (fun v : AbsoluteValue K ℝ ↦ v a) h
  have heq (ω : AS.Ω) :
      (⨆ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, (s ω).ϕ (τ c)) =
        Filter.limsup (fun N : ℕ ↦
          (AS.ϕ ω (Algebra.trace K E (b ^ N))) ^ ((N : ℝ)⁻¹)) Filter.atTop := by
    calc
      _ = ⨆ σ : E →ₐ[K] AlgebraicClosure K, (s ω).ϕ (σ b) :=
        (adjoin_restrict_aut_surjective K c).iSup_comp _
      _ = ⨆ i, (s ω).ϕ (α i) := e.iSup_comp.symm
      _ = _ := by
        rw [(s ω).ϕ.iSup_eq_limsup_sum_pow_rpow hd hα]
        simp_rw [hsum, hrest]
  simp_rw [heq]
  apply Measurable.limsup
  intro N
  apply Measurable.pow_const
  let a := Algebra.trace K E (b ^ N)
  change Measurable fun ω ↦ AS.ϕ ω a
  by_cases ha : a = 0
  · simp only [ha, map_zero]
    exact measurable_const
  · have heval : (fun ω ↦ AS.ϕ ω a) = fun ω ↦ Real.exp (Real.log (AS.ϕ ω a)) := by
      funext ω
      exact (Real.exp_log ((AS.ϕ ω).pos ha)).symm
    rw [heval]
    exact (AS.measurable_log a ha).exp

/-- The filtered indexing type `E_{L/K}` of finite subextensions of an algebraic extension
`L/K`. -/
structure FiniteIntermediateField (K : Type u) [Field K] (L : Type w) [Field L]
    [Algebra K L] extends IntermediateField K L where
  finite_dimensional : FiniteDimensional K toIntermediateField

attribute [instance] FiniteIntermediateField.finite_dimensional

instance instCoeFiniteIntermediateFieldIntermediateField :
    Coe (FiniteIntermediateField K L) (IntermediateField K L) := ⟨fun F ↦ F.1⟩
attribute [coe] FiniteIntermediateField.toIntermediateField

instance instCoeSortFiniteIntermediateFieldType :
    CoeSort (FiniteIntermediateField K L) (Type w) := ⟨fun F ↦ F.1⟩

namespace FiniteIntermediateField

variable {K : Type u} [Field K] {L : Type w} [Field L] [Algebra K L]

/-- The trivial finite subextension `K/K`, as an element of `E_{L/K}`. -/
def bot : FiniteIntermediateField K L :=
  ⟨⊥, inferInstance⟩

/-- The compositum of two finite subextensions, giving the filtered upper bound in `E_{L/K}`. -/
def sup (F G : FiniteIntermediateField K L) : FiniteIntermediateField K L :=
  ⟨F.1 ⊔ G.1, by
    have hF : FiniteDimensional K F.1 := F.2
    have hG : FiniteDimensional K G.1 := G.2
    infer_instance⟩

/-- The left finite subextension is contained in its compositum with another one. -/
theorem left_le_sup (F G : FiniteIntermediateField K L) : F.1 ≤ (sup F G).1 :=
  le_sup_left

/-- The right finite subextension is contained in its compositum with another one. -/
theorem right_le_sup (F G : FiniteIntermediateField K L) : G.1 ≤ (sup F G).1 :=
  le_sup_right

end FiniteIntermediateField

/-- The fibre `M_{L,ω}` of extension absolute values over a base parameter `ω : Ω_K`. -/
abbrev ExtensionFiber (ω : AS.Ω) :=
  {x : ParameterSpaceExtension AS L // x.proj = ω}

namespace ParameterSpaceExtension

/-- Evaluation maps distinguish two different absolute values in the same fibre. -/
instance extensionFiber_separatesPoints (ω : AS.Ω) :
    MeasurableSpace.SeparatesPoints (ExtensionFiber AS L ω) := by
  rw [MeasurableSpace.separatesPoints_iff]
  intro x y h
  apply Subtype.ext
  apply ext AS L (x.property.trans y.property.symm)
  ext a
  have hmeas : Measurable fun z : ExtensionFiber AS L ω ↦ z.val.ϕ a :=
    (measurable_eval AS L a).comp measurable_subtype_coe
  exact ((h {z | z.val.ϕ a = x.val.ϕ a}
    (hmeas (measurableSet_singleton _))).mp rfl).symm

variable [FiniteDimensional K L] [_s : Algebra.IsSeparable K L]

/-- The concrete fibre weight `[L_x : K_ω] / [L : K]` from (3.2). -/
noncomputable def fibreWeight (ω : AS.Ω) (x : ExtensionFiber AS L ω) : ℝ≥0∞ :=
  (localDegree x.1.ϕ K : ℝ≥0∞) / (Module.finrank K L : ℝ≥0∞)

/-- The concrete fibre weights from (3.2) have total mass one. -/
theorem tsum_fibreWeight (ω : AS.Ω) :
    ∑' x : ExtensionFiber AS L ω, fibreWeight AS L ω x = 1 := by
  classical
  let E := {w : AbsoluteValue L ℝ // w.restriction K = AS.ϕ ω}
  let e : ExtensionFiber AS L ω ≃ E := {
    toFun x := ⟨x.val.ϕ, x.val.restrict_eq.trans (congrArg AS.ϕ x.property)⟩
    invFun w := ⟨⟨ω, w.val, w.property⟩, rfl⟩
    left_inv x := by
      apply Subtype.ext
      exact ParameterSpaceExtension.ext AS L x.property.symm rfl
    right_inv _ := rfl }
  let : Fintype E := (AbsoluteValue.finite_extensions (L := L) (AS.ϕ ω)).fintype
  let : Fintype (ExtensionFiber AS L ω) := Fintype.ofEquiv E e.symm
  rw [tsum_fintype]
  change (∑ x : ExtensionFiber AS L ω,
    (x.val.ϕ.localDegree K : ℝ≥0∞) / (Module.finrank K L : ℝ≥0∞)) = 1
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum]
  have hs : ∑ x : ExtensionFiber AS L ω, x.val.ϕ.localDegree K = Module.finrank K L :=
    (e.sum_comp (fun w ↦ w.val.localDegree K)).trans (AbsoluteValue.sum_localDegree (AS.ϕ ω))
  rw [hs, ← div_eq_mul_inv]
  exact ENNReal.div_self (by exact_mod_cast (ne_of_gt (Module.finrank_pos (R := K) (M := L))))
    (by simp)

/-- The finite fibre probability measure `P_{L,ω}` of (3.2), defined from its point masses. -/
noncomputable def fibreProbabilityMeasure (ω : AS.Ω) :
    Measure (ExtensionFiber AS L ω) :=
  Measure.sum fun x : ExtensionFiber AS L ω ↦ fibreWeight AS L ω x • Measure.dirac x

/-- The local-degree normalization makes every fibre measure a probability measure. -/
instance isProbabilityMeasure_fibreProbabilityMeasure (ω : AS.Ω) :
    IsProbabilityMeasure (fibreProbabilityMeasure AS L ω) where
  measure_univ := by
    simpa [fibreProbabilityMeasure, Measure.sum_apply] using tsum_fibreWeight AS L ω

/-- The fibre integration operator `I_{L/K}` on real-valued functions from §3.3.1. -/
noncomputable def fibreIntegral (f : ParameterSpaceExtension AS L → ℝ) : AS.Ω → ℝ :=
  fun ω ↦ ∫ x : ExtensionFiber AS L ω, f x.1 ∂fibreProbabilityMeasure AS L ω

/-- The nonnegative version of the fibre integration operator, used in Definition 3.3.6. -/
noncomputable def fibreLIntegral (f : ParameterSpaceExtension AS L → ℝ≥0∞) : AS.Ω → ℝ≥0∞ :=
  fun ω ↦ ∫⁻ x : ExtensionFiber AS L ω, f x.1 ∂fibreProbabilityMeasure AS L ω

omit _s in
/-- The fibres of the projection of a finite extension are finite sets (§3.3, p. 178: a base
absolute value has at most `[L : K]` extensions to `L`). -/
theorem finite_extensionFiber (ω : AS.Ω) : Finite (ExtensionFiber AS L ω) := by
  have : Finite {w : AbsoluteValue L ℝ // w.restriction K = AS.ϕ ω} :=
    Set.finite_coe_iff.mpr (AbsoluteValue.finite_extensions (L := L) (AS.ϕ ω))
  let f : ExtensionFiber AS L ω → {w : AbsoluteValue L ℝ // w.restriction K = AS.ϕ ω} :=
    fun x ↦ ⟨x.val.abv, x.val.restrict_eq.trans (congrArg AS.ϕ x.property)⟩
  apply Finite.of_injective f
  intro x y h
  apply Subtype.ext
  exact ext AS L (x.property.trans y.property.symm) (congrArg Subtype.val h)

/-- Formula (3.3): the fibre integration operator sends the constant function `1` on `Ω_L`
to the constant function `1` on `Ω_K` (§3.3.1). -/
theorem fibreIntegral_one : fibreIntegral AS L (fun _ ↦ 1) = fun _ ↦ 1 := by
  funext ω
  simp [fibreIntegral]

/-- Every real function on a finite fibre is integrable for its probability measure. -/
theorem integrable_fibre (ω : AS.Ω) (f : ExtensionFiber AS L ω → ℝ) :
    Integrable f (fibreProbabilityMeasure AS L ω) := by
  let := finite_extensionFiber AS L ω
  exact Integrable.of_finite

/-- The fibre integration operator is additive (§3.3.1). -/
theorem fibreIntegral_add (f g : ParameterSpaceExtension AS L → ℝ) :
    fibreIntegral AS L (f + g) = fibreIntegral AS L f + fibreIntegral AS L g := by
  funext ω
  exact integral_add (integrable_fibre AS L ω _) (integrable_fibre AS L ω _)

set_option linter.unusedSectionVars false in
/-- The fibre integration operator is `ℝ`-homogeneous (§3.3.1). -/
theorem fibreIntegral_smul (c : ℝ) (f : ParameterSpaceExtension AS L → ℝ) :
    fibreIntegral AS L (c • f) = c • fibreIntegral AS L f := by
  funext ω
  exact integral_smul c _

set_option linter.unusedSectionVars false in
/-- Chen--Moriwaki, Proposition 3.3.1: fibre integration is linear over functions pulled back
from the base: `I_{K'/K}(φ̄ f) = φ I_{K'/K}(f)` for `φ̄ = φ ∘ π_{K'/K}`. -/
theorem fibreIntegral_comp_proj_mul (φ : AS.Ω → ℝ) (f : ParameterSpaceExtension AS L → ℝ) :
    fibreIntegral AS L (fun x ↦ φ (proj x) * f x) = fun ω ↦ φ ω * fibreIntegral AS L f ω := by
  funext ω
  have hproj : ∀ x : ExtensionFiber AS L ω, x.val.proj = ω := fun x ↦ x.property
  change (∫ x : ExtensionFiber AS L ω, φ x.val.proj * f x.val
    ∂fibreProbabilityMeasure AS L ω) = _
  simp_rw [hproj]
  exact integral_const_mul (φ ω) _

/-- Chen--Moriwaki, Corollary 3.3.3: fibre integration retracts the pullback along the
projection: `I_{K'/K}(φ ∘ π_{K'/K}) = φ`. -/
theorem fibreIntegral_comp_proj (φ : AS.Ω → ℝ) :
    fibreIntegral AS L (fun x ↦ φ (proj x)) = φ := by
  funext ω
  change (∫ x : ExtensionFiber AS L ω, φ x.val.proj
    ∂fibreProbabilityMeasure AS L ω) = φ ω
  simp only [show ∀ x : ExtensionFiber AS L ω, x.val.proj = ω from fun x ↦ x.property]
  simp

/-- Chen--Moriwaki, Proposition 3.3.2, formula (3.4): fibre integration is compatible with
successive finite separable extensions `K ⊆ F ⊆ L`: integrating a function pulled back from
the intermediate stage agrees with integrating the function at the intermediate stage. -/
theorem fibreIntegral_comp_restrict (F : IntermediateField K L)
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (f : ParameterSpaceExtension AS F → ℝ) :
    fibreIntegral AS L (fun x ↦ f (restrict AS L x F)) = fibreIntegral AS F f := by
  sorry

/-- Chen--Moriwaki, Theorem 3.3.4: for finite separable `L/K`, the fibre integration operator
sends measurable real-valued functions on `Ω_L` to measurable real-valued functions on `Ω_K`. -/
theorem measurable_fibreIntegral {f : ParameterSpaceExtension AS L → ℝ} (hf : Measurable f) :
    Measurable (fibreIntegral AS L f) := by
  sorry

/-- Nonnegative measurable functions have measurable fibre integrals. -/
theorem measurable_fibreLIntegral {f : ParameterSpaceExtension AS L → ℝ≥0∞}
    (hf : Measurable f) : Measurable (fibreLIntegral AS L f) := by
  refine Measurable.ennreal_induction
    (motive := fun f ↦ Measurable (fibreLIntegral AS L f)) ?_ ?_ ?_ hf
  · intro c s hs
    have hm := measurable_fibreIntegral AS L (measurable_const.indicator hs :
      Measurable (s.indicator fun _ : ParameterSpaceExtension AS L ↦ (1 : ℝ)))
    convert hm.ennreal_ofReal.const_mul c using 1
    funext ω
    simp only [fibreLIntegral, fibreIntegral, ← Set.indicator_comp_right, Function.comp_def]
    rw [lintegral_indicator_const (hs.preimage measurable_subtype_coe),
      integral_indicator_const _ (hs.preimage measurable_subtype_coe)]
    simp [measureReal_def]
  · intro f g _ hf hg ihf ihg
    convert ihf.add ihg using 1
    funext ω
    exact lintegral_add_left (hf.comp measurable_subtype_coe) _
  · intro f hf hmono ih
    convert Measurable.iSup ih using 1
    funext ω
    exact lintegral_iSup (fun n ↦ (hf n).comp measurable_subtype_coe)
      (fun n m h x ↦ hmono h x.val)

/-- Chen--Moriwaki, Definition 3.3.6: the measure `ν_L` on `Ω_L` defined by
`ν_L(A) = ∫_{Ω_K} I_{L/K}(1_A) dν_K`. -/
noncomputable def inducedMeasure : Measure (ParameterSpaceExtension AS L) :=
  Measure.ofMeasurable
    (fun A _hA ↦ ∫⁻ ω, fibreLIntegral AS L (Set.indicator A fun _ ↦ (1 : ℝ≥0∞)) ω ∂AS.v)
    (by simp [fibreLIntegral])
    (by
      intro A hA hdisj
      have hind (s : Set (ParameterSpaceExtension AS L)) (hs : MeasurableSet s) (ω : AS.Ω) :
          fibreLIntegral AS L (s.indicator fun _ ↦ 1) ω =
            fibreProbabilityMeasure AS L ω (Subtype.val ⁻¹' s) := by
        simp only [fibreLIntegral, ← Set.indicator_comp_right, Function.comp_def]
        rw [lintegral_indicator_const (hs.preimage measurable_subtype_coe)]
        simp
      have hpoint (ω : AS.Ω) :
          fibreLIntegral AS L ((⋃ n, A n).indicator fun _ ↦ 1) ω =
            ∑' n, fibreLIntegral AS L ((A n).indicator fun _ ↦ 1) ω := by
        rw [hind _ (MeasurableSet.iUnion hA), Set.preimage_iUnion,
          measure_iUnion (fun i j hij ↦ (hdisj hij).preimage Subtype.val)
            (fun n ↦ (hA n).preimage measurable_subtype_coe)]
        congr 1
        funext n
        exact (hind _ (hA n) ω).symm
      simp_rw [hpoint]
      exact lintegral_tsum (fun n ↦
        (measurable_fibreLIntegral AS L (measurable_const.indicator (hA n))).aemeasurable))

/-- The defining formula of Definition 3.3.6. -/
theorem inducedMeasure_apply {A : Set (ParameterSpaceExtension AS L)} (hA : MeasurableSet A) :
    inducedMeasure AS L A =
      ∫⁻ ω, fibreLIntegral AS L (Set.indicator A fun _ ↦ (1 : ℝ≥0∞)) ω ∂AS.v :=
  Measure.ofMeasurable_apply A hA

/-- Chen--Moriwaki, Theorem 3.3.7(1), formula (3.7): the induced measure integrates
nonnegative measurable functions through the fibre integration operator. -/
theorem lintegral_inducedMeasure {f : ParameterSpaceExtension AS L → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x, f x ∂inducedMeasure AS L = ∫⁻ ω, fibreLIntegral AS L f ω ∂AS.v := by
  refine Measurable.ennreal_induction
    (motive := fun f ↦ (∫⁻ x, f x ∂inducedMeasure AS L) =
      ∫⁻ ω, fibreLIntegral AS L f ω ∂AS.v) ?_ ?_ ?_ hf
  · intro c s hs
    rw [lintegral_indicator_const hs, inducedMeasure_apply AS L hs,
      ← lintegral_const_mul c (measurable_fibreLIntegral AS L (measurable_const.indicator hs))]
    apply lintegral_congr
    intro ω
    simp only [fibreLIntegral, ← Set.indicator_comp_right, Function.comp_def]
    rw [lintegral_indicator_const (hs.preimage measurable_subtype_coe),
      lintegral_indicator_const (hs.preimage measurable_subtype_coe), one_mul]
  · intro f g _ hf hg ihf ihg
    simp only [Pi.add_apply]
    rw [lintegral_add_left hf, ihf, ihg,
      ← lintegral_add_left (measurable_fibreLIntegral AS L hf)]
    apply lintegral_congr
    intro ω
    exact (lintegral_add_left (hf.comp measurable_subtype_coe) _).symm
  · intro f hf hmono ih
    rw [lintegral_iSup hf hmono]
    simp_rw [ih]
    rw [← lintegral_iSup (fun n ↦ measurable_fibreLIntegral AS L (hf n))
      (fun n m h ω ↦ lintegral_mono (fun x ↦ hmono h x.val))]
    apply lintegral_congr
    intro ω
    exact (lintegral_iSup (fun n ↦ (hf n).comp measurable_subtype_coe)
      (fun n m h x ↦ hmono h x.val)).symm

/-- Chen--Moriwaki, Theorem 3.3.7(2): a measurable function is integrable for the induced
measure if and only if the fibre integral of its absolute value is integrable on the base. -/
theorem integrable_inducedMeasure_iff {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Measurable f) :
    Integrable f (inducedMeasure AS L) ↔
      Integrable (fibreIntegral AS L fun x ↦ |f x|) AS.v := by
  have habs : Measurable (fun x ↦ |f x|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hnonneg (ω : AS.Ω) : 0 ≤ fibreIntegral AS L (fun x ↦ |f x|) ω :=
    integral_nonneg (fun x ↦ abs_nonneg (f x.val))
  have heq (ω : AS.Ω) :
      ENNReal.ofReal (fibreIntegral AS L (fun x ↦ |f x|) ω) =
        fibreLIntegral AS L (fun x ↦ ENNReal.ofReal |f x|) ω :=
    ofReal_integral_eq_lintegral_ofReal (integrable_fibre AS L ω _)
      (Filter.Eventually.of_forall fun x ↦ abs_nonneg (f x.val))
  rw [← integrable_norm_iff hf.aestronglyMeasurable]
  simp only [Real.norm_eq_abs]
  rw [← lintegral_ofReal_ne_top_iff_integrable habs.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ abs_nonneg (f x)),
    lintegral_inducedMeasure AS L habs.ennreal_ofReal,
    ← lintegral_ofReal_ne_top_iff_integrable
      (measurable_fibreIntegral AS L habs).aestronglyMeasurable
      (Filter.Eventually.of_forall hnonneg)]
  simp_rw [heq]

/-- A globally almost everywhere property holds almost everywhere on almost every fibre. -/
theorem ae_ae_fibre_of_ae {p : ParameterSpaceExtension AS L → Prop}
    (hp : ∀ᵐ x ∂inducedMeasure AS L, p x) :
    ∀ᵐ ω ∂AS.v, ∀ᵐ x ∂fibreProbabilityMeasure AS L ω, p x.val := by
  obtain ⟨N, hsub, hN, hzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
  rw [inducedMeasure_apply AS L hN] at hzero
  have h := (lintegral_eq_zero_iff
    (measurable_fibreLIntegral AS L (measurable_const.indicator hN))).mp hzero
  filter_upwards [h] with ω hω
  apply ae_iff.mpr
  apply measure_mono_null (t := Subtype.val ⁻¹' N) (fun x hx ↦ hsub hx)
  change fibreProbabilityMeasure AS L ω (Subtype.val ⁻¹' N) = 0
  simpa only [fibreLIntegral, ← Set.indicator_comp_right, Function.comp_def,
    lintegral_indicator_const (hN.preimage measurable_subtype_coe), one_mul,
    Pi.zero_apply] using hω

/-- Chen--Moriwaki, Theorem 3.3.7(2): formula (3.7) also holds for integrable real-valued
functions. -/
theorem integral_inducedMeasure {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Integrable f (inducedMeasure AS L)) :
    ∫ x, f x ∂inducedMeasure AS L = ∫ ω, fibreIntegral AS L f ω ∂AS.v := by
  have hnonnegative {f : ParameterSpaceExtension AS L → ℝ}
      (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x) :
      ∫ x, f x ∂inducedMeasure AS L = ∫ ω, fibreIntegral AS L f ω ∂AS.v := by
    have heq (ω : AS.Ω) :
        ENNReal.ofReal (fibreIntegral AS L f ω) =
          fibreLIntegral AS L (fun x ↦ ENNReal.ofReal (f x)) ω :=
      ofReal_integral_eq_lintegral_ofReal (integrable_fibre AS L ω _)
        (Filter.Eventually.of_forall fun x ↦ hpos x.val)
    have hnonneg (ω : AS.Ω) : 0 ≤ fibreIntegral AS L f ω :=
      integral_nonneg (fun x ↦ hpos x.val)
    rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall hpos) hf.aestronglyMeasurable,
      lintegral_inducedMeasure AS L hf.ennreal_ofReal,
      integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall hnonneg)
        (measurable_fibreIntegral AS L hf).aestronglyMeasurable]
    simp_rw [heq]
  have hmeasurable {f : ParameterSpaceExtension AS L → ℝ}
      (hf : Integrable f (inducedMeasure AS L)) (hfm : Measurable f) :
      ∫ x, f x ∂inducedMeasure AS L = ∫ ω, fibreIntegral AS L f ω ∂AS.v := by
    let p := fun x ↦ max (f x) 0
    let n := fun x ↦ max (-f x) 0
    have hp : Measurable p := hfm.max measurable_const
    have hn : Measurable n := hfm.neg.max measurable_const
    have hip : Integrable p (inducedMeasure AS L) := hf.pos_part
    have hin : Integrable n (inducedMeasure AS L) := hf.neg.pos_part
    have hbp : Integrable (fibreIntegral AS L p) AS.v := by
      have h := (integrable_inducedMeasure_iff AS L hp).mp hip
      simpa only [p, abs_of_nonneg (le_max_right (f _) (0 : ℝ))] using h
    have hbn : Integrable (fibreIntegral AS L n) AS.v := by
      have h := (integrable_inducedMeasure_iff AS L hn).mp hin
      simpa only [n, abs_of_nonneg (le_max_right (-f _) (0 : ℝ))] using h
    have hfsub : f = p - n := by
      funext x
      dsimp [p, n]
      grind
    have hsub : fibreIntegral AS L f =
        fibreIntegral AS L p - fibreIntegral AS L n := by
      funext ω
      rw [hfsub]
      exact integral_sub (integrable_fibre AS L ω _) (integrable_fibre AS L ω _)
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [integral_sub hbp hbn, ← hnonnegative hp (fun _ ↦ le_max_right _ _),
      ← hnonnegative hn (fun _ ↦ le_max_right _ _), hfsub]
    simpa only [Pi.sub_apply] using integral_sub hip hin
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[inducedMeasure AS L] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : Integrable g (inducedMeasure AS L) := hf.congr hfg
  have hgm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfib : fibreIntegral AS L f =ᵐ[AS.v] fibreIntegral AS L g := by
    filter_upwards [ae_ae_fibre_of_ae AS L hfg] with ω hω
    exact integral_congr_ae hω
  exact (integral_congr_ae hfg).trans
    ((hmeasurable hg hgm).trans (integral_congr_ae hfib).symm)

/-- The projection sends the induced measure to the base measure. -/
theorem map_inducedMeasure_proj :
    Measure.map (ParameterSpaceExtension.proj (AS := AS) (L := L)) (inducedMeasure AS L) =
      AS.v := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_proj AS L) hs, inducedMeasure_apply AS L
    (hs.preimage (measurable_proj AS L))]
  have hconst (ω : AS.Ω) :
      fibreLIntegral AS L ((proj ⁻¹' s).indicator fun _ ↦ 1) ω =
        s.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω := by
    change (∫⁻ x : ExtensionFiber AS L ω,
      (proj ⁻¹' s).indicator (fun _ ↦ (1 : ℝ≥0∞)) x.val
        ∂fibreProbabilityMeasure AS L ω) = _
    classical
    simp only [Set.indicator, Set.mem_preimage]
    simp_rw [show ∀ x : ExtensionFiber AS L ω, x.val.proj = ω from fun x ↦ x.property]
    simp
  simp_rw [hconst]
  rw [lintegral_indicator_const hs, one_mul]

/-- Chen--Moriwaki, Theorem 3.3.7(3), formula (3.8): integrating a pullback from the base
against the induced measure is integrating against the base measure. -/
theorem integral_comp_proj_inducedMeasure {φ : AS.Ω → ℝ} (hφ : Integrable φ AS.v) :
    ∫ x, φ (proj x) ∂inducedMeasure AS L = ∫ ω, φ ω ∂AS.v := by
  have hm : AEStronglyMeasurable φ
      (Measure.map (proj (AS := AS) (L := L)) (inducedMeasure AS L)) := by
    rw [map_inducedMeasure_proj AS L]
    exact hφ.aestronglyMeasurable
  have h := integral_map (measurable_proj AS L).aemeasurable hm
  rw [map_inducedMeasure_proj AS L] at h
  exact h.symm

/-- Chen--Moriwaki, Theorem 3.3.7(5), formula (3.9): the logarithmic integral against the
induced measure computes the logarithm of the norm form:
`[K' : K] ∫ ln |b|_x dν_{K'} = ∫ ln |N_{K'/K}(b)|_ω dν_K`. -/
theorem finrank_mul_integral_log_inducedMeasure (b : L) (hb : b ≠ 0) :
    (Module.finrank K L : ℝ) * ∫ x, Real.log (ϕ x b) ∂inducedMeasure AS L =
      ∫ ω, Real.log (AS.ϕ ω (Algebra.norm K b)) ∂AS.v := by
  sorry

/-- Chen--Moriwaki, Theorem 3.3.7(4): logarithmic evaluations are integrable for the measure
defined in Definition 3.3.6. -/
theorem integrable_log_inducedMeasure (a : L) (ha : a ≠ 0) :
    Integrable
      (fun x : ParameterSpaceExtension AS L ↦ Real.log ((ParameterSpaceExtension.ϕ x) a))
      (inducedMeasure AS L) := by
  sorry

/-- The finite separable extension adelic structure on `L`, using the measure defined by
Definition 3.3.6. -/
noncomputable def _root_.ArakelovGeometry.AdelicStructure.finiteSeparableExtension :
    AdelicStructure L where
  Ω := ParameterSpaceExtension AS L
  A := inferInstance
  v := inducedMeasure AS L
  ϕ := ParameterSpaceExtension.ϕ
  measurable_log := fun a _ha ↦ ParameterSpaceExtension.measurable_log AS L a
  integrable_log := integrable_log_inducedMeasure AS L

/-- Chen--Moriwaki, Theorem 3.3.7(5): the finite separable extension of a proper adelic curve
is proper. -/
theorem isProper_finiteSeparableExtension [AS.toAdelicCurve.IsProper] :
    (AS.finiteSeparableExtension L).toAdelicCurve.IsProper := by
  constructor
  change ∀ a : L, a ≠ 0 → ∫ x, Real.log (ϕ x a) ∂inducedMeasure AS L = 0
  intro a ha
  have hn : Algebra.norm K a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
  have h := finrank_mul_integral_log_inducedMeasure AS L a ha
  have hzero : (∫ ω, Real.log (AS.ϕ ω (Algebra.norm K a)) ∂AS.v) = 0 :=
    AdelicCurve.IsProper.product_formula (C := AS.toAdelicCurve) (Algebra.norm K a) hn
  rw [hzero] at h
  exact (mul_eq_zero.mp h).resolve_left
    (by exact_mod_cast (Module.finrank_pos (R := K) (M := L)).ne')

end ParameterSpaceExtension

/-- The parameter space used for the finite extension `S ⊗_K L` in Definition 3.4.1.
It is the parameter space of the finite separable extension `K'/K`, where `K'` is the separable
part of `L/K`; the paper then identifies `M_{K'}` and `M_L` by the purely inseparable
extension formula. -/
abbrev ParameterSpaceFinExtension [FiniteDimensional K L] :=
  ParameterSpaceExtension AS (separableClosure K L)

namespace ParameterSpaceFinExtension

variable [FiniteDimensional K L]

variable (K) {L} in
/-- If `q = [L : K']` is the inseparable degree, then `a^q ∈ K'`.
This is the algebraic input used in formula (3.13). -/
theorem pow_finInsepDegree_mem_separableClosure (a : L) :
    a ^ Field.finInsepDegree K L ∈ separableClosure K L := by
  obtain ⟨p, hp⟩ := ExpChar.exists (separableClosure K L)
  obtain ⟨n, b, hpoly⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C
    (separableClosure K L) p a
  have hpow : a ^ p ^ n = (b : L) := by
    have h := minpoly.aeval (separableClosure K L) a
    simpa [hpoly, sub_eq_zero] using h
  have hdvd : p ^ n ∣ Field.finInsepDegree K L := by
    simpa [Field.finInsepDegree, hpoly] using
      (minpoly.degree_dvd (Algebra.IsIntegral.isIntegral (R := separableClosure K L) a))
  obtain ⟨m, hm⟩ := hdvd
  rw [hm, pow_mul, hpow]
  exact pow_mem b.property m

variable {L} in
/-- The formula (3.13) extending an absolute value from the separable part `K'` to the finite
extension `L`: `|a| = |a^q|^(1/q)`, where `q = [L : K']`. -/
noncomputable def extendAbsoluteValue
    (v : AbsoluteValue (separableClosure K L) ℝ) : AbsoluteValue L ℝ where
  toFun a :=
    v ⟨a ^ Field.finInsepDegree K L,
        pow_finInsepDegree_mem_separableClosure K a⟩ ^
      ((Field.finInsepDegree K L : ℝ)⁻¹)
  map_mul' a b := by
    have hmul :
        (⟨(a * b) ^ Field.finInsepDegree K L,
          pow_finInsepDegree_mem_separableClosure K (a * b)⟩ : separableClosure K L) =
          ⟨a ^ Field.finInsepDegree K L, pow_finInsepDegree_mem_separableClosure K a⟩ *
            ⟨b ^ Field.finInsepDegree K L, pow_finInsepDegree_mem_separableClosure K b⟩ := by
      ext
      exact mul_pow a b _
    rw [hmul, map_mul, Real.mul_rpow (v.nonneg _) (v.nonneg _)]
  nonneg' a := by
    exact Real.rpow_nonneg (v.nonneg _) _
  eq_zero' a := by
    have hq : (Field.finInsepDegree K L : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (NeZero.ne _)
    rw [Real.rpow_eq_zero (v.nonneg _) (inv_ne_zero hq), v.eq_zero]
    simp only [Subtype.ext_iff, ZeroMemClass.coe_zero, pow_eq_zero_iff (NeZero.ne _)]
  add_le' a b := by
    obtain ⟨p, hp⟩ := ExpChar.exists L
    let : ExpChar K p := (algebraMap K L).expChar (algebraMap K L).injective p
    obtain ⟨n, hn⟩ := finInsepDegree_eq_pow K L p
    have hadd :
        (⟨(a + b) ^ Field.finInsepDegree K L,
          pow_finInsepDegree_mem_separableClosure K (a + b)⟩ : separableClosure K L) =
          ⟨a ^ Field.finInsepDegree K L, pow_finInsepDegree_mem_separableClosure K a⟩ +
            ⟨b ^ Field.finInsepDegree K L, pow_finInsepDegree_mem_separableClosure K b⟩ := by
      apply Subtype.ext
      change (a + b) ^ Field.finInsepDegree K L =
        a ^ Field.finInsepDegree K L + b ^ Field.finInsepDegree K L
      rw [hn, add_pow_expChar_pow]
    have hr : 0 ≤ (Field.finInsepDegree K L : ℝ)⁻¹ := by positivity
    have hr₁ : (Field.finInsepDegree K L : ℝ)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Field.finInsepDegree K L))
    rw [hadd]
    exact (Real.rpow_le_rpow (v.nonneg _) (v.add_le _ _) hr).trans
      (Real.rpow_add_le_add_rpow (v.nonneg _) (v.nonneg _) hr hr₁)

/-- Formula (3.13) as a simp-ready evaluation statement. -/
theorem extendAbsoluteValue_apply
    (v : AbsoluteValue (separableClosure K L) ℝ) (a : L) :
    extendAbsoluteValue v a =
      v ⟨a ^ Field.finInsepDegree K L,
          pow_finInsepDegree_mem_separableClosure K a⟩ ^
        ((Field.finInsepDegree K L : ℝ)⁻¹) :=
  rfl

variable {L} in
/-- The inseparable extension agrees with the original absolute value on the separable part. -/
theorem extendAbsoluteValue_coe
    (v : AbsoluteValue (separableClosure K L) ℝ) (b : separableClosure K L) :
    extendAbsoluteValue v (b : L) = v b := by
  rw [extendAbsoluteValue_apply]
  change v (b ^ Field.finInsepDegree K L) ^ (Field.finInsepDegree K L : ℝ)⁻¹ = v b
  rw [map_pow, Real.pow_rpow_inv_natCast (v.nonneg _) (NeZero.ne _)]

variable {L} in
/-- Restricting the inseparable extension recovers the given absolute value. -/
theorem restriction_extendAbsoluteValue
    (v : AbsoluteValue (separableClosure K L) ℝ) :
    (extendAbsoluteValue v).restriction (separableClosure K L) = v := by
  ext b
  exact extendAbsoluteValue_coe v b

/-- An absolute value on a finite extension is recovered uniquely from its separable part. -/
theorem extendAbsoluteValue_restriction (w : AbsoluteValue L ℝ) :
    extendAbsoluteValue (w.restriction (separableClosure K L)) = w := by
  ext a
  rw [extendAbsoluteValue_apply]
  change w (a ^ Field.finInsepDegree K L) ^ (Field.finInsepDegree K L : ℝ)⁻¹ = w a
  rw [map_pow, Real.pow_rpow_inv_natCast (w.nonneg _) (NeZero.ne _)]

/-- The logarithmic form of formula (3.13), giving formula (3.14):
`ln |a| = q⁻¹ ln |a^q|` with `q` the inseparable degree. -/
theorem log_extendAbsoluteValue
    (v : AbsoluteValue (separableClosure K L) ℝ) (a : L) :
    Real.log (extendAbsoluteValue v a) =
      (Field.finInsepDegree K L : ℝ)⁻¹ *
        Real.log (v ⟨a ^ Field.finInsepDegree K L,
          pow_finInsepDegree_mem_separableClosure K a⟩) := by
  by_cases ha : a = 0
  · subst a
    simp [NeZero.ne (Field.finInsepDegree K L), Subtype.ext_iff]
  · rw [extendAbsoluteValue_apply]
    apply Real.log_rpow (v.pos ?_)
    intro h
    exact pow_ne_zero _ ha (congrArg Subtype.val h)

/-- The canonical bijection `M_{K'} ≃ M_L` in Definition 3.4.1, used here as the parameter map
for the finite extension adelic structure. -/
noncomputable def ϕ (x : AS.ParameterSpaceFinExtension L) : AbsoluteValue L ℝ :=
  extendAbsoluteValue (ParameterSpaceExtension.ϕ x)

/-- The measure on the finite extension `S ⊗_K L`: it is the measure already constructed on the
finite separable extension `K'/K`. -/
noncomputable def measure : Measure (ParameterSpaceFinExtension AS L) :=
  ParameterSpaceExtension.inducedMeasure AS (separableClosure K L)

/-- Logarithmic evaluations on a finite, possibly inseparable, extension are measurable by
formula (3.13) and the finite separable construction on `K'`. -/
theorem measurable_log (a : L) :
    Measurable fun x : ParameterSpaceFinExtension AS L ↦
      Real.log ((ϕ AS L x) a) := by
  simp_rw [ϕ, log_extendAbsoluteValue]
  exact (ParameterSpaceExtension.measurable_log AS (separableClosure K L) _).const_mul _

/-- Logarithmic evaluations on a finite, possibly inseparable, extension are integrable by
formula (3.13) and the finite separable construction on `K'`. -/
theorem integrable_log (a : L) (ha : a ≠ 0) :
    Integrable
      (fun x : ParameterSpaceFinExtension AS L ↦
        Real.log ((ϕ AS L x) a))
      (measure AS L) := by
  simp_rw [ϕ, log_extendAbsoluteValue]
  apply (ParameterSpaceExtension.integrable_log_inducedMeasure AS (separableClosure K L)
    _ ?_).const_mul
  intro h
  exact pow_ne_zero _ ha (congrArg Subtype.val h)

/-- Chen--Moriwaki, Definition 3.4.1: the concrete finite extension adelic structure
`S ⊗_K L`, including the inseparable case. -/
noncomputable def _root_.ArakelovGeometry.AdelicStructure.finiteExtension :
    AdelicStructure L where
  Ω := AS.ParameterSpaceFinExtension L
  A := inferInstance
  v := measure AS L
  ϕ := ParameterSpaceFinExtension.ϕ AS L
  measurable_log := fun a _ha ↦ measurable_log AS L a
  integrable_log := integrable_log AS L

variable {AS} in
/-- The finite fibre over `ω`, using the parameter space of Definition 3.4.1. -/
abbrev BaseFiber (ω : AS.Ω) :=
  {x : ParameterSpaceFinExtension AS L // ParameterSpaceExtension.proj x = ω}

/-- The fibre probability measure for the finite extension `L/K`; it is the finite separable
fibre probability measure on the separable part `K'/K`. -/
noncomputable def fibreProbabilityMeasure (ω : AS.Ω) :
    Measure (BaseFiber L ω) :=
  ParameterSpaceExtension.fibreProbabilityMeasure AS (separableClosure K L) ω

/-- The fibre integration operator `I_{L/K}` of a finite (possibly inseparable) extension
`L/K`, computed on the separable part as in Definition 3.4.1 and Remark 3.4.3. -/
noncomputable def fibreIntegral (f : ParameterSpaceFinExtension AS L → ℝ) : AS.Ω → ℝ :=
  fun ω ↦ ∫ x : BaseFiber L ω, f x.1 ∂fibreProbabilityMeasure AS L ω

/-- The remark closing §3.4.1: the σ-algebra of the finite extension parameter space is also
the smallest σ-algebra making the projection to the base and the evaluations of the extended
absolute values at elements of `L` measurable. -/
theorem measurableSpace_eq_comap_sup :
    (ParameterSpaceExtension.instMeasurableSpace AS (separableClosure K L) :
        MeasurableSpace (ParameterSpaceFinExtension AS L)) =
      MeasurableSpace.comap
          (ParameterSpaceExtension.proj (AS := AS) (L := separableClosure K L)) AS.A ⊔
        ⨆ a : L, MeasurableSpace.comap
          (fun x : ParameterSpaceFinExtension AS L ↦ ϕ AS L x a) inferInstance := by
  change _ ⊔ ⨆ b : separableClosure K L, _ = _
  apply le_antisymm
  · refine sup_le le_sup_left (iSup_le fun b ↦ ?_)
    have heval :
        (fun x : ParameterSpaceFinExtension AS L ↦ ParameterSpaceExtension.ϕ x b) =
          (fun x : ParameterSpaceFinExtension AS L ↦ ϕ AS L x (b : L)) := by
      funext x
      exact (extendAbsoluteValue_coe _ b).symm
    rw [heval]
    exact le_trans (le_iSup
      (fun a : L ↦ MeasurableSpace.comap
        (fun x : ParameterSpaceFinExtension AS L ↦ ϕ AS L x a) inferInstance) (b : L))
      le_sup_right
  · refine sup_le le_sup_left (iSup_le fun a ↦ ?_)
    have hmeas : Measurable fun x : ParameterSpaceFinExtension AS L ↦ ϕ AS L x a := by
      simp_rw [ϕ, extendAbsoluteValue_apply]
      exact (ParameterSpaceExtension.measurable_eval AS (separableClosure K L) _).pow_const _
    exact hmeas.comap_le

/-- Formula (3.14): the logarithmic integrals against `ν_{K'}` of `a ∈ L` and of its power
`a^q ∈ K'`, `q = [L : K']` the inseparable degree, are proportional with ratio `q⁻¹`. -/
theorem integral_log_eq_inv_finInsepDegree_mul (a : L) :
    ∫ x, Real.log (ϕ AS L x a) ∂measure AS L =
      (Field.finInsepDegree K L : ℝ)⁻¹ *
        ∫ x, Real.log (ParameterSpaceExtension.ϕ x
          ⟨a ^ Field.finInsepDegree K L,
            pow_finInsepDegree_mem_separableClosure K a⟩) ∂measure AS L := by
  simp_rw [ϕ, log_extendAbsoluteValue]
  exact integral_const_mul _ _

/-- The closing remark of Definition 3.4.1 together with Theorem 3.3.7(5): the finite
(possibly inseparable) extension of a proper adelic curve is proper. -/
theorem isProper_finiteExtension [AS.toAdelicCurve.IsProper] :
    (AS.finiteExtension L).toAdelicCurve.IsProper := by
  let : (AS.finiteSeparableExtension (separableClosure K L)).toAdelicCurve.IsProper :=
    ParameterSpaceExtension.isProper_finiteSeparableExtension AS (separableClosure K L)
  constructor
  change ∀ a : L, a ≠ 0 → ∫ x, Real.log (ϕ AS L x a) ∂measure AS L = 0
  intro a ha
  rw [integral_log_eq_inv_finInsepDegree_mul]
  have hzero := AdelicCurve.IsProper.product_formula
    (C := (AS.finiteSeparableExtension (separableClosure K L)).toAdelicCurve)
    ⟨a ^ Field.finInsepDegree K L, pow_finInsepDegree_mem_separableClosure K a⟩
    (fun h ↦ pow_ne_zero _ ha (congrArg Subtype.val h))
  change ∫ x, Real.log (ParameterSpaceExtension.ϕ x
    ⟨a ^ Field.finInsepDegree K L, pow_finInsepDegree_mem_separableClosure K a⟩)
    ∂measure AS L = 0 at hzero
  rw [hzero, mul_zero]

omit [FiniteDimensional K L] in
/-- The canonical completion maps for the separable part form a scalar tower. -/
private theorem isScalarTower_completion_separableClosure (w : AbsoluteValue L ℝ) :
    let : Algebra (w.restriction K).Completion
        (w.restriction (separableClosure K L)).Completion :=
      algebraCompletion (w.restriction (separableClosure K L)) K
    IsScalarTower (w.restriction K).Completion
      (w.restriction (separableClosure K L)).Completion w.Completion := by
  let E := separableClosure K L
  let B := (w.restriction K).Completion
  let D := (w.restriction E).Completion
  let : Algebra B D := algebraCompletion (w.restriction E) K
  apply IsScalarTower.of_algebraMap_eq
  intro x
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq (isometry_algebraMap_completion w K).continuous
      ((isometry_algebraMap_completion w E).continuous.comp
        (isometry_algebraMap_completion (w.restriction E) K).continuous)
  · intro a
    change (algebraMap (w.restriction K).Completion w.Completion)
          (a : (w.restriction K).Completion) =
        (algebraMap (w.restriction E).Completion w.Completion)
          ((algebraMap ((w.restriction E).restriction K).Completion
            (w.restriction E).Completion)
            ((show WithAbs ((w.restriction E).restriction K) from a) :
              ((w.restriction E).restriction K).Completion))
    rw [algebraMap_completion_def, algebraMap_completion_def,
      algebraMap_completion_def]
    erw [UniformSpace.Completion.mapRingHom_coe,
      UniformSpace.Completion.mapRingHom_coe,
      UniformSpace.Completion.mapRingHom_coe]
    rfl

/-- Chen--Moriwaki, Lemma 3.4.2: for a finite extension `L/K` and an absolute value `w` on
`L`, the completion of the separable closure `K^sc` of `K` in `L` at `w` identifies, inside
the completion `L_w`, with the separable closure of the completion `K_v` (`v = w|_K`). -/
theorem fieldRange_completion_separableClosure (w : AbsoluteValue L ℝ) :
    (algebraMap (w.restriction (separableClosure K L)).Completion w.Completion).fieldRange =
      (separableClosure (w.restriction K).Completion w.Completion).toSubfield := by
  let E := separableClosure K L
  let B := (w.restriction K).Completion
  let D := (w.restriction E).Completion
  let : Algebra B D := algebraCompletion (w.restriction E) K
  have : Algebra.IsSeparable B D := isSeparable_completion (w.restriction E)
  have : IsScalarTower B D w.Completion := isScalarTower_completion_separableClosure L w
  let p := ringExpChar w.Completion
  let : ExpChar E p := (algebraMap E w.Completion).expChar
    (algebraMap E w.Completion).injective p
  let : ExpChar D p := (algebraMap D w.Completion).expChar
    (algebraMap D w.Completion).injective p
  have hcoe (y : L) :
      (WithAbs.toAbs w y : w.Completion) ∈ Subalgebra.perfectClosure D w.Completion p := by
    obtain ⟨n, e, he⟩ := IsPurelyInseparable.pow_mem E p y
    apply Subalgebra.mem_perfectClosure_iff.mpr
    refine ⟨n, (WithAbs.toAbs (w.restriction E) e : D), ?_⟩
    change algebraMap (w.restriction E).Completion w.Completion
      (WithAbs.toAbs (w.restriction E) e : (w.restriction E).Completion) =
        (WithAbs.toAbs w y : w.Completion) ^ p ^ n
    rw [algebraMap_completion_def, UniformSpace.Completion.mapRingHom_coe]
    change (WithAbs.toAbs w (algebraMap E L e) : w.Completion) = _
    rw [he]
    change UniformSpace.Completion.coeRingHom _ = _
    exact map_pow UniformSpace.Completion.coeRingHom _ _
  have hp : IsPurelyInseparable D w.Completion := by
    apply (isPurelyInseparable_iff_pow_mem D p).mpr
    intro x
    have hspan : Submodule.span D
        (Set.range fun i ↦ (WithAbs.toAbs w (Module.finBasis E L i) : w.Completion)) ≤
        (Subalgebra.perfectClosure D w.Completion p).toSubmodule := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hcoe _
    rw [span_coe_basis_eq_top w E (Module.finBasis E L)] at hspan
    exact Subalgebra.mem_perfectClosure_iff.mp
      (show x ∈ Subalgebra.perfectClosure D w.Completion p from
        hspan (Submodule.mem_top))
  ext x
  constructor
  · rintro ⟨d, rfl⟩
    apply mem_separableClosure_iff.mpr
    exact (Algebra.IsSeparable.isSeparable B d).map
      (IsScalarTower.toAlgHom B D w.Completion)
      (IsScalarTower.toAlgHom B D w.Completion).injective
  · intro hx
    exact IsPurelyInseparable.inseparable D x
      ((mem_separableClosure_iff.mp hx).tower_top D)

/-- Chen--Moriwaki, Remark 3.4.3: under the canonical bijection `M_{K'} ≃ M_L`, the fibre
weights of the finite extension `L/K` are the ratios of separable degrees
`[L_x : K_ω]_s / [L : K]_s`, computed here on the completions. -/
theorem fibreWeight_eq_finSepDegree (ω : AS.Ω)
    (x : ExtensionFiber AS (separableClosure K L) ω) :
    ParameterSpaceExtension.fibreWeight AS (separableClosure K L) ω x =
      (Field.finSepDegree ((ϕ AS L x.1).restriction K).Completion
          (ϕ AS L x.1).Completion : ℝ≥0∞) /
        (Field.finSepDegree K L : ℝ≥0∞) := by
  let w := ϕ AS L x.1
  have hd : (w.restriction (separableClosure K L)).localDegree K =
      Field.finSepDegree (w.restriction K).Completion w.Completion := by
    let E := separableClosure K L
    let B := (w.restriction K).Completion
    let D := (w.restriction E).Completion
    let : Algebra B D := algebraCompletion (w.restriction E) K
    have : IsScalarTower B D w.Completion := isScalarTower_completion_separableClosure L w
    let f := IsScalarTower.toAlgHom B D w.Completion
    have hf : f.range = (separableClosure B w.Completion).toSubalgebra := by
      ext y
      exact congrArg (fun S : Subfield w.Completion ↦ y ∈ S)
        (fieldRange_completion_separableClosure L w) |>.to_iff
    have hdim := (AlgEquiv.ofInjectiveField f).toLinearEquiv.finrank_eq
    rw [hf] at hdim
    have : FiniteDimensional B w.Completion := finiteDimensional_completion w K
    have hs := Field.finSepDegree_mul_finSepDegree_of_isAlgebraic B
      (separableClosure B w.Completion) w.Completion
    simp only [IsPurelyInseparable.finSepDegree_eq_one, mul_one,
      Field.finSepDegree_eq_finrank_of_isSeparable] at hs
    exact hdim.trans hs
  simp only [w, ϕ, restriction_extendAbsoluteValue] at hd
  have hg := Field.finSepDegree_mul_finSepDegree_of_isAlgebraic K (separableClosure K L) L
  simp only [IsPurelyInseparable.finSepDegree_eq_one, mul_one,
    Field.finSepDegree_eq_finrank_of_isSeparable] at hg
  rw [ParameterSpaceExtension.fibreWeight, hd, hg]
  rfl

end ParameterSpaceFinExtension

namespace Algebraic

variable [Algebra.IsAlgebraic K L]

/-- The finite subextension `K(a)` generated by an element of an algebraic extension. -/
def ofElement (a : L) : FiniteIntermediateField K L :=
  ⟨IntermediateField.adjoin K ({a} : Set L), by
    exact IntermediateField.adjoin.finiteDimensional
      ((Algebra.IsAlgebraic.isAlgebraic (R := K) a).isIntegral)⟩

/-- The generator `a` belongs to the finite subextension `K(a)`. -/
theorem mem_ofElement (a : L) : a ∈ (ofElement (K := K) (L := L) a).1 := by
  change a ∈ IntermediateField.adjoin K ({a} : Set L)
  exact IntermediateField.mem_adjoin_simple_self K a

/-- Chen--Moriwaki, Proposition 3.4.5: for an algebraic extension `L/K`, every extension
place of an intermediate stage lifts to `L`: the restriction maps `π_{L/K''}` are
surjective. -/
theorem surjective_restrict (F : IntermediateField K L) :
    Function.Surjective fun x : ParameterSpaceExtension AS L ↦
      ParameterSpaceExtension.restrict AS L x F := by
  intro x
  obtain ⟨w, hw⟩ := AbsoluteValue.exists_extension (L := L) x.abv
  have hbase : w.restriction K = AS.ϕ x.base := by
    ext a
    calc
      w (algebraMap K L a) = w (algebraMap F L (algebraMap K F a)) := by
        rw [← IsScalarTower.algebraMap_apply K F L]
      _ = x.abv (algebraMap K F a) :=
        congrArg (fun z : AbsoluteValue F ℝ ↦ z (algebraMap K F a)) hw
      _ = AS.ϕ x.base a :=
        congrArg (fun z : AbsoluteValue K ℝ ↦ z a) x.restrict_eq
  refine ⟨⟨x.base, w, hbase⟩, ?_⟩
  exact ParameterSpaceExtension.ext AS F rfl hw

/-- The base projection of an algebraic extension is surjective: every absolute value of the
base structure extends to `L` (the case `K'' = K` of Proposition 3.4.5). -/
theorem surjective_proj :
    Function.Surjective (ParameterSpaceExtension.proj (AS := AS) (L := L)) := by
  intro ω
  obtain ⟨w, hw⟩ := AbsoluteValue.exists_extension (L := L) (AS.ϕ ω)
  exact ⟨⟨ω, w, hw⟩, rfl⟩

variable {L} in
/-- The projection `π_{L/F}` from the algebraic parameter space to the finite stage attached
to a finite subextension `F/K`. For a non-separable finite stage this lands in the parameter
space of the separable part of `F/K`, exactly as in Definition 3.4.1. -/
def projFinite (F : FiniteIntermediateField K L) :
    ParameterSpaceExtension AS L → AS.ParameterSpaceFinExtension F :=
  fun x ↦
    ParameterSpaceExtension.restrict AS F.1 (ParameterSpaceExtension.restrict AS L x F)
      (separableClosure K F.1)

variable {AS} in
/-- The finite-stage fibre over `ω : Ω_K`. -/
abbrev FiniteBaseFiber (F : FiniteIntermediateField K L) (ω : AS.Ω) :=
  {x : AS.ParameterSpaceFinExtension F // ParameterSpaceExtension.proj x = ω}

omit [Algebra.IsAlgebraic K L] in
/-- In §3.4.2 the finite-stage fibres carry the discrete σ-algebra: every subset of a
finite-stage fibre is measurable. -/
theorem measurableSet_finiteBaseFiber (F : FiniteIntermediateField K L) (ω : AS.Ω)
    (B : Set (FiniteBaseFiber L F ω)) : MeasurableSet B := by
  let := ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K F.1) ω
  exact (Set.toFinite B).measurableSet

variable {AS} in
/-- The fibre `M_{L,ω}` over a base parameter `ω : Ω_K`. -/
abbrev BaseFiber (ω : AS.Ω) :=
  {x : ParameterSpaceExtension AS L // ParameterSpaceExtension.proj x = ω}

variable {AS L} in
/-- Restriction from the algebraic fibre `M_{L,ω}` to the finite fibre attached to `F`. -/
def projFiniteFiber (F : FiniteIntermediateField K L) (ω : AS.Ω) :
    BaseFiber L ω → FiniteBaseFiber L F ω :=
  fun x ↦ ⟨projFinite AS F x.1, by
    simpa [projFinite, ParameterSpaceFinExtension, ParameterSpaceExtension.proj,
      ParameterSpaceExtension.restrict] using x.2⟩

variable {L} in
/-- Inclusion of finite subextensions restricts to their separable parts. -/
def finiteSeparableInclusion {F G : FiniteIntermediateField K L} (hFG : F.1 ≤ G.1) :
    separableClosure K F.1 →ₐ[K] separableClosure K G.1 where
  toFun a := ⟨IntermediateField.inclusion hFG a,
    (map_mem_separableClosure_iff (IntermediateField.inclusion hFG)).mpr a.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' a b := Subtype.ext (map_add _ (a : F.1) (b : F.1))
  map_mul' a b := Subtype.ext (map_mul _ (a : F.1) (b : F.1))
  commutes' a := Subtype.ext ((IntermediateField.inclusion hFG).commutes a)

variable {L} in
/-- The finite-stage transition map is restriction along the inclusion of separable parts. -/
def projFiniteOfLE {F G : FiniteIntermediateField K L} (hFG : F.1 ≤ G.1)
    (x : ParameterSpaceFinExtension AS G) : ParameterSpaceFinExtension AS F where
  base := x.base
  abv := x.abv.pullback (finiteSeparableInclusion hFG).toRingHom
  restrict_eq := by
    ext a
    change x.abv (finiteSeparableInclusion hFG (algebraMap K (separableClosure K F.1) a)) =
      AS.ϕ x.base a
    rw [(finiteSeparableInclusion hFG).commutes]
    exact congrArg (fun v : AbsoluteValue K ℝ ↦ v a) x.restrict_eq

variable {L} in
omit [Algebra.IsAlgebraic K L] in
/-- Finite-stage projections commute with restriction to a smaller stage. -/
theorem projFiniteOfLE_projFinite {F G : FiniteIntermediateField K L} (hFG : F.1 ≤ G.1)
    (x : ParameterSpaceExtension AS L) :
    projFiniteOfLE AS hFG (projFinite AS G x) = projFinite AS F x := by
  apply ParameterSpaceExtension.ext _ _ rfl
  ext a
  rfl

variable {AS L} in
/-- The finite-stage transition on a fibre preserves its base point. -/
def projFiniteFiberOfLE {F G : FiniteIntermediateField K L} (hFG : F.1 ≤ G.1) (ω : AS.Ω)
    (x : FiniteBaseFiber L G ω) : FiniteBaseFiber L F ω :=
  ⟨projFiniteOfLE AS hFG x.1, x.2⟩

variable {AS L} in
omit [Algebra.IsAlgebraic K L] in
/-- Fibre projections commute with restriction to a smaller finite stage. -/
theorem projFiniteFiberOfLE_projFiniteFiber {F G : FiniteIntermediateField K L}
    (hFG : F.1 ≤ G.1) (ω : AS.Ω) (x : BaseFiber L ω) :
    projFiniteFiberOfLE hFG ω (projFiniteFiber G ω x) = projFiniteFiber F ω x := by
  apply Subtype.ext
  exact projFiniteOfLE_projFinite AS hFG x.1

/-- The inverse image `M_{L,x}` of a finite-stage point `x` under `π_{L/F}`. -/
def finiteFiber (F : FiniteIntermediateField K L)
    (x : ParameterSpaceFinExtension (AS := AS) (L := F.1)) :
    Set (ParameterSpaceExtension AS L) :=
  {z | projFinite AS F z = x}

/-- The projective-limit σ-algebra on `Ω_L`, generated by all finite-stage projections
`π_{L/F}` as in §3.4.2. -/
@[instance_reducible]
def projectiveMeasurableSpace : MeasurableSpace (ParameterSpaceExtension AS L) :=
  ⨆ F : FiniteIntermediateField K L,
    MeasurableSpace.comap (projFinite AS F) inferInstance

variable {AS} in
/-- The fibre σ-algebra `A_{L,ω}`, generated by the restrictions of finite-stage projections to
the fibre `M_{L,ω}`. -/
@[instance_reducible]
def fibreMeasurableSpace (ω : AS.Ω) :
    MeasurableSpace (BaseFiber L ω) :=
  ⨆ F : FiniteIntermediateField K L,
    MeasurableSpace.comap (projFiniteFiber F ω) inferInstance

omit [Algebra.IsAlgebraic K L] in
/-- Each finite-stage projection is measurable for the projective-limit σ-algebra. -/
theorem measurable_projFinite_projective (F : FiniteIntermediateField K L) :
    Measurable[projectiveMeasurableSpace AS L]
      (projFinite AS F) :=
  Measurable.of_comap_le (le_iSup (fun F : FiniteIntermediateField K L ↦
    MeasurableSpace.comap (projFinite AS F) inferInstance) F)

omit [Algebra.IsAlgebraic K L] in
/-- The base projection is measurable for the projective-limit σ-algebra. -/
theorem measurable_proj_projective :
    Measurable[projectiveMeasurableSpace AS L]
      (ParameterSpaceExtension.proj (AS := AS) (L := L)) := by
  exact (ParameterSpaceExtension.measurable_proj AS
    (separableClosure K (FiniteIntermediateField.bot (K := K) (L := L)).1)).comp
      (measurable_projFinite_projective AS L FiniteIntermediateField.bot)

/-- Every evaluation map `x ↦ |a|_x` is measurable for the projective-limit σ-algebra. -/
theorem measurable_eval_projective (a : L) :
    Measurable[projectiveMeasurableSpace AS L]
      (fun x : ParameterSpaceExtension AS L ↦ (ParameterSpaceExtension.ϕ x) a) := by
  let F := ofElement (K := K) L a
  let b : F := ⟨a, mem_ofElement L a⟩
  have hm : Measurable fun x : ParameterSpaceFinExtension AS F ↦
      ParameterSpaceFinExtension.ϕ AS F x b := by
    simp_rw [ParameterSpaceFinExtension.ϕ, ParameterSpaceFinExtension.extendAbsoluteValue_apply]
    exact (ParameterSpaceExtension.measurable_eval AS (separableClosure K F) _).pow_const _
  convert hm.comp (measurable_projFinite_projective AS L F) using 1
  funext x
  exact (congrArg (fun w : AbsoluteValue F ℝ ↦ w b)
    (ParameterSpaceFinExtension.extendAbsoluteValue_restriction (K := K) F
      ((ParameterSpaceExtension.ϕ x).restriction F))).symm

/-- The projective σ-algebra of §3.4.2 agrees with the concrete σ-algebra generated by the base
projection and all evaluations. This is Proposition 3.4.13. -/
theorem projectiveMeasurableSpace_eq :
    projectiveMeasurableSpace AS L =
      (inferInstance : MeasurableSpace (ParameterSpaceExtension AS L)) := by
  apply le_antisymm
  · apply iSup_le
    intro F
    exact ((ParameterSpaceExtension.measurable_restrict AS F.1 (separableClosure K F.1)).comp
      (ParameterSpaceExtension.measurable_restrict AS L F.1)).comap_le
  · change _ ⊔ ⨆ a : L, _ ≤ _
    exact sup_le (measurable_proj_projective AS L).comap_le
      (iSup_le fun a ↦ (measurable_eval_projective AS L a).comap_le)

/-- Logarithmic evaluations are measurable for the projective-limit σ-algebra. -/
theorem measurable_log_projective (a : L) :
    Measurable[projectiveMeasurableSpace AS L]
      (fun x : ParameterSpaceExtension AS L ↦ Real.log ((ParameterSpaceExtension.ϕ x) a)) :=
  (measurable_eval_projective AS L a).log

/-- A real-valued cylinder function on `Ω_L`, i.e. a function descending to a finite
subextension. This is the global vector space `V_L` from Remark 3.4.7. -/
structure DescendsToFinite (f : ParameterSpaceExtension AS L → ℝ) : Type (max u v w) where
  /-- A finite subextension through which the function factors. -/
  F : FiniteIntermediateField K L
  /-- The descended function on the finite-stage space of Definition 3.4.1. -/
  g : ParameterSpaceFinExtension AS F → ℝ
  /-- The factorization through `π_{L/F}`. -/
  eq_comp : f = g ∘ projFinite AS F

/-- The vector space of real-valued cylinder functions on `Ω_L`. -/
abbrev CylinderFunctions :=
  Σ f : ParameterSpaceExtension AS L → ℝ, DescendsToFinite AS L f

variable {AS L} in
omit [Algebra.IsAlgebraic K L] in
/-- Remark 3.4.7: the cylinder functions `V_L` are closed under addition. -/
theorem DescendsToFinite.nonempty_add {f g : ParameterSpaceExtension AS L → ℝ}
    (hf : DescendsToFinite AS L f) (hg : DescendsToFinite AS L g) :
    Nonempty (DescendsToFinite AS L (f + g)) := by
  refine ⟨⟨FiniteIntermediateField.sup hf.F hg.F, fun x ↦
    hf.g (projFiniteOfLE AS (FiniteIntermediateField.left_le_sup hf.F hg.F) x) +
      hg.g (projFiniteOfLE AS (FiniteIntermediateField.right_le_sup hf.F hg.F) x), ?_⟩⟩
  ext x
  simp only [hf.eq_comp, hg.eq_comp, Pi.add_apply, Function.comp_apply,
    projFiniteOfLE_projFinite]

variable {AS L} in
omit [Algebra.IsAlgebraic K L] in
/-- Remark 3.4.7: the cylinder functions `V_L` are closed under scalar multiplication. -/
theorem DescendsToFinite.nonempty_smul (c : ℝ) {f : ParameterSpaceExtension AS L → ℝ}
    (hf : DescendsToFinite AS L f) : Nonempty (DescendsToFinite AS L (c • f)) := by
  refine ⟨⟨hf.F, fun x ↦ c * hf.g x, ?_⟩⟩
  ext x
  simp only [hf.eq_comp, Pi.smul_apply, Function.comp_apply, smul_eq_mul]

variable {AS L} in
/-- A real-valued fibre cylinder function on `M_{L,ω}`, descending to a finite fibre. This is
the definition-level counterpart of `V_{L,ω}` in §3.4.2. -/
structure DescendsToFiniteFiber (ω : AS.Ω)
    (f : BaseFiber L ω → ℝ) :
    Type (max u v w) where
  /-- A finite subextension through which the fibre function factors. -/
  F : FiniteIntermediateField K L
  /-- The descended function on the finite-stage fibre. -/
  g : FiniteBaseFiber L F ω → ℝ
  /-- The factorization through the fibre projection. -/
  eq_comp : f = g ∘ projFiniteFiber F ω

/-- The fibre cylinder functions `V_{L,ω}`. -/
abbrev FibreCylinderFunctions (ω : AS.Ω) :=
  Σ f : BaseFiber L ω → ℝ,
    DescendsToFiniteFiber ω f

variable {AS L} in
omit [Algebra.IsAlgebraic K L] in
/-- Chen--Moriwaki, Proposition 3.4.6: the fibre cylinder functions `V_{L,ω}` are closed
under addition. -/
theorem DescendsToFiniteFiber.nonempty_add {ω : AS.Ω} {f g : BaseFiber L ω → ℝ}
    (hf : DescendsToFiniteFiber ω f) (hg : DescendsToFiniteFiber ω g) :
    Nonempty (DescendsToFiniteFiber ω (f + g)) := by
  refine ⟨⟨FiniteIntermediateField.sup hf.F hg.F, fun x ↦
    hf.g (projFiniteFiberOfLE (FiniteIntermediateField.left_le_sup hf.F hg.F) ω x) +
      hg.g (projFiniteFiberOfLE (FiniteIntermediateField.right_le_sup hf.F hg.F) ω x), ?_⟩⟩
  ext x
  simp only [hf.eq_comp, hg.eq_comp, Pi.add_apply, Function.comp_apply,
    projFiniteFiberOfLE_projFiniteFiber]

variable {AS L} in
omit [Algebra.IsAlgebraic K L] in
/-- Chen--Moriwaki, Proposition 3.4.6: the fibre cylinder functions `V_{L,ω}` are closed
under multiplication; `V_{L,ω}` is an `ℝ`-algebra of functions. -/
theorem DescendsToFiniteFiber.nonempty_mul {ω : AS.Ω} {f g : BaseFiber L ω → ℝ}
    (hf : DescendsToFiniteFiber ω f) (hg : DescendsToFiniteFiber ω g) :
    Nonempty (DescendsToFiniteFiber ω (f * g)) := by
  refine ⟨⟨FiniteIntermediateField.sup hf.F hg.F, fun x ↦
    hf.g (projFiniteFiberOfLE (FiniteIntermediateField.left_le_sup hf.F hg.F) ω x) *
      hg.g (projFiniteFiberOfLE (FiniteIntermediateField.right_le_sup hf.F hg.F) ω x), ?_⟩⟩
  ext x
  simp only [hf.eq_comp, hg.eq_comp, Pi.mul_apply, Function.comp_apply,
    projFiniteFiberOfLE_projFiniteFiber]

variable {AS L} in
omit [Algebra.IsAlgebraic K L] in
/-- Chen--Moriwaki, Proposition 3.4.6: the fibre cylinder functions `V_{L,ω}` are closed
under scalar multiplication. -/
theorem DescendsToFiniteFiber.nonempty_smul (c : ℝ) {ω : AS.Ω} {f : BaseFiber L ω → ℝ}
    (hf : DescendsToFiniteFiber ω f) : Nonempty (DescendsToFiniteFiber ω (c • f)) := by
  refine ⟨⟨hf.F, fun x ↦ c * hf.g x, ?_⟩⟩
  ext x
  simp only [hf.eq_comp, Pi.smul_apply, Function.comp_apply, smul_eq_mul]

variable {AS L} in
/-- The fibre integral of a cylinder function, computed at a finite stage through which it
descends; this is the operator `I_{L/K,ω}` of formula (3.17). -/
noncomputable def fibreCylinderIntegral {ω : AS.Ω} {f : BaseFiber L ω → ℝ}
    (d : DescendsToFiniteFiber ω f) : ℝ :=
  ∫ y, d.g y ∂ParameterSpaceFinExtension.fibreProbabilityMeasure AS d.F ω

variable {AS L} in
/-- Chen--Moriwaki, Proposition 3.4.6 (well-definedness of `I_{L/K,ω}`): the fibre integral
of a cylinder function does not depend on the finite stage through which it descends. -/
theorem fibreCylinderIntegral_congr {ω : AS.Ω} {f : BaseFiber L ω → ℝ}
    (d₁ d₂ : DescendsToFiniteFiber ω f) :
    fibreCylinderIntegral d₁ = fibreCylinderIntegral d₂ := by
  sorry

/-- The cylinder content on the fibre `M_{L,ω}`: the infimum of the prescribed finite-stage
fibre measures over cylinder supersets. On a cylinder set `(π_{L/F,ω})⁻¹(B)` it takes the
prescribed value `P_{F,ω}(B)`; this is the additive set function extended by Carathéodory's
theorem in the proof of Proposition 3.4.6. -/
noncomputable def fibreCylinderContent (ω : AS.Ω) (A : Set (BaseFiber L ω)) : ℝ≥0∞ :=
  ⨅ (F : FiniteIntermediateField K L) (B : Set (FiniteBaseFiber L F ω))
    (_ : A ⊆ projFiniteFiber F ω ⁻¹' B),
    ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω B

/-- Chen--Moriwaki, Proposition 3.4.6: the projective-limit fibre probability measure
`P_{L,ω}` on the fibre `M_{L,ω}`, defined as the Carathéodory extension of the cylinder
content: the outer measure generated by `fibreCylinderContent` (whose value on a countable
cylinder cover is the infimum of the total finite-stage measures), restricted to the fibre
σ-algebra `A_{L,ω}`. -/
noncomputable def fibreProbabilityMeasure (ω : AS.Ω) :
    @Measure (BaseFiber L ω)
      (fibreMeasurableSpace L ω) :=
  letI : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  (OuterMeasure.ofFunction (fibreCylinderContent AS L ω) (by sorry)).toMeasure (by sorry)

/-- Chen--Moriwaki, Proposition 3.4.6: `P_{L,ω}` has total mass one. -/
theorem fibreProbabilityMeasure_isProbability (ω : AS.Ω) :
    @IsProbabilityMeasure (BaseFiber L ω)
      (fibreMeasurableSpace L ω)
      (fibreProbabilityMeasure AS L ω) := by
  sorry

/-- Chen--Moriwaki, Proposition 3.4.6: the finite-stage marginals of `P_{L,ω}` are the
prescribed finite fibre probability measures. -/
theorem map_fibreProbabilityMeasure_projFiniteFiber (ω : AS.Ω)
    (F : FiniteIntermediateField K L) :
    @Measure.map (BaseFiber L ω) (FiniteBaseFiber L F ω)
        (fibreMeasurableSpace L ω) inferInstance
        (projFiniteFiber F ω) (fibreProbabilityMeasure AS L ω) =
      ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω := by
  sorry

/-- Chen--Moriwaki, Proposition 3.4.6, formula (3.17): integrating a cylinder function
against `P_{L,ω}` computes its finite-stage fibre integral `I_{L/K,ω}`. -/
theorem integral_fibreProbabilityMeasure_descend {ω : AS.Ω} {f : BaseFiber L ω → ℝ}
    (d : DescendsToFiniteFiber ω f) :
    ∫ x, f x ∂fibreProbabilityMeasure AS L ω = fibreCylinderIntegral d := by
  sorry

/-- The fibre integral `I_{L/K}` for nonnegative functions, defined using the projective-limit
probability measures `P_{L,ω}`. -/
noncomputable def fibreLIntegral
    (f : ParameterSpaceExtension AS L → ℝ≥0∞) : AS.Ω → ℝ≥0∞ :=
  fun ω ↦
    ∫⁻ x : BaseFiber L ω, f x.1
      ∂fibreProbabilityMeasure AS L ω

/-- The fibre integration operator `I_{L/K}` on real-valued functions, defined using the
projective-limit fibre probability measures (Remark 3.4.7 and the discussion after
Proposition 3.4.8). -/
noncomputable def fibreIntegral (f : ParameterSpaceExtension AS L → ℝ) : AS.Ω → ℝ :=
  fun ω ↦
    ∫ x : BaseFiber L ω, f x.1
      ∂fibreProbabilityMeasure AS L ω

/-- Remark 3.4.7: fibre integration retracts the pullback along the base projection:
`I_{L/K}(g ∘ π_{L/K}) = g`. -/
theorem fibreIntegral_comp_proj (g : AS.Ω → ℝ) :
    fibreIntegral AS L (fun x ↦ g (ParameterSpaceExtension.proj x)) = g := by
  sorry

/-- Formula (3.19): on a function pulled back from a finite stage, the fibre integration
operator computes the finite-stage fibre integral: `I_{L/K}(g ∘ π_{L/K''}) = I_{K''/K}(g)`. -/
theorem fibreIntegral_comp_projFinite (F : FiniteIntermediateField K L)
    (g : ParameterSpaceFinExtension AS F → ℝ) :
    fibreIntegral AS L (fun x ↦ g (projFinite AS F x)) =
      ParameterSpaceFinExtension.fibreIntegral AS F g := by
  sorry

omit [Algebra.IsAlgebraic K L] in
/-- Chen--Moriwaki, Proposition 3.4.8: a projectively measurable function restricts to an
`A_{L,ω}`-measurable function on every fibre. -/
theorem measurable_restrict_baseFiber {f : ParameterSpaceExtension AS L → ℝ≥0∞}
    (hf : Measurable[projectiveMeasurableSpace AS L] f) (ω : AS.Ω) :
    Measurable[fibreMeasurableSpace L ω] fun x : BaseFiber L ω ↦ f x.1 := by
  apply hf.comp
  apply Measurable.of_comap_le
  change MeasurableSpace.comap _ (⨆ F : FiniteIntermediateField K L, _) ≤ _
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun F ↦ ?_
  rw [MeasurableSpace.comap_comp]
  have h := le_iSup
    (fun F : FiniteIntermediateField K L ↦
      MeasurableSpace.comap (projFiniteFiber F ω) inferInstance) F
  change MeasurableSpace.comap _ (MeasurableSpace.comap Subtype.val _) ≤ _ at h
  rw [MeasurableSpace.comap_comp] at h
  exact h

/-- Proposition 3.4.8: fibre integration of a nonnegative projectively measurable function is
measurable on the base. -/
theorem measurable_fibreLIntegral {f : ParameterSpaceExtension AS L → ℝ≥0∞}
    (hf : Measurable[projectiveMeasurableSpace AS L] f) :
    Measurable (fibreLIntegral AS L f) := by
  sorry

/-- The measure `ν_L` on the projective-limit parameter space `Ω_L`, defined by the formula
following Proposition 3.4.8:
`ν_L(A) = ∫_{Ω_K} ∫_{M_{L,ω}} 1_A(x) dP_{L,ω} dν_K`. -/
noncomputable def measure :
    @Measure (ParameterSpaceExtension AS L) (projectiveMeasurableSpace AS L) :=
  letI : MeasurableSpace (ParameterSpaceExtension AS L) :=
    projectiveMeasurableSpace AS L
  Measure.ofMeasurable
      (fun A _hA ↦
        ∫⁻ ω, fibreLIntegral (AS := AS) (L := L)
          (Set.indicator A fun _ ↦ (1 : ℝ≥0∞)) ω ∂AS.v)
      (by simp [fibreLIntegral])
      (by
        intro A hA hdisj
        sorry)

/-- The defining formula for `ν_L`. -/
theorem measure_apply {A : Set (ParameterSpaceExtension AS L)}
    (hA : @MeasurableSet (ParameterSpaceExtension AS L)
      (projectiveMeasurableSpace AS L) A) :
    measure AS L A =
      ∫⁻ ω, fibreLIntegral (AS := AS) (L := L)
        (Set.indicator A fun _ ↦ (1 : ℝ≥0∞)) ω ∂AS.v :=
  by
    let : MeasurableSpace (ParameterSpaceExtension AS L) :=
      projectiveMeasurableSpace AS L
    exact Measure.ofMeasurable_apply A hA

/-- Formula (3.18): the projective-limit measure `ν_L` integrates nonnegative projectively
measurable functions through the fibre integration operator. -/
theorem lintegral_measure {f : ParameterSpaceExtension AS L → ℝ≥0∞}
    (hf : Measurable[projectiveMeasurableSpace AS L] f) :
    ∫⁻ x, f x ∂measure AS L = ∫⁻ ω, fibreLIntegral AS L f ω ∂AS.v := by
  sorry

/-- Chen--Moriwaki, Proposition 3.4.9: a projectively measurable function is `ν_L`-integrable
if and only if the fibre integral of its absolute value — computed in `[0, +∞]`, as in the
discussion after Proposition 3.4.8, since fibres of an infinite extension need not have
integrable restrictions — has finite integral on the base. -/
theorem integrable_measure_iff {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Measurable[projectiveMeasurableSpace AS L] f) :
    Integrable[projectiveMeasurableSpace AS L] f (measure AS L) ↔
      ∫⁻ ω, fibreLIntegral AS L (fun x ↦ ENNReal.ofReal |f x|) ω ∂AS.v < ∞ := by
  sorry

/-- Chen--Moriwaki, Proposition 3.4.9: fibre integration is a contraction from
`L¹(Ω_L, ν_L)` to `L¹(Ω_K, ν_K)`; this is the continuity of the operator `I_{L/K}`. -/
theorem integral_abs_fibreIntegral_le {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    ∫ ω, |fibreIntegral AS L f ω| ∂AS.v ≤ ∫ x, |f x| ∂measure AS L := by
  sorry

/-- Chen--Moriwaki, Proposition 3.4.9, formula (3.20): the projective-limit measure
integrates integrable functions through the fibre integration operator. -/
theorem integral_measure {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    ∫ x, f x ∂measure AS L = ∫ ω, fibreIntegral AS L f ω ∂AS.v := by
  sorry

/-- Formula (3.21): the pullback of a `ν_K`-integrable function along the base projection is
`ν_L`-integrable. -/
theorem integrable_comp_proj_measure {g : AS.Ω → ℝ} (hg : Integrable g AS.v) :
    Integrable[projectiveMeasurableSpace AS L]
      (fun x ↦ g (ParameterSpaceExtension.proj x)) (measure AS L) := by
  sorry

/-- Formula (3.21): integrating a pullback from the base against `ν_L` is integrating
against `ν_K`. -/
theorem integral_comp_proj_measure {g : AS.Ω → ℝ} (hg : Integrable g AS.v) :
    ∫ x, g (ParameterSpaceExtension.proj x) ∂measure AS L = ∫ ω, g ω ∂AS.v := by
  sorry

/-- Proposition 3.4.10: logarithmic evaluations are integrable for the projective-limit measure. -/
theorem integrable_log_measure (a : L) (ha : a ≠ 0) :
    Integrable[projectiveMeasurableSpace AS L]
      (fun x : ParameterSpaceExtension AS L ↦ Real.log ((ParameterSpaceExtension.ϕ x) a))
      (measure (AS := AS) (L := L)) := by
  sorry

/-- The projection `π_{L/K}` sends the projective-limit measure to the base measure. -/
theorem map_measure_proj :
    (letI : MeasurableSpace (ParameterSpaceExtension AS L) :=
      projectiveMeasurableSpace AS L
    Measure.map ParameterSpaceExtension.proj
      (measure AS L) = AS.v) := by
  sorry

/-- Chen--Moriwaki, Definition 3.4.11: the concrete algebraic extension adelic structure
`S ⊗_K L`. -/
noncomputable def _root_.ArakelovGeometry.AdelicStructure.algebraicExtension :
    AdelicStructure L where
  Ω := ParameterSpaceExtension AS L
  A := projectiveMeasurableSpace AS L
  v := measure AS L
  ϕ := ParameterSpaceExtension.ϕ
  measurable_log := fun a _ha ↦ measurable_log_projective AS L a
  integrable_log := integrable_log_measure AS L

/-- Chen--Moriwaki, Proposition 3.4.10: the algebraic extension of a proper adelic curve is
proper. -/
theorem isProper_algebraicExtension [AS.toAdelicCurve.IsProper] :
    (AS.algebraicExtension L).toAdelicCurve.IsProper := by
  sorry

end Algebraic

end AdelicStructure

section Compatibility

open AdelicStructure

variable {K : Type u} [Field K] (AS : AdelicStructure.{u, v} K)
variable (M : Type w) [Field M] [Algebra K M]

/-- Chen--Moriwaki, Proposition 3.4.4: finite extension of adelic structures is transitive:
for a tower `K ⊆ K₁ ⊆ K₂` of finite extensions, `(S ⊗_K K₁) ⊗_{K₁} K₂` and `S ⊗_K K₂` are
canonically equivalent, compatibly with the projections to the base (formula (3.15)). -/
theorem exists_equiv_finiteExtension_finiteExtension [FiniteDimensional K M]
    (F : IntermediateField K M) :
    ∃ e : AdelicStructure.Equiv
        ((AS.finiteExtension F).finiteExtension M) (AS.finiteExtension M),
      (∀ x, ParameterSpaceExtension.proj (ParameterSpaceExtension.proj x) =
        ParameterSpaceExtension.proj (e.toMeasurableEquiv x)) ∧
      ∀ g : ((AS.finiteExtension F).finiteExtension M).Ω → ℝ,
        ParameterSpaceFinExtension.fibreIntegral AS F
            (ParameterSpaceFinExtension.fibreIntegral (AS.finiteExtension F) M g) =
          ParameterSpaceFinExtension.fibreIntegral AS M
            (fun y ↦ g (e.toMeasurableEquiv.symm y)) := by
  sorry

/-- Chen--Moriwaki, Theorem 3.4.12: algebraic extension of adelic structures is transitive:
for a tower `K ⊆ L₁ ⊆ L₂` of algebraic extensions, `(S ⊗_K L₁) ⊗_{L₁} L₂` and `S ⊗_K L₂` are
canonically equivalent, compatibly with the projections to the base (formulae (3.22),
(3.23)). The fibre identity is pointwise for measurable nonnegative functions, as in
the proof on PDF pages 213–214. For globally integrable real functions it holds almost
everywhere, by Proposition 3.4.9. The signed integral in the source is defined only on
its integrability domain (PDF pages 210–211); totalizing it does not give an identity
for arbitrary real functions. -/
theorem exists_equiv_algebraicExtension_algebraicExtension [Algebra.IsAlgebraic K M]
    (F : IntermediateField K M) :
    ∃ e : AdelicStructure.Equiv
        ((AS.algebraicExtension F).algebraicExtension M) (AS.algebraicExtension M),
      (∀ x, ParameterSpaceExtension.proj (ParameterSpaceExtension.proj x) =
        ParameterSpaceExtension.proj (e.toMeasurableEquiv x)) ∧
      (∀ g : ((AS.algebraicExtension F).algebraicExtension M).Ω → ℝ≥0∞,
        Measurable[((AS.algebraicExtension F).algebraicExtension M).A] g →
        Algebraic.fibreLIntegral AS F
            (Algebraic.fibreLIntegral (AS.algebraicExtension F) M g) =
          Algebraic.fibreLIntegral AS M
            (fun y ↦ g (e.toMeasurableEquiv.symm y))) ∧
      ∀ g : ((AS.algebraicExtension F).algebraicExtension M).Ω → ℝ,
        Integrable[((AS.algebraicExtension F).algebraicExtension M).A] g
          ((AS.algebraicExtension F).algebraicExtension M).v →
        Algebraic.fibreIntegral AS F
            (Algebraic.fibreIntegral (AS.algebraicExtension F) M g) =ᵐ[AS.v]
          Algebraic.fibreIntegral AS M
            (fun y ↦ g (e.toMeasurableEquiv.symm y)) := by
  sorry

end Compatibility

end Extensions

end ArakelovGeometry
