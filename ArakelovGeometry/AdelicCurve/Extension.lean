/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Defs
import ArakelovGeometry.AdelicCurve.RootBounds
import ArakelovGeometry.ExternalResults.AbsoluteValueFinite
import ArakelovGeometry.ExternalResults.AbsoluteValueCompact
import ArakelovGeometry.ExternalResults.AbsoluteValueExtension
import ArakelovGeometry.ExternalResults.FunctionalMonotoneClass
import ArakelovGeometry.ExternalResults.AbsoluteValueLocal
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Tuple.Sort
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
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.SetAlgebra
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


/-- The product over any fixed-size subset of a decreasing nonnegative tuple is bounded
by the product over its initial segment. -/
theorem prod_le_prod_initial_of_antitone {n k : ℕ} (hk : k ≤ n)
    {s : Fin n → ℝ} (hs : Antitone s) (hs0 : ∀ i, 0 ≤ s i)
    (J : Finset (Fin n)) (hJ : J.card = k) :
    (∏ j ∈ J, s j) ≤ ∏ i : Fin k, s (i.castLE hk) := by
  classical
  have hindex (i : Fin k) : i.val ≤ (J.orderEmbOfFin hJ i).val := by
    cases k with
    | zero => exact i.elim0
    | succ k =>
      induction i using Fin.induction with
      | zero => exact Nat.zero_le _
      | succ i ih =>
        exact Nat.succ_le_of_lt (lt_of_le_of_lt ih
          ((J.orderEmbOfFin hJ).strictMono (Fin.castSucc_lt_succ (i := i))))
  calc
    _ = ∏ i : Fin k, s (J.orderEmbOfFin hJ i) := by
      calc
        _ = ∏ j ∈ Finset.univ.image (J.orderEmbOfFin hJ), s j := by simp
        _ = _ := Finset.prod_image (J.orderEmbOfFin hJ).injective.injOn
    _ ≤ _ := Finset.prod_le_prod (fun i _ ↦ hs0 _) (fun i _ ↦ hs (hindex i))

/-- An initial product in a decreasing nonnegative tuple is the largest subset product
of the same size. -/
theorem prod_initial_eq_iSup_prod {n k : ℕ} (hk : k ≤ n)
    {s : Fin n → ℝ} (hs : Antitone s) (hs0 : ∀ i, 0 ≤ s i) :
    (∏ i : Fin k, s (i.castLE hk)) =
      ⨆ J : {J : Finset (Fin n) // J.card = k}, ∏ j ∈ J.val, s j := by
  classical
  let J₀ : {J : Finset (Fin n) // J.card = k} :=
    ⟨Finset.univ.map (Fin.castLEEmb hk), by simp⟩
  let : Nonempty {J : Finset (Fin n) // J.card = k} := ⟨J₀⟩
  apply le_antisymm
  · apply Finite.le_ciSup_of_le J₀
    simp [J₀, Finset.prod_map]
  · apply ciSup_le
    intro J
    exact prod_le_prod_initial_of_antitone hk hs hs0 J.val J.property

/-- Sorting a tuple identifies its initial products with the largest subset products. -/
theorem prod_initial_comp_perm_eq_iSup_prod {n k : ℕ} (hk : k ≤ n)
    {s : Fin n → ℝ} (hs0 : ∀ i, 0 ≤ s i) (π : Equiv.Perm (Fin n))
    (hπ : Antitone (s ∘ π)) :
    (∏ i : Fin k, s (π (i.castLE hk))) =
      ⨆ J : {J : Finset (Fin n) // J.card = k}, ∏ j ∈ J.val, s j := by
  classical
  let e := π.finsetCongr.subtypeEquiv
    (p := fun J : Finset (Fin n) ↦ J.card = k)
    (q := fun J : Finset (Fin n) ↦ J.card = k) (by intro J; simp)
  calc
    _ = ⨆ J : {J : Finset (Fin n) // J.card = k}, ∏ j ∈ J.val, s (π j) :=
      prod_initial_eq_iSup_prod hk hπ (fun i ↦ hs0 (π i))
    _ = ⨆ J : {J : Finset (Fin n) // J.card = k}, ∏ j ∈ (e J).val, s j := by
      apply iSup_congr
      intro J
      simp [e, Equiv.subtypeEquiv, Finset.prod_map]
    _ = _ := e.iSup_comp (g := fun J ↦ ∏ j ∈ J.val, s j)

/-- A positive tuple has measurable ordered entries when its maximal subset products
are measurable, without any measurability assumption on the sorting permutations. -/
theorem measurable_perm_eval_of_measurable_iSup_prod
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (s : Ω → Fin n → ℝ) (hs : ∀ ω i, 0 < s ω i)
    (π : Ω → Equiv.Perm (Fin n)) (hπ : ∀ ω, Antitone (s ω ∘ π ω))
    (hP : ∀ k ≤ n, Measurable fun ω ↦
      ⨆ J : {J : Finset (Fin n) // J.card = k}, ∏ j ∈ J.val, s ω j)
    (i : Fin n) :
    Measurable fun ω ↦ s ω (π ω i) := by
  have hprefix (k : ℕ) (hk : k ≤ n) :
      Measurable fun ω ↦ ∏ j : Fin k, s ω (π ω (j.castLE hk)) := by
    have heq (ω : Ω) := prod_initial_comp_perm_eq_iSup_prod hk
      (fun j ↦ (hs ω j).le) (π ω) (hπ ω)
    simp_rw [heq]
    exact hP k hk
  have heq (ω : Ω) :
      s ω (π ω i) =
        (∏ j : Fin (i.val + 1), s ω (π ω (j.castLE i.isLt))) /
          ∏ j : Fin i.val, s ω (π ω (j.castLE i.isLt.le)) := by
    rw [Fin.prod_univ_castSucc]
    change s ω (π ω i) = ((∏ j : Fin i.val, s ω (π ω (j.castLE i.isLt.le))) *
      s ω (π ω i)) / _
    exact (mul_div_cancel_left₀ _ (ne_of_gt (Finset.prod_pos (fun _ _ ↦ hs ω _)))).symm
  simp_rw [heq]
  exact (hprefix (i.val + 1) i.isLt).div (hprefix i.val i.isLt.le)

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


/-- Evaluation maps multiplied by measurable base functions generate the extension
sigma algebra. -/
theorem measurableSpace_eq_iSup_comap_eval_mul_base :
    (inferInstance : MeasurableSpace (ParameterSpaceExtension AS L)) =
      ⨆ b : L, ⨆ φ : {φ : AS.Ω → ℝ // Measurable φ},
        MeasurableSpace.comap (fun x : ParameterSpaceExtension AS L ↦ x.ϕ b * φ.val x.proj)
          inferInstance := by
  let m : MeasurableSpace (ParameterSpaceExtension AS L) :=
    ⨆ b : L, ⨆ φ : {φ : AS.Ω → ℝ // Measurable φ},
      MeasurableSpace.comap (fun x : ParameterSpaceExtension AS L ↦ x.ϕ b * φ.val x.proj)
        inferInstance
  apply le_antisymm
  · change MeasurableSpace.comap (proj (AS := AS) (L := L)) AS.A ⊔
      (⨆ b : L, MeasurableSpace.comap (fun x : ParameterSpaceExtension AS L ↦ x.ϕ b)
        inferInstance) ≤ m
    apply sup_le
    · apply Measurable.comap_le
      intro A hA
      have hm : @Measurable (ParameterSpaceExtension AS L) ℝ m _
          (fun x ↦ x.ϕ 1 * (A.indicator fun _ ↦ (1 : ℝ)) x.proj) :=
        Measurable.of_comap_le (le_iSup_of_le 1
          (le_iSup_of_le ⟨A.indicator fun _ ↦ (1 : ℝ), measurable_const.indicator hA⟩ le_rfl))
      have hi : @Measurable (ParameterSpaceExtension AS L) ℝ m _
          ((proj ⁻¹' A).indicator fun _ ↦ (1 : ℝ)) := by
        simpa only [map_one, one_mul, ← Set.indicator_comp_right, Function.comp_def] using hm
      exact (measurable_indicator_const_iff (1 : ℝ)).mp hi
    · apply iSup_le
      intro b
      have hm : @Measurable (ParameterSpaceExtension AS L) ℝ m _
          (fun x ↦ x.ϕ b * (1 : ℝ)) :=
        Measurable.of_comap_le (le_iSup_of_le b
          (le_iSup_of_le ⟨fun _ ↦ (1 : ℝ), measurable_const⟩ le_rfl))
      simpa only [mul_one] using hm.comap_le
  · apply iSup_le
    intro b
    apply iSup_le
    intro φ
    exact ((measurable_eval AS L b).mul (φ.property.comp (measurable_proj AS L))).comap_le

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


variable (K) in
/-- The maximal products of fixed numbers of embedding values are measurable by the
Galois orbit maximum formula. -/
theorem measurable_iSup_prod_embeddings {E : Type*} [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (s : AS.Ω → ParameterSpaceExtension AS (AlgebraicClosure K))
    (hs : ∀ ω, (s ω).proj = ω) (b : E) (k : ℕ)
    (hk : k ≤ Fintype.card (E →ₐ[K] AlgebraicClosure K)) :
    Measurable fun ω ↦
      ⨆ J : {J : Finset (E →ₐ[K] AlgebraicClosure K) // J.card = k},
        ∏ σ ∈ J.val, (s ω).ϕ (σ b) := by
  classical
  let e := Fintype.equivFin (E →ₐ[K] AlgebraicClosure K)
  let J₀ : {J : Finset (E →ₐ[K] AlgebraicClosure K) // J.card = k} :=
    ⟨(Finset.univ.map (Fin.castLEEmb hk)).map e.symm.toEmbedding, by simp⟩
  let : Nonempty {J : Finset (E →ₐ[K] AlgebraicClosure K) // J.card = k} := ⟨J₀⟩
  let P (ω : AS.Ω) := ⨆ J : {J : Finset (E →ₐ[K] AlgebraicClosure K) // J.card = k},
    ∏ σ ∈ J.val, (s ω).ϕ (σ b)
  have hbound (ω : AS.Ω)
      (J : {J : Finset (E →ₐ[K] AlgebraicClosure K) // J.card = k})
      (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
      (s ω).ϕ (τ (∏ σ ∈ J.val, σ b)) ≤ P ω := by
    let p := (AlgEquiv.refl : E ≃ₐ[K] E).arrowCongr τ
    let J' : {J : Finset (E →ₐ[K] AlgebraicClosure K) // J.card = k} :=
      ⟨J.val.map p.toEmbedding, by simpa using J.property⟩
    apply Finite.le_ciSup_of_le J'
    simp only [J', Finset.prod_map]
    rw [_root_.map_prod, AbsoluteValue.map_prod]
    rfl
  have heq (ω : AS.Ω) : P ω =
      ⨆ J : {J : Finset (E →ₐ[K] AlgebraicClosure K) // J.card = k},
        ⨆ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
          (s ω).ϕ (τ (∏ σ ∈ J.val, σ b)) := by
    apply le_antisymm
    · apply ciSup_le
      intro J
      apply Finite.le_ciSup_of_le J
      have hb : BddAbove (Set.range fun τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K ↦
          (s ω).ϕ (τ (∏ σ ∈ J.val, σ b))) := ⟨P ω, by
        rintro _ ⟨τ, rfl⟩
        exact hbound ω J τ⟩
      apply le_ciSup_of_le hb (AlgEquiv.refl : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      change (∏ σ ∈ J.val, (s ω).ϕ (σ b)) ≤ (s ω).ϕ (∏ σ ∈ J.val, σ b)
      rw [AbsoluteValue.map_prod]
    · apply ciSup_le
      intro J
      exact ciSup_le (hbound ω J)
  change Measurable fun ω ↦ P ω
  simp_rw [heq]
  apply Measurable.iSup
  intro J
  apply measurable_iSup_abv_aut AS s hs
  change (∏ σ ∈ J.val, σ b) ∈ separableClosure K (AlgebraicClosure K)
  exact (separableClosure K (AlgebraicClosure K)).prod_mem
    (fun σ _ ↦ IsSeparable.map σ σ.injective (Algebra.IsSeparable.isSeparable K b))

variable (K) in
/-- The decreasingly ordered absolute values of the embeddings of a nonzero separable
element are measurable. The chosen ordering need not depend measurably on the base point. -/
theorem measurable_ordered_abv_embeddings {E : Type*} [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (s : AS.Ω → ParameterSpaceExtension AS (AlgebraicClosure K))
    (hs : ∀ ω, (s ω).proj = ω) (b : E) (hb : b ≠ 0)
    {n : ℕ} (e : Fin n ≃ (E →ₐ[K] AlgebraicClosure K))
    (π : AS.Ω → Equiv.Perm (Fin n))
    (hπ : ∀ ω, Antitone (fun i ↦ (s ω).ϕ (e (π ω i) b)))
    (i : Fin n) :
    Measurable fun ω ↦ (s ω).ϕ (e (π ω i) b) := by
  classical
  have hP (k : ℕ) (hk : k ≤ n) :
      Measurable fun ω ↦
        ⨆ J : {J : Finset (Fin n) // J.card = k}, ∏ j ∈ J.val, (s ω).ϕ (e j b) := by
    let eJ := e.finsetCongr.subtypeEquiv
      (p := fun J : Finset (Fin n) ↦ J.card = k)
      (q := fun J : Finset (E →ₐ[K] AlgebraicClosure K) ↦ J.card = k)
      (by intro J; simp)
    have heq (ω : AS.Ω) :
        (⨆ J : {J : Finset (Fin n) // J.card = k}, ∏ j ∈ J.val, (s ω).ϕ (e j b)) =
        ⨆ J : {J : Finset (E →ₐ[K] AlgebraicClosure K) // J.card = k},
          ∏ σ ∈ J.val, (s ω).ϕ (σ b) := by
      calc
        _ = ⨆ J : {J : Finset (Fin n) // J.card = k},
            ∏ σ ∈ (eJ J).val, (s ω).ϕ (σ b) := by
          apply iSup_congr
          intro J
          simp [eJ, Equiv.subtypeEquiv, Finset.prod_map]
        _ = _ := eJ.iSup_comp (g := fun J ↦ ∏ σ ∈ J.val, (s ω).ϕ (σ b))
    simp_rw [heq]
    apply measurable_iSup_prod_embeddings (AS := AS) K s hs b k
    simpa only [← Fintype.card_congr e, Fintype.card_fin] using hk
  exact measurable_perm_eval_of_measurable_iSup_prod
    (fun ω i ↦ (s ω).ϕ (e i b))
    (fun ω i ↦ (s ω).ϕ.pos ((map_ne_zero (e i)).mpr hb)) π hπ hP i

variable (K) in
/-- The sum of the absolute values of all embeddings of an element of a finite separable
extension is measurable for any choice of extensions to the algebraic closure. -/
theorem measurable_sum_abv_embeddings {E : Type*} [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (s : AS.Ω → ParameterSpaceExtension AS (AlgebraicClosure K))
    (hs : ∀ ω, (s ω).proj = ω) (b : E) :
    Measurable fun ω ↦ ∑ σ : E →ₐ[K] AlgebraicClosure K, (s ω).ϕ (σ b) := by
  classical
  by_cases hb : b = 0
  · simp only [hb, map_zero, Finset.sum_const_zero]
    exact measurable_const
  let n := Fintype.card (E →ₐ[K] AlgebraicClosure K)
  let e : Fin n ≃ (E →ₐ[K] AlgebraicClosure K) := (Fintype.equivFin _).symm
  let x (ω : AS.Ω) (i : Fin n) := (s ω).ϕ (e i b)
  let π (ω : AS.Ω) := Tuple.sort (α := ℝᵒᵈ) (fun i ↦ x ω i)
  have hπ (ω : AS.Ω) : Antitone (x ω ∘ π ω) :=
    Tuple.monotone_sort (α := ℝᵒᵈ) (fun i ↦ x ω i)
  have hm (i : Fin n) : Measurable fun ω ↦ x ω (π ω i) :=
    measurable_ordered_abv_embeddings (AS := AS) K s hs b hb e π hπ i
  have heq (ω : AS.Ω) : (∑ σ : E →ₐ[K] AlgebraicClosure K, (s ω).ϕ (σ b)) =
      ∑ i : Fin n, x ω (π ω i) := by
    rw [Equiv.sum_comp (π ω)]
    exact (e.sum_comp (fun σ ↦ (s ω).ϕ (σ b))).symm
  simp_rw [heq]
  exact Finset.measurable_sum _ (fun i _ ↦ hm i)

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

/-- Real fibre integration is the finite sum with its local-degree weights. -/
theorem fibreIntegral_eq_sum (f : ParameterSpaceExtension AS L → ℝ) (ω : AS.Ω)
    [Fintype (ExtensionFiber AS L ω)] :
    fibreIntegral AS L f ω =
      ∑ x : ExtensionFiber AS L ω, (fibreWeight AS L ω x).toReal * f x.val := by
  unfold fibreIntegral fibreProbabilityMeasure
  rw [integral_sum_measure (integrable_fibre AS L ω _), tsum_fintype]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]

omit [Algebra.IsSeparable K L] in
/-- Nonnegative fibre integration is the finite sum with its local-degree weights. -/
theorem fibreLIntegral_eq_sum (f : ParameterSpaceExtension AS L → ℝ≥0∞) (ω : AS.Ω)
    [Fintype (ExtensionFiber AS L ω)] :
    fibreLIntegral AS L f ω =
      ∑ x : ExtensionFiber AS L ω, fibreWeight AS L ω x * f x.val := by
  unfold fibreLIntegral fibreProbabilityMeasure
  rw [lintegral_sum_measure, tsum_fintype]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

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
  classical
  funext ω
  let E := {w : AbsoluteValue L ℝ // w.restriction K = AS.ϕ ω}
  let D := {w : AbsoluteValue F ℝ // w.restriction K = AS.ϕ ω}
  let : Fintype E := (AbsoluteValue.finite_extensions (L := L) (AS.ϕ ω)).fintype
  let : Fintype D := (AbsoluteValue.finite_extensions (L := F) (AS.ϕ ω)).fintype
  let eL : ExtensionFiber AS L ω ≃ E := {
    toFun x := ⟨x.val.ϕ, x.val.restrict_eq.trans (congrArg AS.ϕ x.property)⟩
    invFun w := ⟨⟨ω, w.val, w.property⟩, rfl⟩
    left_inv x := by
      apply Subtype.ext
      exact ParameterSpaceExtension.ext AS L x.property.symm rfl
    right_inv _ := rfl }
  let eF : ExtensionFiber AS F ω ≃ D := {
    toFun x := ⟨x.val.ϕ, x.val.restrict_eq.trans (congrArg AS.ϕ x.property)⟩
    invFun w := ⟨⟨ω, w.val, w.property⟩, rfl⟩
    left_inv x := by
      apply Subtype.ext
      exact ParameterSpaceExtension.ext AS F x.property.symm rfl
    right_inv _ := rfl }
  let : Fintype (ExtensionFiber AS L ω) := Fintype.ofEquiv E eL.symm
  let : Fintype (ExtensionFiber AS F ω) := Fintype.ofEquiv D eF.symm
  let φ (w : D) : ℝ := f ⟨ω, w.val, w.property⟩
  have hs := AbsoluteValue.sum_localDegree_nsmul_restriction F (AS.ϕ ω) φ
  simp only [nsmul_eq_mul] at hs
  have hl :
      ∑ x : ExtensionFiber AS L ω, (x.val.ϕ.localDegree K : ℝ) * f (restrict AS L x.val F) =
        ∑ w : E, (w.val.localDegree K : ℝ) * φ ⟨w.val.restriction F, w.property⟩ := by
    rw [← eL.sum_comp (fun w ↦ (w.val.localDegree K : ℝ) *
      φ ⟨w.val.restriction F, w.property⟩)]
    apply Finset.sum_congr rfl
    intro x _
    apply congrArg ((x.val.ϕ.localDegree K : ℝ) * ·)
    apply congrArg f
    exact ParameterSpaceExtension.ext AS F x.property rfl
  have hr :
      ∑ x : ExtensionFiber AS F ω, (x.val.ϕ.localDegree K : ℝ) * f x.val =
        ∑ w : D, (w.val.localDegree K : ℝ) * φ w := by
    rw [← eF.sum_comp (fun w ↦ (w.val.localDegree K : ℝ) * φ w)]
    apply Finset.sum_congr rfl
    intro x _
    apply congrArg ((x.val.ϕ.localDegree K : ℝ) * ·)
    apply congrArg f
    exact ParameterSpaceExtension.ext AS F x.property rfl
  rw [fibreIntegral_eq_sum, fibreIntegral_eq_sum]
  simp only [fibreWeight, ENNReal.toReal_div, ENNReal.toReal_natCast,
    div_mul_eq_mul_div, ← Finset.sum_div]
  rw [hl, hr, hs]
  have hd : (Module.finrank K L : ℝ) =
      (Module.finrank K F : ℝ) * (Module.finrank F L : ℝ) := by
    exact_mod_cast (Module.finrank_mul_finrank K F L).symm
  rw [hd]
  have hn : (Module.finrank F L : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := F) (M := L)).ne'
  rw [mul_comm (Module.finrank K F : ℝ), mul_div_mul_left _ _ hn]


/-- The local-degree weighted evaluation integral is the normalized average over
embeddings into an algebraic closure, for any extension of the base absolute value. -/
theorem fibreIntegral_eval_eq_sum_embeddings (ω : AS.Ω)
    (u : AbsoluteValue (AlgebraicClosure K) ℝ) (hu : u.restriction K = AS.ϕ ω)
    (b : L) :
    fibreIntegral AS L (fun x ↦ x.ϕ b) ω =
      (Module.finrank K L : ℝ)⁻¹ * ∑ σ : L →ₐ[K] AlgebraicClosure K, u (σ b) := by
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
  rw [fibreIntegral_eq_sum]
  simp only [fibreWeight, ENNReal.toReal_div, ENNReal.toReal_natCast]
  calc
    _ = (Module.finrank K L : ℝ)⁻¹ *
        ∑ x : ExtensionFiber AS L ω, (x.val.ϕ.localDegree K : ℝ) * x.val.ϕ b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (Module.finrank K L : ℝ)⁻¹ * ∑ w : E, (w.val.localDegree K : ℝ) * w.val b := by
      congr 1
      exact e.sum_comp (fun w ↦ (w.val.localDegree K : ℝ) * w.val b)
    _ = _ := by
      congr 1
      convert AbsoluteValue.sum_localDegree_nsmul_eq_sum_embeddings (AS.ϕ ω) u hu
        (fun w : AbsoluteValue L ℝ ↦ w b) using 1 <;> simp [nsmul_eq_mul, E]
      rfl

/-- Evaluation functions have measurable fibre integrals. -/
theorem measurable_fibreIntegral_eval (b : L) :
    Measurable (fibreIntegral AS L (fun x ↦ x.ϕ b)) := by
  classical
  choose u hu using fun ω : AS.Ω ↦
    AbsoluteValue.exists_extension (L := AlgebraicClosure K) (AS.ϕ ω)
  let s (ω : AS.Ω) : ParameterSpaceExtension AS (AlgebraicClosure K) := ⟨ω, u ω, hu ω⟩
  have hs (ω : AS.Ω) : (s ω).proj = ω := rfl
  have heq (ω : AS.Ω) :
      fibreIntegral AS L (fun x ↦ x.ϕ b) ω =
        (Module.finrank K L : ℝ)⁻¹ * ∑ σ : L →ₐ[K] AlgebraicClosure K, (s ω).ϕ (σ b) :=
    fibreIntegral_eval_eq_sum_embeddings AS L ω (s ω).ϕ
      ((ϕ_restriction AS (AlgebraicClosure K) (s ω)).trans (congrArg AS.ϕ (hs ω))) b
  change Measurable fun ω ↦ fibreIntegral AS L (fun x ↦ x.ϕ b) ω
  simp_rw [heq]
  exact (measurable_sum_abv_embeddings K AS s hs b).const_mul _

/-- Finite-fibre integration preserves pointwise sequential limits of real functions. -/
theorem tendsto_fibreIntegral (f : ℕ → ParameterSpaceExtension AS L → ℝ)
    (g : ParameterSpaceExtension AS L → ℝ)
    (hf : ∀ x, Filter.Tendsto (fun n ↦ f n x) Filter.atTop (nhds (g x)))
    (ω : AS.Ω) :
    Filter.Tendsto (fun n ↦ fibreIntegral AS L (f n) ω) Filter.atTop
      (nhds (fibreIntegral AS L g ω)) := by
  let : Finite (ExtensionFiber AS L ω) := finite_extensionFiber AS L ω
  let : Fintype (ExtensionFiber AS L ω) := Fintype.ofFinite _
  simp_rw [fibreIntegral_eq_sum]
  exact tendsto_finsetSum _ (fun x _ ↦ tendsto_const_nhds.mul (hf x.val))

omit _s in
/-- Nonnegative fibre integration preserves increasing sequential suprema. -/
theorem fibreLIntegral_iSup (f : ℕ → ParameterSpaceExtension AS L → ℝ≥0∞)
    (hf : Monotone f) :
    fibreLIntegral AS L (fun x ↦ ⨆ n, f n x) =
      fun ω ↦ ⨆ n, fibreLIntegral AS L (f n) ω := by
  funext ω
  let : Finite (ExtensionFiber AS L ω) := finite_extensionFiber AS L ω
  exact lintegral_iSup (fun n ↦ measurable_of_finite (fun x : ExtensionFiber AS L ω ↦ f n x.val))
    (fun n m h x ↦ hf h x.val)

omit _s in
/-- Nonnegative fibre integration preserves countable sums. -/
theorem fibreLIntegral_tsum (f : ℕ → ParameterSpaceExtension AS L → ℝ≥0∞) :
    fibreLIntegral AS L (fun x ↦ ∑' n, f n x) =
      fun ω ↦ ∑' n, fibreLIntegral AS L (f n) ω := by
  funext ω
  let : Finite (ExtensionFiber AS L ω) := finite_extensionFiber AS L ω
  exact lintegral_tsum (fun n ↦
    (measurable_of_finite (fun x : ExtensionFiber AS L ω ↦ f n x.val)).aemeasurable)

/-- Chen--Moriwaki, Theorem 3.3.4: for finite separable `L/K`, the fibre integration operator
sends measurable real-valued functions on `Ω_L` to measurable real-valued functions on `Ω_K`. -/
theorem measurable_fibreIntegral {f : ParameterSpaceExtension AS L → ℝ} (hf : Measurable f) :
    Measurable (fibreIntegral AS L f) := by
 classical
  let H : Submodule ℝ (ParameterSpaceExtension AS L → ℝ) := {
    carrier := {f | Measurable (fibreIntegral AS L f)}
    zero_mem' := by
      change Measurable fun ω : AS.Ω ↦
        ∫ _x : ExtensionFiber AS L ω, (0 : ℝ) ∂fibreProbabilityMeasure AS L ω
      simp only [integral_zero]
      exact measurable_const
    add_mem' := fun hf hg ↦ by
      change Measurable (fibreIntegral AS L (_ + _))
      rw [fibreIntegral_add]
      exact hf.add hg
    smul_mem' := fun c f hf ↦ by
      change Measurable (fibreIntegral AS L (c • f))
      rw [fibreIntegral_smul]
      exact hf.const_smul c }
  have hH : IsSeqClosed (H : Set (ParameterSpaceExtension AS L → ℝ)) := by
    intro u f hu hf
    exact measurable_of_tendsto_metrizable hu (tendsto_pi_nhds.mpr fun ω ↦
      tendsto_fibreIntegral AS L u f (fun x ↦ tendsto_pi_nhds.mp hf x) ω)
  let C : Set (ParameterSpaceExtension AS L → ℝ) :=
    Set.range (fun p : L × {φ : AS.Ω → ℝ // Measurable φ} ↦
      fun x : ParameterSpaceExtension AS L ↦ x.ϕ p.1 * p.2.val x.proj)
  have h1 : (1 : ParameterSpaceExtension AS L → ℝ) ∈ C := by
    refine ⟨⟨1, ⟨fun _ ↦ 1, measurable_const⟩⟩, ?_⟩
    ext x
    simp
  have hmul : ∀ f ∈ C, ∀ g ∈ C, f * g ∈ C := by
    rintro f ⟨⟨b, φ⟩, rfl⟩ g ⟨⟨c, ψ⟩, rfl⟩
    refine ⟨⟨b * c, ⟨φ.val * ψ.val, φ.property.mul ψ.property⟩⟩, ?_⟩
    ext x
    simp only [Pi.mul_apply, map_mul]
    ring
  have hCH : C ⊆ H := by
    rintro f ⟨⟨b, φ⟩, rfl⟩
    change Measurable (fibreIntegral AS L (fun x ↦ x.ϕ b * φ.val x.proj))
    have heq : (fun x : ParameterSpaceExtension AS L ↦ x.ϕ b * φ.val x.proj) =
        fun x ↦ φ.val x.proj * x.ϕ b := by
      ext x
      exact mul_comm _ _
    rw [heq, fibreIntegral_comp_proj_mul]
    exact φ.property.mul (measurable_fibreIntegral_eval AS L b)
  have hm : (inferInstance : MeasurableSpace (ParameterSpaceExtension AS L)) =
      ⨆ g : C, MeasurableSpace.comap g.val inferInstance := by
    rw [measurableSpace_eq_iSup_comap_eval_mul_base AS L]
    apply le_antisymm
    · apply iSup_le
      intro b
      apply iSup_le
      intro φ
      exact le_iSup_of_le ⟨_, ⟨⟨b, φ⟩, rfl⟩⟩ le_rfl
    · apply iSup_le
      intro g
      obtain ⟨⟨b, φ⟩, hg⟩ := g.property
      rw [← hg]
      exact le_iSup_of_le b (le_iSup_of_le φ le_rfl)
  apply MeasureTheory.measurable_mem_of_isSeqClosed H hH h1 hmul hCH
  exact hm ▸ hf

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

/-- Formula (3.10): the fibre integral of a logarithmic evaluation is the logarithm
of its field norm divided by the extension degree. -/
theorem fibreIntegral_log_eq_log_norm (b : L) (hb : b ≠ 0) (ω : AS.Ω) :
    fibreIntegral AS L (fun x ↦ Real.log (ϕ x b)) ω =
      Real.log (AS.ϕ ω (Algebra.norm K b)) / (Module.finrank K L : ℝ) := by
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
  rw [fibreIntegral_eq_sum]
  simp only [fibreWeight, ENNReal.toReal_div, ENNReal.toReal_natCast,
    div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  have hp : AS.ϕ ω (Algebra.norm K b) =
      ∏ x : ExtensionFiber AS L ω, x.val.ϕ b ^ x.val.ϕ.localDegree K :=
    (AbsoluteValue.apply_norm_eq_prod (AS.ϕ ω) b).trans
      (e.prod_comp (fun w ↦ w.val b ^ w.val.localDegree K)).symm
  rw [hp, Real.log_prod (fun x _ ↦ pow_ne_zero _ (x.val.ϕ.ne_zero hb))]
  simp only [Real.log_pow]

/-- Chen--Moriwaki, Theorem 3.3.7(4): logarithmic evaluations are integrable for the measure
defined in Definition 3.3.6. -/
theorem integrable_log_inducedMeasure (a : L) (ha : a ≠ 0) :
    Integrable
      (fun x : ParameterSpaceExtension AS L ↦ Real.log ((ParameterSpaceExtension.ϕ x) a))
      (inducedMeasure AS L) := by
  let p := minpoly K a
  have hp : p.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral a)
  let h : AS.Ω → ℝ := fun ω ↦
    Real.log (p.natDegree : ℝ) * AS.κ ω + AS.coefficientLogBound p ω
  have hm : Measurable h := AS.measurable_logarithmicRootBound p
  have hi : Integrable h AS.v := AS.integrable_logarithmicRootBound p
  let u : ParameterSpaceExtension AS L → ℝ := fun x ↦ h (proj x) - Real.log (ϕ x a)
  have um : Measurable u := (hm.comp (measurable_proj AS L)).sub (measurable_log AS L a)
  have un (x : ParameterSpaceExtension AS L) : 0 ≤ u x := by
    exact sub_nonneg.mpr (AS.log_apply_le_rootBound p hp a
      (minpoly.aeval K a) ha (proj x) (ϕ x) (ϕ_restriction AS L x))
  have uint : Integrable u (inducedMeasure AS L) := by
    apply (integrable_inducedMeasure_iff AS L um).mpr
    have heq : (fibreIntegral AS L fun x ↦ |u x|) =
        fun ω ↦ h ω -
          Real.log (AS.ϕ ω (Algebra.norm K a)) / (Module.finrank K L : ℝ) := by
      funext ω
      simp_rw [abs_of_nonneg (un _)]
      change (∫ x : ExtensionFiber AS L ω, u x.val
        ∂fibreProbabilityMeasure AS L ω) = _
      rw [show (fun x : ExtensionFiber AS L ω ↦ u x.val) =
        (fun x ↦ h (proj x.val) - Real.log (ϕ x.val a)) from rfl]
      rw [integral_sub (integrable_fibre AS L ω _) (integrable_fibre AS L ω _)]
      change fibreIntegral AS L (fun x ↦ h (proj x)) ω -
        fibreIntegral AS L (fun x ↦ Real.log (ϕ x a)) ω = _
      rw [fibreIntegral_comp_proj, fibreIntegral_log_eq_log_norm AS L a ha]
    rw [heq]
    exact hi.sub ((AS.integrable_log (Algebra.norm K a)
      (Algebra.norm_ne_zero_iff.mpr ha)).div_const _)
  have hmp : MeasurePreserving (proj (AS := AS) (L := L))
      (inducedMeasure AS L) AS.v :=
    ⟨measurable_proj AS L, map_inducedMeasure_proj AS L⟩
  have hc := hmp.integrable_comp_of_integrable hi
  convert hc.sub uint using 1
  funext x
  dsimp [u, Function.comp_def]
  ring

/-- Chen--Moriwaki, Theorem 3.3.7(5), formula (3.9): the logarithmic integral against the
induced measure computes the logarithm of the norm form:
`[K' : K] ∫ ln |b|_x dν_{K'} = ∫ ln |N_{K'/K}(b)|_ω dν_K`. -/
theorem finrank_mul_integral_log_inducedMeasure (b : L) (hb : b ≠ 0) :
    (Module.finrank K L : ℝ) * ∫ x, Real.log (ϕ x b) ∂inducedMeasure AS L =
      ∫ ω, Real.log (AS.ϕ ω (Algebra.norm K b)) ∂AS.v := by
  rw [integral_inducedMeasure AS L (integrable_log_inducedMeasure AS L b hb)]
  simp_rw [fibreIntegral_log_eq_log_norm (AS := AS) (L := L) b hb]
  rw [integral_div]
  exact mul_div_cancel₀ _ (by exact_mod_cast (Module.finrank_pos (R := K) (M := L)).ne')

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
  have : IsScalarTower B D w.Completion := isScalarTower_completion_restriction w E
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
    have : IsScalarTower B D w.Completion := isScalarTower_completion_restriction w E
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

omit [Algebra.IsAlgebraic K L] in
/-- Evaluation gives each fibre its natural topology of pointwise convergence. -/
instance instTopologicalSpaceBaseFiber (ω : AS.Ω) : TopologicalSpace (BaseFiber L ω) :=
  TopologicalSpace.induced (fun x : BaseFiber L ω ↦ (x.val.abv : L → ℝ)) inferInstance

omit [Algebra.IsAlgebraic K L] in
/-- Absolute values on a fixed fibre are determined by all their evaluations. -/
theorem isEmbedding_fibreEval (ω : AS.Ω) :
    Topology.IsEmbedding (fun x : BaseFiber L ω ↦ (x.val.abv : L → ℝ)) := by
  refine ⟨⟨rfl⟩, ?_⟩
  intro x y hxy
  apply Subtype.ext
  exact ParameterSpaceExtension.ext AS L (x.property.trans y.property.symm)
    (DFunLike.coe_injective hxy)

omit [Algebra.IsAlgebraic K L] in
instance instT2SpaceBaseFiber (ω : AS.Ω) : T2Space (BaseFiber L ω) :=
  (isEmbedding_fibreEval AS L ω).t2Space

/-- Algebraic fibres are compact in the evaluation topology. -/
instance instCompactSpaceBaseFiber (ω : AS.Ω) :
    CompactSpace (BaseFiber L ω) := by
  constructor
  apply (isEmbedding_fibreEval AS L ω).isCompact_iff.mpr
  rw [Set.image_univ]
  have hr : Set.range (fun x : BaseFiber L ω ↦ (x.val.abv : L → ℝ)) =
      Set.range (fun w : {w : AbsoluteValue L ℝ // w.restriction K = AS.ϕ ω} ↦
        (w.val : L → ℝ)) := by
    ext f
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x.val.abv, x.val.restrict_eq.trans (congrArg AS.ϕ x.property)⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨⟨⟨ω, w.val, w.property⟩, rfl⟩, rfl⟩
  rw [hr]
  exact AbsoluteValue.isCompact_range_extensions (AS.ϕ ω)

variable {AS L} in
/-- Restriction from the algebraic fibre `M_{L,ω}` to the finite fibre attached to `F`. -/
def projFiniteFiber (F : FiniteIntermediateField K L) (ω : AS.Ω) :
    BaseFiber L ω → FiniteBaseFiber L F ω :=
  fun x ↦ ⟨projFinite AS F x.1, by
    simpa [projFinite, ParameterSpaceFinExtension, ParameterSpaceExtension.proj,
      ParameterSpaceExtension.restrict] using x.2⟩

omit [Algebra.IsAlgebraic K L] in
/-- Restriction to a finite fibre is continuous for the evaluation topologies. -/
theorem continuous_projFiniteFiber (F : FiniteIntermediateField K L) (ω : AS.Ω) :
    Continuous (projFiniteFiber F ω) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro a
  exact (continuous_apply ((a : F.1) : L)).comp continuous_induced_dom

omit [Algebra.IsAlgebraic K L] in
/-- Finite-stage cylinders are clopen in an algebraic fibre. -/
theorem isClopen_fibreCylinder (F : FiniteIntermediateField K L) (ω : AS.Ω)
    (B : Set (FiniteBaseFiber L F ω)) :
    IsClopen (projFiniteFiber F ω ⁻¹' B) := by
  let := ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K F.1) ω
  exact ⟨(isClosed_discrete B).preimage (continuous_projFiniteFiber AS L F ω),
    (isOpen_discrete B).preimage (continuous_projFiniteFiber AS L F ω)⟩

/-- Finite-stage cylinders are compact. -/
theorem isCompact_fibreCylinder
    (F : FiniteIntermediateField K L) (ω : AS.Ω)
    (B : Set (FiniteBaseFiber L F ω)) :
    IsCompact (projFiniteFiber F ω ⁻¹' B) :=
  (isClopen_fibreCylinder AS L F ω B).isClosed.isCompact

/-- Every finite-stage fibre point lifts to the algebraic fibre. -/
theorem surjective_projFiniteFiber (F : FiniteIntermediateField K L) (ω : AS.Ω) :
    Function.Surjective (projFiniteFiber (AS := AS) F ω) := by
  intro x
  let v := ParameterSpaceFinExtension.extendAbsoluteValue x.val.abv
  obtain ⟨w, hw⟩ := AbsoluteValue.exists_extension (L := L) v
  have hE : (w.restriction F.1).restriction (separableClosure K F.1) = x.val.abv := by
    rw [hw]
    exact ParameterSpaceFinExtension.restriction_extendAbsoluteValue _
  have hbase : w.restriction K = AS.ϕ ω := by
    ext a
    have h := congrArg (fun z : AbsoluteValue (separableClosure K F.1) ℝ ↦
      z (algebraMap K (separableClosure K F.1) a)) hE
    exact h.trans ((congrArg (fun z : AbsoluteValue K ℝ ↦ z a) x.val.restrict_eq).trans
      (congrArg (fun z ↦ AS.ϕ z a) x.property))
  refine ⟨⟨⟨ω, w, hbase⟩, rfl⟩, ?_⟩
  apply Subtype.ext
  exact ParameterSpaceExtension.ext AS (separableClosure K F.1) x.property.symm hE

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

omit [Algebra.IsAlgebraic K L] in
/-- Finite-stage projection preserves the probability measure on each fibre. -/
theorem map_finiteFibreProbabilityMeasure_projFiniteFiberOfLE (ω : AS.Ω)
    {F G : FiniteIntermediateField K L} (hFG : F.1 ≤ G.1) :
    Measure.map (projFiniteFiberOfLE hFG ω)
        (ParameterSpaceFinExtension.fibreProbabilityMeasure AS G ω) =
      ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω := by
  classical
  let F₀ := separableClosure K F.1
  let G₀ := separableClosure K G.1
  let i : F₀ →ₐ[K] G₀ := finiteSeparableInclusion hFG
  let q := projFiniteFiberOfLE (AS := AS) hFG ω
  let EF := {w : AbsoluteValue F₀ ℝ // w.restriction K = AS.ϕ ω}
  let EG := {w : AbsoluteValue G₀ ℝ // w.restriction K = AS.ϕ ω}
  let : Fintype EF := (AbsoluteValue.finite_extensions (L := F₀) (AS.ϕ ω)).fintype
  let : Fintype EG := (AbsoluteValue.finite_extensions (L := G₀) (AS.ϕ ω)).fintype
  let eF : FiniteBaseFiber L F ω ≃ EF := {
    toFun x := ⟨x.val.abv, x.val.restrict_eq.trans (congrArg AS.ϕ x.property)⟩
    invFun w := ⟨⟨ω, w.val, w.property⟩, rfl⟩
    left_inv x := by
      apply Subtype.ext
      exact ParameterSpaceExtension.ext AS F₀ x.property.symm rfl
    right_inv _ := rfl }
  let eG : FiniteBaseFiber L G ω ≃ EG := {
    toFun x := ⟨x.val.abv, x.val.restrict_eq.trans (congrArg AS.ϕ x.property)⟩
    invFun w := ⟨⟨ω, w.val, w.property⟩, rfl⟩
    left_inv x := by
      apply Subtype.ext
      exact ParameterSpaceExtension.ext AS G₀ x.property.symm rfl
    right_inv _ := rfl }
  let : Fintype (FiniteBaseFiber L F ω) := Fintype.ofEquiv EF eF.symm
  let : Fintype (FiniteBaseFiber L G ω) := Fintype.ofEquiv EG eG.symm
  have : IsProbabilityMeasure (ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω) :=
    ParameterSpaceExtension.isProbabilityMeasure_fibreProbabilityMeasure AS F₀ ω
  have : IsProbabilityMeasure (ParameterSpaceFinExtension.fibreProbabilityMeasure AS G ω) :=
    ParameterSpaceExtension.isProbabilityMeasure_fibreProbabilityMeasure AS G₀ ω
  have hint (g : FiniteBaseFiber L F ω → ℝ) :
      (∫ x, g (q x) ∂ParameterSpaceFinExtension.fibreProbabilityMeasure AS G ω) =
        ∫ x, g x ∂ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω := by
    let φ (a : AbsoluteValue F₀ ℝ) : ℝ :=
      if h : a.restriction K = AS.ϕ ω then g ⟨⟨ω, a, h⟩, rfl⟩ else 0
    have hF (x : FiniteBaseFiber L F ω) : φ x.val.abv = g x := by
      have hx : x.val.abv.restriction K = AS.ϕ ω :=
        x.val.restrict_eq.trans (congrArg AS.ϕ x.property)
      rw [show φ x.val.abv = _ from dif_pos hx]
      apply congrArg g
      apply Subtype.ext
      exact ParameterSpaceExtension.ext AS F₀ x.property.symm rfl
    have hG (x : FiniteBaseFiber L G ω) :
        φ (x.val.abv.pullback i.toRingHom) = g (q x) := hF (q x)
    have hw := AbsoluteValue.finrank_nsmul_sum_localDegree_pullback i (AS.ϕ ω) φ
    rw [← eG.sum_comp (fun w ↦ w.val.localDegree K • φ (w.val.pullback i.toRingHom)),
      ← eF.sum_comp (fun w ↦ w.val.localDegree K • φ w.val)] at hw
    change Module.finrank K F₀ •
        (∑ x : FiniteBaseFiber L G ω, x.val.abv.localDegree K •
          φ (x.val.abv.pullback i.toRingHom)) =
      Module.finrank K G₀ •
        ∑ x : FiniteBaseFiber L F ω, x.val.abv.localDegree K • φ x.val.abv at hw
    simp only [nsmul_eq_mul] at hw
    simp_rw [hF, hG] at hw
    unfold ParameterSpaceFinExtension.fibreProbabilityMeasure
      ParameterSpaceExtension.fibreProbabilityMeasure
    rw [integral_sum_measure (ParameterSpaceExtension.integrable_fibre AS G₀ ω (fun x ↦ g (q x))),
      integral_sum_measure (ParameterSpaceExtension.integrable_fibre AS F₀ ω g)]
    simp only [tsum_fintype, integral_smul_measure, integral_dirac, smul_eq_mul,
      ParameterSpaceExtension.fibreWeight, ENNReal.toReal_div, ENNReal.toReal_natCast,
      div_mul_eq_mul_div, ← Finset.sum_div]
    apply (div_eq_div_iff
      (by exact_mod_cast (Module.finrank_pos (R := K) (M := G₀)).ne')
      (by exact_mod_cast (Module.finrank_pos (R := K) (M := F₀)).ne')).mpr
    simpa only [ParameterSpaceExtension.ϕ, mul_comm] using hw
  apply Measure.ext
  intro s hs
  have hq : Measurable q := measurable_of_countable q
  rw [Measure.map_apply hq hs]
  have hi := hint (s.indicator fun _ ↦ 1)
  have hpre : MeasurableSet (q ⁻¹' s) := hq hs
  simp only [← Set.indicator_comp_right, Function.comp_def] at hi
  rw [show (fun _ : FiniteBaseFiber L G ω ↦ (1 : ℝ)) = 1 from rfl,
    show (fun _ : FiniteBaseFiber L F ω ↦ (1 : ℝ)) = 1 from rfl,
    integral_indicator_one hpre, integral_indicator_one hs] at hi
  calc
    _ = ENNReal.ofReal
        ((ParameterSpaceFinExtension.fibreProbabilityMeasure AS G ω) (q ⁻¹' s)).toReal :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = ENNReal.ofReal ((ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω) s).toReal :=
      congrArg ENNReal.ofReal hi
    _ = _ := ENNReal.ofReal_toReal (measure_ne_top _ _)

omit [Algebra.IsAlgebraic K L] in
/-- Every point of a finite-stage fibre lifts along a larger finite stage. -/
theorem surjective_projFiniteFiberOfLE (ω : AS.Ω)
    {F G : FiniteIntermediateField K L} (hFG : F.1 ≤ G.1) :
    Function.Surjective (projFiniteFiberOfLE (AS := AS) hFG ω) := by
  let F₀ := separableClosure K F.1
  let G₀ := separableClosure K G.1
  let i : F₀ →ₐ[K] G₀ := finiteSeparableInclusion hFG
  let : Algebra F₀ G₀ := i.toRingHom.toAlgebra
  have : IsScalarTower K F₀ G₀ :=
    IsScalarTower.of_algebraMap_eq (fun a ↦ (i.commutes a).symm)
  have : FiniteDimensional F₀ G₀ := Module.Finite.of_restrictScalars_finite K F₀ G₀
  intro x
  obtain ⟨w, hw⟩ := AbsoluteValue.exists_extension (L := G₀) x.val.abv
  have hbase : w.restriction K = AS.ϕ ω := by
    ext a
    have h := congrArg (fun z : AbsoluteValue F₀ ℝ ↦ z (algebraMap K F₀ a)) hw
    change w (i (algebraMap K F₀ a)) = x.val.abv (algebraMap K F₀ a) at h
    rw [i.commutes] at h
    exact h.trans ((congrArg (fun z : AbsoluteValue K ℝ ↦ z a) x.val.restrict_eq).trans
      (congrArg (fun z ↦ AS.ϕ z a) x.property))
  refine ⟨⟨⟨ω, w, hbase⟩, rfl⟩, ?_⟩
  apply Subtype.ext
  exact ParameterSpaceExtension.ext AS F₀ x.property.symm hw

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
  let H := FiniteIntermediateField.sup d₁.F d₂.F
  let := ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K H.1) ω
  have hint (d : DescendsToFiniteFiber ω f) (h : d.F.1 ≤ H.1) :
      fibreCylinderIntegral d = ∫ y, d.g (projFiniteFiberOfLE h ω y)
        ∂ParameterSpaceFinExtension.fibreProbabilityMeasure AS H ω := by
    let := ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K d.F.1) ω
    rw [fibreCylinderIntegral,
      ← map_finiteFibreProbabilityMeasure_projFiniteFiberOfLE AS L ω h]
    exact integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable d.g).aestronglyMeasurable
  rw [hint d₁ (FiniteIntermediateField.left_le_sup d₁.F d₂.F),
    hint d₂ (FiniteIntermediateField.right_le_sup d₁.F d₂.F)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  obtain ⟨x, rfl⟩ := surjective_projFiniteFiber AS L H ω y
  simp only [H, projFiniteFiberOfLE_projFiniteFiber]
  exact (congrFun d₁.eq_comp x).symm.trans (congrFun d₂.eq_comp x)

/-- The sets represented at a finite stage of an algebraic fibre. -/
def fibreCylinders (ω : AS.Ω) : Set (Set (BaseFiber L ω)) :=
  {A | ∃ (F : FiniteIntermediateField K L) (B : Set (FiniteBaseFiber L F ω)),
    projFiniteFiber F ω ⁻¹' B = A}

omit [Algebra.IsAlgebraic K L] in
/-- Finite-stage cylinders form an algebra of sets. -/
theorem isSetAlgebra_fibreCylinders (ω : AS.Ω) :
    IsSetAlgebra (fibreCylinders AS L ω) := by
  constructor
  · exact ⟨FiniteIntermediateField.bot, ∅, rfl⟩
  · rintro A ⟨F, B, rfl⟩
    exact ⟨F, Bᶜ, rfl⟩
  · rintro A B ⟨F, C, rfl⟩ ⟨G, D, rfl⟩
    refine ⟨FiniteIntermediateField.sup F G,
      (projFiniteFiberOfLE (FiniteIntermediateField.left_le_sup F G) ω ⁻¹' C) ∪
      (projFiniteFiberOfLE (FiniteIntermediateField.right_le_sup F G) ω ⁻¹' D), ?_⟩
    ext x
    simp only [Set.mem_preimage, Set.mem_union, projFiniteFiberOfLE_projFiniteFiber]

omit [Algebra.IsAlgebraic K L] in
/-- The prescribed fibre σ-algebra is generated by the finite-stage cylinders. -/
theorem fibreMeasurableSpace_eq_generateFrom (ω : AS.Ω) :
    fibreMeasurableSpace L ω = MeasurableSpace.generateFrom (fibreCylinders AS L ω) := by
  apply le_antisymm
  · refine iSup_le fun F ↦ ?_
    rintro A ⟨B, _, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom ⟨F, B, rfl⟩
  · apply MeasurableSpace.generateFrom_le
    rintro A ⟨F, B, rfl⟩
    exact le_iSup (fun F : FiniteIntermediateField K L ↦
      MeasurableSpace.comap (projFiniteFiber F ω) inferInstance) F
        _ ⟨B, measurableSet_finiteBaseFiber AS L F ω B, rfl⟩

omit [Algebra.IsAlgebraic K L] in
/-- Finite-stage fibre projections are measurable for the cylinder σ-algebra. -/
theorem measurable_projFiniteFiber (ω : AS.Ω) (F : FiniteIntermediateField K L) :
    Measurable[fibreMeasurableSpace L ω] (projFiniteFiber F ω) :=
  Measurable.of_comap_le (le_iSup (fun F : FiniteIntermediateField K L ↦
    MeasurableSpace.comap (projFiniteFiber F ω) inferInstance) F)

/-- The cylinder content on the fibre `M_{L,ω}`: the infimum of the prescribed finite-stage
fibre measures over cylinder supersets. On a cylinder set `(π_{L/F,ω})⁻¹(B)` it takes the
prescribed value `P_{F,ω}(B)`; this is the additive set function extended by Carathéodory's
theorem in the proof of Proposition 3.4.6. -/
noncomputable def fibreCylinderContent (ω : AS.Ω) (A : Set (BaseFiber L ω)) : ℝ≥0∞ :=
  ⨅ (F : FiniteIntermediateField K L) (B : Set (FiniteBaseFiber L F ω))
    (_ : A ⊆ projFiniteFiber F ω ⁻¹' B),
    ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω B

omit [Algebra.IsAlgebraic K L] in
/-- The empty cylinder has zero content. -/
theorem fibreCylinderContent_empty (ω : AS.Ω) : fibreCylinderContent AS L ω ∅ = 0 := by
  apply le_antisymm _ zero_le
  exact iInf_le_of_le FiniteIntermediateField.bot
    (iInf_le_of_le ∅ (iInf_le_of_le (Set.empty_subset _) (by simp)))

/-- Inclusion of cylinders implies the corresponding inequality of finite-stage masses. -/
theorem finiteFibreProbabilityMeasure_le_of_preimage_subset (ω : AS.Ω)
    (F G : FiniteIntermediateField K L) (B : Set (FiniteBaseFiber L F ω))
    (C : Set (FiniteBaseFiber L G ω))
    (hBC : projFiniteFiber F ω ⁻¹' B ⊆ projFiniteFiber G ω ⁻¹' C) :
    ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω B ≤
      ParameterSpaceFinExtension.fibreProbabilityMeasure AS G ω C := by
  let H := FiniteIntermediateField.sup F G
  let qF := projFiniteFiberOfLE (FiniteIntermediateField.left_le_sup F G) ω
  let qG := projFiniteFiberOfLE (FiniteIntermediateField.right_le_sup F G) ω
  have hsub : qF ⁻¹' B ⊆ qG ⁻¹' C := by
    intro y hy
    obtain ⟨x, rfl⟩ := surjective_projFiniteFiber AS L H ω y
    exact hBC (by simpa [qF, H, projFiniteFiberOfLE_projFiniteFiber] using hy)
  let := ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K H.1) ω
  have hF := congrArg (fun μ : Measure (FiniteBaseFiber L F ω) ↦ μ B)
    (map_finiteFibreProbabilityMeasure_projFiniteFiberOfLE AS L ω
      (FiniteIntermediateField.left_le_sup F G))
  have hG := congrArg (fun μ : Measure (FiniteBaseFiber L G ω) ↦ μ C)
    (map_finiteFibreProbabilityMeasure_projFiniteFiberOfLE AS L ω
      (FiniteIntermediateField.right_le_sup F G))
  rw [Measure.map_apply (measurable_of_countable _)
    (measurableSet_finiteBaseFiber AS L F ω B)] at hF
  rw [Measure.map_apply (measurable_of_countable _)
    (measurableSet_finiteBaseFiber AS L G ω C)] at hG
  rw [← hF, ← hG]
  exact measure_mono hsub

/-- The cylinder content agrees with each prescribed finite-stage probability. -/
theorem fibreCylinderContent_preimage (ω : AS.Ω) (F : FiniteIntermediateField K L)
    (B : Set (FiniteBaseFiber L F ω)) :
    fibreCylinderContent AS L ω (projFiniteFiber F ω ⁻¹' B) =
      ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω B := by
  apply le_antisymm
  · exact iInf_le_of_le F (iInf_le_of_le B (iInf_le_of_le (Set.Subset.refl _) le_rfl))
  · exact le_iInf fun G ↦ le_iInf fun C ↦ le_iInf fun hBC ↦
      finiteFibreProbabilityMeasure_le_of_preimage_subset AS L ω F G B C hBC

/-- Cylinder content is additive on disjoint cylinders. -/
theorem fibreCylinderContent_union (ω : AS.Ω) {A B : Set (BaseFiber L ω)}
    (hA : A ∈ fibreCylinders AS L ω) (hB : B ∈ fibreCylinders AS L ω)
    (hdisj : Disjoint A B) :
    fibreCylinderContent AS L ω (A ∪ B) =
      fibreCylinderContent AS L ω A + fibreCylinderContent AS L ω B := by
  obtain ⟨F, C, rfl⟩ := hA
  obtain ⟨G, D, rfl⟩ := hB
  let H := FiniteIntermediateField.sup F G
  let C' := projFiniteFiberOfLE (FiniteIntermediateField.left_le_sup F G) ω ⁻¹' C
  let D' := projFiniteFiberOfLE (FiniteIntermediateField.right_le_sup F G) ω ⁻¹' D
  have hC : projFiniteFiber H ω ⁻¹' C' = projFiniteFiber F ω ⁻¹' C := by
    ext x
    simp only [C', H, Set.mem_preimage, projFiniteFiberOfLE_projFiniteFiber]
  have hD : projFiniteFiber H ω ⁻¹' D' = projFiniteFiber G ω ⁻¹' D := by
    ext x
    simp only [D', H, Set.mem_preimage, projFiniteFiberOfLE_projFiniteFiber]
  have hCD : Disjoint C' D' := by
    rw [Set.disjoint_left] at hdisj ⊢
    intro y hyC hyD
    obtain ⟨x, rfl⟩ := surjective_projFiniteFiber AS L H ω y
    exact hdisj ((Set.ext_iff.mp hC x).mp hyC) ((Set.ext_iff.mp hD x).mp hyD)
  rw [← hC, ← hD, ← Set.preimage_union]
  simp only [fibreCylinderContent_preimage]
  exact measure_union hCD (measurableSet_finiteBaseFiber AS L H ω D')

/-- The cylinder content, restricted to the cylinder algebra, is additive. -/
noncomputable def fibreCylinderAddContent (ω : AS.Ω) :
    AddContent ℝ≥0∞ (fibreCylinders AS L ω) :=
  (isSetAlgebra_fibreCylinders AS L ω).isSetRing.addContent_of_union
    (fibreCylinderContent AS L ω) (fibreCylinderContent_empty AS L ω)
    (fibreCylinderContent_union AS L ω)

/-- Compactness gives countable subadditivity of the cylinder content on cylinders. -/
theorem fibreCylinderAddContent_isSigmaSubadditive (ω : AS.Ω) :
    (fibreCylinderAddContent AS L ω).IsSigmaSubadditive := by
  intro f hf huf
  have hc : IsCompact (⋃ i, f i) := by
    obtain ⟨F, B, hB⟩ := huf
    rw [← hB]
    exact isCompact_fibreCylinder AS L F ω B
  have ho (i : ℕ) : IsOpen (f i) := by
    obtain ⟨F, B, hB⟩ := hf i
    rw [← hB]
    exact (isClopen_fibreCylinder AS L F ω B).isOpen
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover f ho (by rfl)
  have heq : (⋃ i, f i) = ⋃ i ∈ t, f i :=
    le_antisymm ht (Set.iUnion₂_subset fun i _ ↦ Set.subset_iUnion f i)
  calc
    (fibreCylinderAddContent AS L ω) (⋃ i, f i) =
        (fibreCylinderAddContent AS L ω) (⋃ i ∈ t, f i) := congrArg _ heq
    _ ≤ ∑ i ∈ t, (fibreCylinderAddContent AS L ω) (f i) :=
      addContent_biUnion_le (isSetAlgebra_fibreCylinders AS L ω).isSetRing (fun i _ ↦ hf i)
    _ ≤ ∑' i, (fibreCylinderAddContent AS L ω) (f i) := ENNReal.sum_le_tsum t

/-- The outer measure generated by the cylinder envelope is the extension of its content. -/
theorem fibreCylinderOuterMeasure_eq_induced (ω : AS.Ω) :
    OuterMeasure.ofFunction (fibreCylinderContent AS L ω) (fibreCylinderContent_empty AS L ω) =
      inducedOuterMeasure
        (fun A (_ : A ∈ fibreCylinders AS L ω) ↦ fibreCylinderAddContent AS L ω A)
        (isSetAlgebra_fibreCylinders AS L ω).empty_mem addContent_empty := by
  apply le_antisymm
  · apply le_inducedOuterMeasure.mpr
    intro A _
    exact OuterMeasure.ofFunction_le A
  · apply OuterMeasure.le_ofFunction.mpr
    intro A
    refine le_iInf fun F ↦ le_iInf fun B ↦ le_iInf fun hAB ↦ ?_
    calc
      _ ≤ inducedOuterMeasure
          (fun A (_ : A ∈ fibreCylinders AS L ω) ↦ fibreCylinderAddContent AS L ω A)
          (isSetAlgebra_fibreCylinders AS L ω).empty_mem addContent_empty
          (projFiniteFiber F ω ⁻¹' B) := measure_mono hAB
      _ ≤ fibreCylinderAddContent AS L ω (projFiniteFiber F ω ⁻¹' B) :=
        le_inducedOuterMeasure.mp le_rfl _ ⟨F, B, rfl⟩
      _ = _ := fibreCylinderContent_preimage AS L ω F B

/-- The outer measure has the prescribed mass on each finite-stage cylinder. -/
theorem fibreCylinderOuterMeasure_preimage (ω : AS.Ω) (F : FiniteIntermediateField K L)
    (B : Set (FiniteBaseFiber L F ω)) :
    OuterMeasure.ofFunction (fibreCylinderContent AS L ω) (fibreCylinderContent_empty AS L ω)
        (projFiniteFiber F ω ⁻¹' B) =
      ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω B := by
  rw [fibreCylinderOuterMeasure_eq_induced AS L ω,
    AddContent.inducedOuterMeasure_eq
      (isSetAlgebra_fibreCylinders AS L ω).isSetRing.isSetSemiring
      (fibreCylinderAddContent AS L ω) (fibreCylinderAddContent_isSigmaSubadditive AS L ω)
      ⟨F, B, rfl⟩]
  exact fibreCylinderContent_preimage AS L ω F B

/-- The fibre σ-algebra consists of Carathéodory-measurable sets for the cylinder content. -/
theorem fibreMeasurableSpace_le_caratheodory (ω : AS.Ω) :
    fibreMeasurableSpace L ω ≤
      (OuterMeasure.ofFunction (fibreCylinderContent AS L ω)
        (fibreCylinderContent_empty AS L ω)).caratheodory := by
  rw [fibreMeasurableSpace_eq_generateFrom AS L ω, fibreCylinderOuterMeasure_eq_induced AS L ω]
  intro A hA
  exact AddContent.isCaratheodory_inducedOuterMeasure
    (isSetAlgebra_fibreCylinders AS L ω).isSetRing.isSetSemiring
    (fibreCylinderAddContent AS L ω) A hA

/-- Chen--Moriwaki, Proposition 3.4.6: the projective-limit fibre probability measure
`P_{L,ω}` on the fibre `M_{L,ω}`, defined as the Carathéodory extension of the cylinder
content: the outer measure generated by `fibreCylinderContent` (whose value on a countable
cylinder cover is the infimum of the total finite-stage measures), restricted to the fibre
σ-algebra `A_{L,ω}`. -/
noncomputable def fibreProbabilityMeasure (ω : AS.Ω) :
    @Measure (BaseFiber L ω)
      (fibreMeasurableSpace L ω) :=
  letI : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  (OuterMeasure.ofFunction (fibreCylinderContent AS L ω)
    (fibreCylinderContent_empty AS L ω)).toMeasure (fibreMeasurableSpace_le_caratheodory AS L ω)

/-- The algebraic fibre measure has the prescribed mass on every finite-stage cylinder. -/
theorem fibreProbabilityMeasure_preimage (ω : AS.Ω) (F : FiniteIntermediateField K L)
    (B : Set (FiniteBaseFiber L F ω)) :
    fibreProbabilityMeasure AS L ω (projFiniteFiber F ω ⁻¹' B) =
      ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω B := by
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  rw [fibreProbabilityMeasure, toMeasure_apply _ _
    ((measurable_projFiniteFiber AS L ω F) (measurableSet_finiteBaseFiber AS L F ω B)),
    fibreCylinderOuterMeasure_preimage AS L ω F B]

/-- Chen--Moriwaki, Proposition 3.4.6: `P_{L,ω}` has total mass one. -/
theorem fibreProbabilityMeasure_isProbability (ω : AS.Ω) :
    @IsProbabilityMeasure (BaseFiber L ω)
      (fibreMeasurableSpace L ω)
      (fibreProbabilityMeasure AS L ω) := by
  let F : FiniteIntermediateField K L := FiniteIntermediateField.bot
  have : IsProbabilityMeasure (ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω) :=
    ParameterSpaceExtension.isProbabilityMeasure_fibreProbabilityMeasure AS
      (separableClosure K F.1) ω
  constructor
  have h := fibreProbabilityMeasure_preimage AS L ω F Set.univ
  simpa only [Set.preimage_univ, measure_univ] using h

attribute [instance] fibreProbabilityMeasure_isProbability

/-- Chen--Moriwaki, Proposition 3.4.6: the finite-stage marginals of `P_{L,ω}` are the
prescribed finite fibre probability measures. -/
theorem map_fibreProbabilityMeasure_projFiniteFiber (ω : AS.Ω)
    (F : FiniteIntermediateField K L) :
    @Measure.map (BaseFiber L ω) (FiniteBaseFiber L F ω)
        (fibreMeasurableSpace L ω) inferInstance
        (projFiniteFiber F ω) (fibreProbabilityMeasure AS L ω) =
      ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω := by
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_projFiniteFiber AS L ω F) hB]
  exact fibreProbabilityMeasure_preimage AS L ω F B

/-- Chen--Moriwaki, Proposition 3.4.6, formula (3.17): integrating a cylinder function
against `P_{L,ω}` computes its finite-stage fibre integral `I_{L/K,ω}`. -/
theorem integral_fibreProbabilityMeasure_descend {ω : AS.Ω} {f : BaseFiber L ω → ℝ}
    (d : DescendsToFiniteFiber ω f) :
    ∫ x, f x ∂fibreProbabilityMeasure AS L ω = fibreCylinderIntegral d := by
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  let := ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K d.F.1) ω
  calc
    _ = ∫ x, d.g (projFiniteFiber d.F ω x) ∂fibreProbabilityMeasure AS L ω :=
      integral_congr_ae (Filter.Eventually.of_forall (congrFun d.eq_comp))
    _ = ∫ y, d.g y ∂Measure.map (projFiniteFiber d.F ω)
        (fibreProbabilityMeasure AS L ω) :=
      (integral_map (measurable_projFiniteFiber AS L ω d.F).aemeasurable
        (measurable_of_countable d.g).aestronglyMeasurable).symm
    _ = _ := by rw [map_fibreProbabilityMeasure_projFiniteFiber]; rfl

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
  funext ω
  calc
    _ = ∫ _ : BaseFiber L ω, g ω ∂fibreProbabilityMeasure AS L ω :=
      integral_congr_ae (Filter.Eventually.of_forall fun x ↦ congrArg g x.property)
    _ = g ω := by simp

/-- Formula (3.19): on a function pulled back from a finite stage, the fibre integration
operator computes the finite-stage fibre integral: `I_{L/K}(g ∘ π_{L/K''}) = I_{K''/K}(g)`. -/
theorem fibreIntegral_comp_projFinite (F : FiniteIntermediateField K L)
    (g : ParameterSpaceFinExtension AS F → ℝ) :
    fibreIntegral AS L (fun x ↦ g (projFinite AS F x)) =
      ParameterSpaceFinExtension.fibreIntegral AS F g := by
  funext ω
  exact integral_fibreProbabilityMeasure_descend AS L
    ⟨F, fun y ↦ g y.val, rfl⟩

/-- Nonnegative pullbacks from the base are constant on probability fibres. -/
theorem fibreLIntegral_comp_proj (g : AS.Ω → ℝ≥0∞) :
    fibreLIntegral AS L (fun x ↦ g (ParameterSpaceExtension.proj x)) = g := by
  funext ω
  calc
    _ = ∫⁻ _ : BaseFiber L ω, g ω ∂fibreProbabilityMeasure AS L ω :=
      lintegral_congr fun x ↦ congrArg g x.property
    _ = g ω := by simp

/-- Nonnegative finite-stage pullbacks integrate through the prescribed finite marginal. -/
theorem fibreLIntegral_comp_projFinite (F : FiniteIntermediateField K L)
    (g : ParameterSpaceFinExtension AS F → ℝ≥0∞) :
    fibreLIntegral AS L (fun x ↦ g (projFinite AS F x)) =
      ParameterSpaceExtension.fibreLIntegral AS (separableClosure K F.1) g := by
  funext ω
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  let := ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K F.1) ω
  have h := lintegral_map (μ := fibreProbabilityMeasure AS L ω)
    (measurable_of_countable (fun y : FiniteBaseFiber L F ω ↦ g y.val))
    (measurable_projFiniteFiber AS L ω F)
  rw [map_fibreProbabilityMeasure_projFiniteFiber AS L ω F] at h
  exact h.symm

omit [Algebra.IsAlgebraic K L] in
/-- The inclusion of a fibre into the projective parameter space is measurable. -/
theorem measurable_subtype_val_baseFiber (ω : AS.Ω) :
    @Measurable (BaseFiber L ω) (ParameterSpaceExtension AS L)
      (fibreMeasurableSpace L ω) (projectiveMeasurableSpace AS L) Subtype.val := by
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

omit [Algebra.IsAlgebraic K L] in
/-- Chen--Moriwaki, Proposition 3.4.8: a projectively measurable function restricts to a
measurable function on every fibre, for any measurable codomain. -/
theorem measurable_restrict_baseFiber {Y : Type*} [MeasurableSpace Y]
    {f : ParameterSpaceExtension AS L → Y}
    (hf : Measurable[projectiveMeasurableSpace AS L] f) (ω : AS.Ω) :
    Measurable[fibreMeasurableSpace L ω] fun x : BaseFiber L ω ↦ f x.1 :=
  hf.comp (measurable_subtype_val_baseFiber AS L ω)

variable {L} in
omit [Algebra.IsAlgebraic K L] in
theorem measurable_projFiniteOfLE {F G : FiniteIntermediateField K L} (hFG : F.1 ≤ G.1) :
    Measurable (projFiniteOfLE AS hFG) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap _ (_ ⊔ ⨆ a : separableClosure K F.1, _) ≤ _
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
  refine sup_le ?_ (iSup_le fun a ↦ ?_)
  · rw [MeasurableSpace.comap_comp]
    exact (ParameterSpaceExtension.measurable_proj AS (separableClosure K G.1)).comap_le
  · rw [MeasurableSpace.comap_comp]
    exact (ParameterSpaceExtension.measurable_eval AS (separableClosure K G.1)
      (finiteSeparableInclusion hFG a)).comap_le

/-- The fibre probabilities, pushed into the total parameter space, form a measurable
family of probability measures. -/
theorem measurable_map_fibreProbabilityMeasure :
    @Measurable AS.Ω
      (@Measure (ParameterSpaceExtension AS L) (projectiveMeasurableSpace AS L)) AS.A
      (@Measure.instMeasurableSpace (ParameterSpaceExtension AS L) (projectiveMeasurableSpace AS L))
      (fun ω ↦ @Measure.map (BaseFiber L ω) (ParameterSpaceExtension AS L)
        (fibreMeasurableSpace L ω) (projectiveMeasurableSpace AS L)
        Subtype.val (fibreProbabilityMeasure AS L ω)) := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  let μ (ω : AS.Ω) : Measure (ParameterSpaceExtension AS L) :=
    @Measure.map (BaseFiber L ω) (ParameterSpaceExtension AS L)
      (fibreMeasurableSpace L ω) (projectiveMeasurableSpace AS L)
      Subtype.val (fibreProbabilityMeasure AS L ω)
  let (ω : AS.Ω) : @IsProbabilityMeasure (BaseFiber L ω) (fibreMeasurableSpace L ω)
      (fibreProbabilityMeasure AS L ω) := fibreProbabilityMeasure_isProbability AS L ω
  let (ω : AS.Ω) : IsProbabilityMeasure (μ ω) :=
    Measure.isProbabilityMeasure_map (measurable_subtype_val_baseFiber AS L ω).aemeasurable
  let m (F : FiniteIntermediateField K L) :=
    MeasurableSpace.comap (projFinite AS F) inferInstance
  have hmono {F G : FiniteIntermediateField K L} (hFG : F.1 ≤ G.1) : m F ≤ m G := by
    intro A hA
    obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
    apply MeasurableSpace.measurableSet_comap.mpr
    refine ⟨projFiniteOfLE AS hFG ⁻¹' B,
      hB.preimage (measurable_projFiniteOfLE AS hFG), ?_⟩
    ext x
    exact (congrArg (fun z ↦ z ∈ B) (projFiniteOfLE_projFinite AS hFG x)).to_iff
  have hgen : (inferInstance : MeasurableSpace (ParameterSpaceExtension AS L)) =
      MeasurableSpace.generateFrom (⋃ F, {A | @MeasurableSet _ (m F) A}) :=
    (MeasurableSpace.generateFrom_iUnion_measurableSet m).symm
  have hpi : IsPiSystem (⋃ F, {A | @MeasurableSet _ (m F) A}) := by
    apply isPiSystem_iUnion_of_directed_le
    · intro F A hA B hB _
      exact @MeasurableSet.inter _ (m F) _ _ hA hB
    · intro F G
      refine ⟨FiniteIntermediateField.sup F G, ?_, ?_⟩
      · exact hmono (FiniteIntermediateField.left_le_sup F G)
      · exact hmono (FiniteIntermediateField.right_le_sup F G)
  change Measurable μ
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure hgen hpi
  intro A hA
  obtain ⟨F, hA⟩ := Set.mem_iUnion.mp hA
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
  have heq (ω : AS.Ω) :
      μ ω (projFinite AS F ⁻¹' B) =
        ParameterSpaceExtension.fibreLIntegral AS (separableClosure K F.1)
          (B.indicator fun _ ↦ (1 : ℝ≥0∞)) ω := by
    have hp : @Measurable (BaseFiber L ω) (FiniteBaseFiber L F ω)
        (fibreMeasurableSpace L ω) inferInstance (projFiniteFiber F ω) :=
      Measurable.of_comap_le (le_iSup
        (fun G : FiniteIntermediateField K L ↦
          MeasurableSpace.comap (projFiniteFiber G ω) inferInstance) F)
    have hmarg : Measure.map (projFinite AS F) (μ ω) =
        Measure.map Subtype.val (ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω) := by
      rw [Measure.map_map (measurable_projFinite_projective AS L F)
        (measurable_subtype_val_baseFiber AS L ω)]
      have hcomp :
          (projFinite AS F ∘ (Subtype.val : BaseFiber L ω → ParameterSpaceExtension AS L)) =
          (Subtype.val : FiniteBaseFiber L F ω → ParameterSpaceFinExtension AS F) ∘
            projFiniteFiber F ω := rfl
      rw [hcomp, ← Measure.map_map measurable_subtype_coe hp,
        map_fibreProbabilityMeasure_projFiniteFiber]
    rw [← Measure.map_apply (measurable_projFinite_projective AS L F) hB, hmarg,
      Measure.map_apply measurable_subtype_coe hB]
    symm
    change (∫⁻ x : FiniteBaseFiber L F ω, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x.val
      ∂ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω) = _
    have hind : (fun x : FiniteBaseFiber L F ω ↦ B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x.val) =
        (Subtype.val ⁻¹' B).indicator (fun _ : FiniteBaseFiber L F ω ↦ (1 : ℝ≥0∞)) := rfl
    rw [hind, lintegral_indicator_const (hB.preimage measurable_subtype_coe), one_mul]
  simp_rw [heq]
  exact ParameterSpaceExtension.measurable_fibreLIntegral AS (separableClosure K F.1)
    (measurable_const.indicator hB)

/-- Proposition 3.4.8: fibre integration of a nonnegative projectively measurable function is
measurable on the base. -/
theorem measurable_fibreLIntegral {f : ParameterSpaceExtension AS L → ℝ≥0∞}
    (hf : Measurable[projectiveMeasurableSpace AS L] f) :
    Measurable (fibreLIntegral AS L f) := by
  have hm := (Measure.measurable_lintegral hf).comp
    (measurable_map_fibreProbabilityMeasure AS L)
  convert hm using 1 <;> try rfl
  funext ω
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  exact (lintegral_map hf (measurable_subtype_val_baseFiber AS L ω)).symm

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
        let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
        have hind (s : Set (ParameterSpaceExtension AS L)) (hs : MeasurableSet s) (ω : AS.Ω) :
            fibreLIntegral AS L (s.indicator fun _ ↦ 1) ω =
              fibreProbabilityMeasure AS L ω (Subtype.val ⁻¹' s) := by
          simp only [fibreLIntegral, ← Set.indicator_comp_right, Function.comp_def]
          rw [lintegral_indicator_const (hs.preimage (measurable_subtype_val_baseFiber AS L ω))]
          simp
        have hpoint (ω : AS.Ω) :
            fibreLIntegral AS L ((⋃ n, A n).indicator fun _ ↦ 1) ω =
              ∑' n, fibreLIntegral AS L ((A n).indicator fun _ ↦ 1) ω := by
          rw [hind _ (MeasurableSet.iUnion hA), Set.preimage_iUnion,
            measure_iUnion (fun i j hij ↦ (hdisj hij).preimage Subtype.val)
              (fun n ↦ (hA n).preimage (measurable_subtype_val_baseFiber AS L ω))]
          congr 1
          funext n
          exact (hind _ (hA n) ω).symm
        simp_rw [hpoint]
        exact lintegral_tsum (fun n ↦
          (measurable_fibreLIntegral AS L (measurable_const.indicator (hA n))).aemeasurable))

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
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  refine Measurable.ennreal_induction
    (motive := fun f ↦ (∫⁻ x, f x ∂measure AS L) =
      ∫⁻ ω, fibreLIntegral AS L f ω ∂AS.v) ?_ ?_ ?_ hf
  · intro c s hs
    rw [lintegral_indicator_const hs, measure_apply AS L hs,
      ← lintegral_const_mul c (measurable_fibreLIntegral AS L (measurable_const.indicator hs))]
    apply lintegral_congr
    intro ω
    simp only [fibreLIntegral, ← Set.indicator_comp_right, Function.comp_def]
    rw [lintegral_indicator_const (hs.preimage (measurable_subtype_val_baseFiber AS L ω)),
      lintegral_indicator_const (hs.preimage (measurable_subtype_val_baseFiber AS L ω)), one_mul]
  · intro f g _ hf hg ihf ihg
    simp only [Pi.add_apply]
    rw [lintegral_add_left hf, ihf, ihg,
      ← lintegral_add_left (measurable_fibreLIntegral AS L hf)]
    apply lintegral_congr
    intro ω
    exact (lintegral_add_left (measurable_restrict_baseFiber AS L hf ω) _).symm
  · intro f hf hmono ih
    rw [lintegral_iSup hf hmono]
    simp_rw [ih]
    rw [← lintegral_iSup (fun n ↦ measurable_fibreLIntegral AS L (hf n))
      (fun n m h ω ↦ lintegral_mono fun x ↦ hmono h x.val)]
    apply lintegral_congr
    intro ω
    exact (lintegral_iSup (fun n ↦ measurable_restrict_baseFiber AS L (hf n) ω)
      (fun n m h x ↦ hmono h x.val)).symm

/-- Chen--Moriwaki, Proposition 3.4.9: a projectively measurable function is `ν_L`-integrable
if and only if the fibre integral of its absolute value — computed in `[0, +∞]`, as in the
discussion after Proposition 3.4.8, since fibres of an infinite extension need not have
integrable restrictions — has finite integral on the base. -/
theorem integrable_measure_iff {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Measurable[projectiveMeasurableSpace AS L] f) :
    Integrable[projectiveMeasurableSpace AS L] f (measure AS L) ↔
      ∫⁻ ω, fibreLIntegral AS L (fun x ↦ ENNReal.ofReal |f x|) ω ∂AS.v < ∞ := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  have habs : Measurable (fun x ↦ |f x|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  rw [← integrable_norm_iff hf.aestronglyMeasurable]
  simp only [Real.norm_eq_abs]
  rw [← lintegral_ofReal_ne_top_iff_integrable habs.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ abs_nonneg (f x)),
    lintegral_measure AS L habs.ennreal_ofReal]
  exact lt_top_iff_ne_top.symm

/-- An almost everywhere property holds almost everywhere on almost every algebraic fibre. -/
theorem ae_ae_fibre_of_ae {p : ParameterSpaceExtension AS L → Prop}
    (hp : ∀ᵐ x ∂measure AS L, p x) :
    ∀ᵐ ω ∂AS.v, ∀ᵐ x ∂fibreProbabilityMeasure AS L ω, p x.val := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  obtain ⟨N, hsub, hN, hzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
  rw [measure_apply AS L hN] at hzero
  have h := (lintegral_eq_zero_iff
    (measurable_fibreLIntegral AS L (measurable_const.indicator hN))).mp hzero
  filter_upwards [h] with ω hω
  apply ae_iff.mpr
  apply measure_mono_null (t := Subtype.val ⁻¹' N) (fun x hx ↦ hsub hx)
  change fibreProbabilityMeasure AS L ω (Subtype.val ⁻¹' N) = 0
  simpa only [fibreLIntegral, ← Set.indicator_comp_right, Function.comp_def,
    lintegral_indicator_const (hN.preimage (measurable_subtype_val_baseFiber AS L ω)), one_mul,
    Pi.zero_apply] using hω

/-- A globally null set has null intersection with almost every algebraic fibre. -/
theorem ae_fibre_measure_preimage_eq_zero {N : Set (ParameterSpaceExtension AS L)}
    (hN : measure AS L N = 0) :
    ∀ᵐ ω ∂AS.v, fibreProbabilityMeasure AS L ω (Subtype.val ⁻¹' N) = 0 := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  have h : ∀ᵐ x ∂measure AS L, x ∉ N := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hN
  filter_upwards [ae_ae_fibre_of_ae AS L h] with ω hω
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  simpa only [ae_iff, not_not, Set.preimage] using hω

/-- The real integral of a nonnegative measurable function is the real value of its
nonnegative integral. -/
theorem fibreIntegral_eq_toReal_of_nonneg {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Measurable[projectiveMeasurableSpace AS L] f) (hpos : ∀ x, 0 ≤ f x)
    (ω : AS.Ω) :
    fibreIntegral AS L f ω =
      (fibreLIntegral AS L (fun x ↦ ENNReal.ofReal (f x)) ω).toReal := by
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x ↦ hpos x.val)
    (measurable_restrict_baseFiber AS L hf ω).aestronglyMeasurable

/-- A measurable integrable function has integrable restrictions to almost every algebraic fibre. -/
theorem integrable_fibre_ae_of_measurable {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Measurable[projectiveMeasurableSpace AS L] f)
    (hi : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    ∀ᵐ ω ∂AS.v, Integrable (fun x : BaseFiber L ω ↦ f x.val)
      (fibreProbabilityMeasure AS L ω) := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  have habs : Measurable (fun x ↦ ENNReal.ofReal |f x|) := by
    simpa only [Real.norm_eq_abs] using hf.norm.ennreal_ofReal
  have hfin := (integrable_measure_iff AS L hf).mp hi
  filter_upwards [ae_lt_top (measurable_fibreLIntegral AS L habs) hfin.ne] with ω hω
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  have hm := measurable_restrict_baseFiber AS L hf ω
  rw [← integrable_norm_iff hm.aestronglyMeasurable]
  simp only [Real.norm_eq_abs]
  apply (lintegral_ofReal_ne_top_iff_integrable
    (μ := fibreProbabilityMeasure AS L ω) (f := fun x : BaseFiber L ω ↦ |f x.val|)
    (by simpa only [Real.norm_eq_abs] using hm.norm.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦ abs_nonneg (f x.val))).mp
  exact hω.ne

/-- The average of a nonnegative integrable function is integrable on the base. -/
theorem integrable_fibreIntegral_of_nonneg {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Measurable[projectiveMeasurableSpace AS L] f) (hpos : ∀ x, 0 ≤ f x)
    (hi : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    Integrable (fibreIntegral AS L f) AS.v := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  have hfin := (integrable_measure_iff AS L hf).mp hi
  simp_rw [abs_of_nonneg (hpos _)] at hfin
  have heq : fibreIntegral AS L f =
      fun ω ↦ (fibreLIntegral AS L (fun x ↦ ENNReal.ofReal (f x)) ω).toReal :=
    funext (fibreIntegral_eq_toReal_of_nonneg AS L hf hpos)
  rw [heq]
  exact integrable_toReal_of_lintegral_ne_top
    (measurable_fibreLIntegral AS L hf.ennreal_ofReal).aemeasurable hfin.ne

/-- Nonnegative integrable real functions satisfy the algebraic disintegration formula. -/
theorem integral_measure_of_nonneg {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Measurable[projectiveMeasurableSpace AS L] f) (hpos : ∀ x, 0 ≤ f x)
    (hi : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    ∫ x, f x ∂measure AS L = ∫ ω, fibreIntegral AS L f ω ∂AS.v := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  have hfin := (integrable_measure_iff AS L hf).mp hi
  simp_rw [abs_of_nonneg (hpos _)] at hfin
  have hm := measurable_fibreLIntegral AS L hf.ennreal_ofReal
  have heq : fibreIntegral AS L f =
      fun ω ↦ (fibreLIntegral AS L (fun x ↦ ENNReal.ofReal (f x)) ω).toReal :=
    funext (fibreIntegral_eq_toReal_of_nonneg AS L hf hpos)
  calc
    _ = (∫⁻ ω, fibreLIntegral AS L (fun x ↦ ENNReal.ofReal (f x)) ω ∂AS.v).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hpos)
        hf.aestronglyMeasurable, lintegral_measure AS L hf.ennreal_ofReal]
    _ = _ := by
      rw [heq, integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
        hm.ennreal_toReal.aestronglyMeasurable]
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_lt_top hm hfin.ne] with ω hω
      exact (ENNReal.ofReal_toReal hω.ne).symm

theorem integrable_fibreIntegral_and_integral_of_measurable
    {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Measurable[projectiveMeasurableSpace AS L] f)
    (hi : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    Integrable (fibreIntegral AS L f) AS.v ∧
      ∫ x, f x ∂measure AS L = ∫ ω, fibreIntegral AS L f ω ∂AS.v := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  let p := fun x ↦ max (f x) 0
  let n := fun x ↦ max (-f x) 0
  have hp : Measurable p := hf.max measurable_const
  have hn : Measurable n := hf.neg.max measurable_const
  have hip : Integrable p (measure AS L) := hi.pos_part
  have hin : Integrable n (measure AS L) := hi.neg.pos_part
  have hbp := integrable_fibreIntegral_of_nonneg AS L hp (fun _ ↦ le_max_right _ _) hip
  have hbn := integrable_fibreIntegral_of_nonneg AS L hn (fun _ ↦ le_max_right _ _) hin
  have hfsub : f = p - n := by
    funext x
    dsimp [p, n]
    grind
  have hsub : fibreIntegral AS L f =ᵐ[AS.v]
      fun ω ↦ fibreIntegral AS L p ω - fibreIntegral AS L n ω := by
    filter_upwards [integrable_fibre_ae_of_measurable AS L hp hip,
      integrable_fibre_ae_of_measurable AS L hn hin] with ω hωp hωn
    change (∫ x : BaseFiber L ω, f x.val ∂fibreProbabilityMeasure AS L ω) = _
    rw [hfsub]
    exact integral_sub hωp hωn
  refine ⟨(hbp.sub hbn).congr hsub.symm, ?_⟩
  rw [integral_congr_ae hsub, integral_sub hbp hbn,
    ← integral_measure_of_nonneg AS L hp (fun _ ↦ le_max_right _ _) hip,
    ← integral_measure_of_nonneg AS L hn (fun _ ↦ le_max_right _ _) hin, hfsub]
  exact integral_sub hip hin

/-- Integrable functions have integrable restrictions to almost every algebraic fibre. -/
theorem integrable_fibre_ae {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    ∀ᵐ ω ∂AS.v, Integrable (fun x : BaseFiber L ω ↦ f x.val)
      (fibreProbabilityMeasure AS L ω) := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[measure AS L] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : Integrable g (measure AS L) := hf.congr hfg
  have hgm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  filter_upwards [integrable_fibre_ae_of_measurable AS L hgm hg,
    ae_ae_fibre_of_ae AS L hfg] with ω hω hfgω
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  apply hω.congr
  filter_upwards [hfgω] with x hx
  exact hx.symm

/-- Fibre averages of integrable functions are integrable on the base. -/
theorem integrable_fibreIntegral {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    Integrable (fibreIntegral AS L f) AS.v := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[measure AS L] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : Integrable g (measure AS L) := hf.congr hfg
  have hgm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hi := (integrable_fibreIntegral_and_integral_of_measurable AS L hgm hg).1
  apply hi.congr
  filter_upwards [ae_ae_fibre_of_ae AS L hfg] with ω hω
  exact (integral_congr_ae hω).symm

/-- Chen--Moriwaki, Proposition 3.4.9: algebraic disintegration for integrable real functions. -/
theorem integral_measure {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    ∫ x, f x ∂measure AS L = ∫ ω, fibreIntegral AS L f ω ∂AS.v := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[measure AS L] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : Integrable g (measure AS L) := hf.congr hfg
  have hgm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfib : fibreIntegral AS L f =ᵐ[AS.v] fibreIntegral AS L g := by
    filter_upwards [ae_ae_fibre_of_ae AS L hfg] with ω hω
    exact integral_congr_ae hω
  exact (integral_congr_ae hfg).trans
    (((integrable_fibreIntegral_and_integral_of_measurable AS L hgm hg).2).trans
      (integral_congr_ae hfib).symm)

/-- Chen--Moriwaki, Proposition 3.4.9: algebraic fibre integration is an L1 contraction. -/
theorem integral_abs_fibreIntegral_le {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    ∫ ω, |fibreIntegral AS L f ω| ∂AS.v ≤ ∫ x, |f x| ∂measure AS L := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  have habs : Integrable (fun x ↦ |f x|) (measure AS L) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  rw [integral_measure AS L habs]
  apply integral_mono
  · simpa only [Real.norm_eq_abs] using (integrable_fibreIntegral AS L hf).norm
  · exact integrable_fibreIntegral AS L habs
  · intro ω
    let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
    simpa only [fibreIntegral, Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := fibreProbabilityMeasure AS L ω)
        (fun x : BaseFiber L ω ↦ f x.val)

theorem ofReal_abs_fibreIntegral_le_fibreLIntegral_ae
    {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    ∀ᵐ ω ∂AS.v, ENNReal.ofReal |fibreIntegral AS L f ω| ≤
      fibreLIntegral AS L (fun x ↦ ENNReal.ofReal |f x|) ω := by
  filter_upwards [integrable_fibre_ae AS L hf] with ω hω
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  have habs : Integrable (fun x : BaseFiber L ω ↦ |f x.val|)
      (fibreProbabilityMeasure AS L ω) := by
    simpa only [Real.norm_eq_abs] using hω.norm
  calc
    _ ≤ ENNReal.ofReal (fibreIntegral AS L (fun x ↦ |f x|) ω) := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [fibreIntegral, Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := fibreProbabilityMeasure AS L ω)
          (fun x : BaseFiber L ω ↦ f x.val)
    _ = _ := ofReal_integral_eq_lintegral_ofReal habs
      (Filter.Eventually.of_forall fun x ↦ abs_nonneg (f x.val))

/-- The base projection preserves the algebraic extension measure. -/
theorem map_measure_proj :
    (letI : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
    Measure.map ParameterSpaceExtension.proj (measure AS L) = AS.v) := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_proj_projective AS L) hs, measure_apply AS L
    (hs.preimage (measurable_proj_projective AS L))]
  have hconst (ω : AS.Ω) :
      fibreLIntegral AS L ((ParameterSpaceExtension.proj ⁻¹' s).indicator fun _ ↦ 1) ω =
        s.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω := by
    change (∫⁻ x : BaseFiber L ω,
      (ParameterSpaceExtension.proj ⁻¹' s).indicator (fun _ ↦ (1 : ℝ≥0∞)) x.val
        ∂fibreProbabilityMeasure AS L ω) = _
    classical
    simp only [Set.indicator, Set.mem_preimage]
    simp_rw [show ∀ x : BaseFiber L ω, ParameterSpaceExtension.proj x.val = ω
      from fun x ↦ x.property]
    simp
  simp_rw [hconst]
  rw [lintegral_indicator_const hs, one_mul]

/-- Formula (3.21): the pullback of a `ν_K`-integrable function along the base projection is
`ν_L`-integrable. -/
theorem integrable_comp_proj_measure {g : AS.Ω → ℝ} (hg : Integrable g AS.v) :
    Integrable[projectiveMeasurableSpace AS L]
      (fun x ↦ g (ParameterSpaceExtension.proj x)) (measure AS L) := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  exact (show MeasurePreserving ParameterSpaceExtension.proj (measure AS L) AS.v from
    ⟨measurable_proj_projective AS L, map_measure_proj AS L⟩).integrable_comp_of_integrable hg

/-- Formula (3.21): integrating a pullback from the base against `ν_L` is integrating
against `ν_K`. -/
theorem integral_comp_proj_measure {g : AS.Ω → ℝ} (hg : Integrable g AS.v) :
    ∫ x, g (ParameterSpaceExtension.proj x) ∂measure AS L = ∫ ω, g ω ∂AS.v := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  have hm : AEStronglyMeasurable g
      (Measure.map (ParameterSpaceExtension.proj (AS := AS) (L := L)) (measure AS L)) := by
    rw [map_measure_proj AS L]
    exact hg.aestronglyMeasurable
  have h := integral_map (measurable_proj_projective AS L).aemeasurable hm
  rw [map_measure_proj AS L] at h
  exact h.symm

/-- Each finite-stage projection sends the algebraic extension measure to the finite
extension measure. -/
theorem map_measure_projFinite (F : FiniteIntermediateField K L) :
    (let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
    Measure.map (projFinite AS F) (measure AS L) = ParameterSpaceFinExtension.measure AS F) := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  ext B hB
  rw [Measure.map_apply (measurable_projFinite_projective AS L F) hB,
    measure_apply AS L (hB.preimage (measurable_projFinite_projective AS L F))]
  change _ = ParameterSpaceExtension.inducedMeasure AS (separableClosure K F.1) B
  rw [ParameterSpaceExtension.inducedMeasure_apply AS (separableClosure K F.1) hB]
  apply lintegral_congr
  intro ω
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  have hp : Measurable (projFiniteFiber F ω) :=
    Measurable.of_comap_le (le_iSup
      (fun G : FiniteIntermediateField K L ↦
        MeasurableSpace.comap (projFiniteFiber G ω) inferInstance) F)
  have hf : Measurable (fun y : FiniteBaseFiber L F ω ↦ B.indicator (fun _ ↦ (1 : ℝ≥0∞)) y.val) :=
    (measurable_const.indicator hB).comp measurable_subtype_coe
  change (∫⁻ x : BaseFiber L ω,
    B.indicator (fun _ ↦ (1 : ℝ≥0∞)) (projFiniteFiber F ω x).val
    ∂fibreProbabilityMeasure AS L ω) = _
  rw [← lintegral_map hf hp, map_fibreProbabilityMeasure_projFiniteFiber]
  rfl

/-- Pullback from a finite stage preserves integrability. -/
theorem integrable_comp_projFinite_measure (F : FiniteIntermediateField K L)
    {g : ParameterSpaceFinExtension AS F → ℝ}
    (hg : Integrable g (ParameterSpaceFinExtension.measure AS F)) :
    Integrable[projectiveMeasurableSpace AS L] (fun x ↦ g (projFinite AS F x)) (measure AS L) := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  have hg' : Integrable g (Measure.map (projFinite AS F) (measure AS L)) := by
    simpa only [map_measure_projFinite AS L F] using hg
  exact hg'.comp_measurable (measurable_projFinite_projective AS L F)

/-- Integration of an integrable pullback from a finite stage. -/
theorem integral_comp_projFinite_measure (F : FiniteIntermediateField K L)
    {g : ParameterSpaceFinExtension AS F → ℝ}
    (hg : Integrable g (ParameterSpaceFinExtension.measure AS F)) :
    ∫ x, g (projFinite AS F x) ∂measure AS L =
      ∫ y, g y ∂ParameterSpaceFinExtension.measure AS F := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  rw [← map_measure_projFinite AS L F] at hg ⊢
  exact (integral_map (measurable_projFinite_projective AS L F).aemeasurable
    hg.aestronglyMeasurable).symm

/-- Pullback from a finite stage preserves the integral of the norm. -/
theorem integral_norm_comp_projFinite_measure (F : FiniteIntermediateField K L)
    {g : ParameterSpaceFinExtension AS F → ℝ}
    (hg : Integrable g (ParameterSpaceFinExtension.measure AS F)) :
    ∫ x, ‖g (projFinite AS F x)‖ ∂measure AS L =
      ∫ y, ‖g y‖ ∂ParameterSpaceFinExtension.measure AS F :=
  integral_comp_projFinite_measure AS L F hg.norm

/-- Proposition 3.4.10: logarithmic evaluations are integrable for the projective-limit measure. -/
theorem integrable_log_measure (a : L) (ha : a ≠ 0) :
    Integrable[projectiveMeasurableSpace AS L]
      (fun x : ParameterSpaceExtension AS L ↦ Real.log ((ParameterSpaceExtension.ϕ x) a))
      (measure (AS := AS) (L := L)) := by
  let F := ofElement (K := K) L a
  let b : F := ⟨a, mem_ofElement L a⟩
  have hb : b ≠ 0 := fun h ↦ ha (congrArg Subtype.val h)
  convert integrable_comp_projFinite_measure AS L F
    (ParameterSpaceFinExtension.integrable_log AS F b hb) using 1
  funext x
  exact congrArg Real.log (congrArg (fun w : AbsoluteValue F ℝ ↦ w b)
    (ParameterSpaceFinExtension.extendAbsoluteValue_restriction (K := K) F
      ((ParameterSpaceExtension.ϕ x).restriction F))).symm

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
  constructor
  change ∀ a : L, a ≠ 0 →
    ∫ x, Real.log (ParameterSpaceExtension.ϕ x a) ∂measure AS L = 0
  intro a ha
  let F := ofElement (K := K) L a
  let b : F := ⟨a, mem_ofElement L a⟩
  have hb : b ≠ 0 := fun h ↦ ha (congrArg Subtype.val h)
  let : (AS.finiteExtension F).toAdelicCurve.IsProper :=
    ParameterSpaceFinExtension.isProper_finiteExtension AS F
  have hzero := AdelicCurve.IsProper.product_formula
    (C := (AS.finiteExtension F).toAdelicCurve) b hb
  change ∫ y, Real.log (ParameterSpaceFinExtension.ϕ AS F y b)
    ∂ParameterSpaceFinExtension.measure AS F = 0 at hzero
  rw [← integral_comp_projFinite_measure AS L F
    (ParameterSpaceFinExtension.integrable_log AS F b hb)] at hzero
  convert hzero using 1
  congr 1
  funext x
  exact congrArg Real.log (congrArg (fun w : AbsoluteValue F ℝ ↦ w b)
    (ParameterSpaceFinExtension.extendAbsoluteValue_restriction (K := K) F
      ((ParameterSpaceExtension.ϕ x).restriction F))).symm

end Algebraic

end AdelicStructure



end Extensions

end ArakelovGeometry
