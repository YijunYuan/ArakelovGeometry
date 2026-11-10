/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Measurable orientations of complex field embeddings

Absolute-value evaluations determine measurable real parts and products of
imaginary parts. A common conjugation choice then gives measurable values on
a countable field, without assuming that its raw orientation sign is measurable.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry

variable {α K : Type*} [MeasurableSpace α] [Field K]

/-- Absolute values of field embeddings determine their real parts measurably. -/
theorem measurable_complex_embedding_re (e : α → K →+* ℂ)
    (h : ∀ a, Measurable (fun ω => ‖e ω a‖)) (a : K) :
    Measurable (fun ω => (e ω a).re) := by
  have he (ω) : (e ω a).re = (‖e ω (a + 1)‖ ^ 2 - ‖e ω a‖ ^ 2 - 1) / 2 := by
    simp only [map_add, map_one, Complex.sq_norm, Complex.normSq_apply,
      Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im]
    ring
  simp_rw [he]
  exact (((h (a + 1)).pow_const 2).sub ((h a).pow_const 2)).sub_const 1 |>.div_const 2

/-- The square of every imaginary part is measurable before any orientation is chosen. -/
theorem measurable_complex_embedding_im_sq (e : α → K →+* ℂ)
    (h : ∀ a, Measurable (fun ω => ‖e ω a‖)) (a : K) :
    Measurable (fun ω => (e ω a).im ^ 2) := by
  have he (ω) : (e ω a).im ^ 2 = ‖e ω a‖ ^ 2 - (e ω a).re ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply]
    ring
  simp_rw [he]
  exact ((h a).pow_const 2).sub ((measurable_complex_embedding_re e h a).pow_const 2)

/-- Products of two imaginary parts are recovered by real polarization. -/
theorem measurable_complex_embedding_im_mul (e : α → K →+* ℂ)
    (h : ∀ a, Measurable (fun ω => ‖e ω a‖)) (a b : K) :
    Measurable (fun ω => (e ω a).im * (e ω b).im) := by
  have he (ω) : (e ω a).im * (e ω b).im =
      ((e ω (a + b)).im ^ 2 - (e ω a).im ^ 2 - (e ω b).im ^ 2) / 2 := by
    simp only [map_add, Complex.add_im]
    ring
  simp_rw [he]
  exact (((measurable_complex_embedding_im_sq e h (a + b)).sub
    (measurable_complex_embedding_im_sq e h a)).sub
      (measurable_complex_embedding_im_sq e h b)).div_const 2

/-- Source Claim 4.1.27: a signed product is measurable on the nonzero locus
from the two given product evaluations, without measurability of the sign. -/
theorem measurable_signed_mul_indicator (s g η : α → ℝ)
    (hs : ∀ ω, s ω = 1 ∨ s ω = -1)
    (hsg : Measurable (fun ω => s ω * g ω))
    (hgη : Measurable (fun ω => g ω * η ω)) :
    Measurable ({ω | g ω ≠ 0}.indicator (fun ω => s ω * η ω)) := by
  classical
  have he : ({ω | g ω ≠ 0}.indicator (fun ω => s ω * η ω)) =
      fun ω => (g ω * η ω) / (s ω * g ω) := by
    funext ω
    by_cases hg : g ω = 0
    · simp [hg]
    · rw [Set.indicator_of_mem hg]
      rcases hs ω with hs | hs <;> rw [hs] <;> field_simp
  rw [he]
  exact hgη.div hsg

/-- A countable family whose pairwise products are measurable admits one
common sign making every member measurable. The sign itself need not be measurable. -/
theorem exists_measurable_common_sign (g : ℕ → α → ℝ)
    (h : ∀ i j, Measurable (fun ω => g i ω * g j ω)) :
    ∃ s : α → ℝ, (∀ ω, s ω = 1 ∨ s ω = -1) ∧
      ∀ j, Measurable (fun ω => s ω * g j ω) := by
  classical
  have hnz (i : ℕ) : MeasurableSet {ω | g i ω ≠ 0} := by
    convert (measurableSet_eq_fun (h i i)
      (show Measurable (fun _ : α => (0 : ℝ)) from measurable_const)).compl using 1
    ext ω
    simp
  have hzero : MeasurableSet {ω | ∀ i, g i ω = 0} := by
    convert MeasurableSet.iInter (fun i => (hnz i).compl) using 1
    ext ω
    simp
  let p : α → ℕ → Prop := fun ω i => g i ω ≠ 0 ∨ ∀ j, g j ω = 0
  have hex (ω) : ∃ i, p ω i := by
    by_cases hg : ∃ i, g i ω ≠ 0
    · obtain ⟨i, hi⟩ := hg
      exact ⟨i, Or.inl hi⟩
    · exact ⟨0, Or.inr (by simpa only [not_exists, not_not] using hg)⟩
  let n : α → ℕ := fun ω => Nat.find (hex ω)
  have hn : Measurable n := measurable_find hex (fun i => (hnz i).union hzero)
  let s : α → ℝ := fun ω => if g (n ω) ω < 0 then -1 else 1
  refine ⟨s, fun ω => ?_, fun j => ?_⟩
  · dsimp only [s]
    split_ifs <;> simp
  · have hnum : Measurable (fun ω => g (n ω) ω * g j ω) :=
      (measurable_from_prod_countable_left (f := fun q : α × ℕ => g q.2 q.1 * g j q.1)
        (fun i => h i j)).comp (measurable_id.prodMk hn)
    have hsq : Measurable (fun ω => g (n ω) ω * g (n ω) ω) :=
      (measurable_from_prod_countable_left
        (f := fun q : α × ℕ => g q.2 q.1 * g q.2 q.1)
          (fun i => h i i)).comp (measurable_id.prodMk hn)
    have habs : Measurable (fun ω => |g (n ω) ω|) := by
      simpa only [Real.sqrt_mul_self_eq_abs] using hsq.sqrt
    have he (ω) : s ω * g j ω = (g (n ω) ω * g j ω) / |g (n ω) ω| := by
      have hp : p ω (n ω) := Nat.find_spec (hex ω)
      rcases hp with hnonzero | hall
      · by_cases hneg : g (n ω) ω < 0
        · dsimp only [s]
          rw [ite_eq_left hneg, abs_of_neg hneg]
          field_simp
        · have hpos : 0 < g (n ω) ω := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hnonzero)
          dsimp only [s]
          rw [ite_eq_right hneg, abs_of_pos hpos]
          field_simp
      · simp only [hall, mul_zero, abs_zero, div_zero]
    simp_rw [he]
    exact hnum.div habs

/-- A common complex conjugation changes the field embedding without changing
any of its absolute values. -/
def conjugateComplexEmbedding (e : K →+* ℂ) (c : Bool) : K →+* ℂ :=
  if c then (starRingEnd ℂ).comp e else e

@[simp]
theorem norm_conjugateComplexEmbedding (e : K →+* ℂ) (c : Bool) (a : K) :
    ‖conjugateComplexEmbedding e c a‖ = ‖e a‖ := by
  cases c <;> simp [conjugateComplexEmbedding]

/-- One conjugation choice makes all evaluations on a countable subfield
measurable. No measurability of the conjugation choice is assumed. -/
theorem exists_measurable_conjugate_on_countable_subfield (e : α → K →+* ℂ)
    (h : ∀ a, Measurable (fun ω => ‖e ω a‖))
    (K₀ : Subfield K) [Countable K₀] :
    ∃ c : α → Bool, ∀ a : K₀,
      Measurable (fun ω => conjugateComplexEmbedding (e ω) (c ω) (a : K)) := by
  obtain ⟨a, ha⟩ := exists_surjective_nat K₀
  obtain ⟨s, hs, hm⟩ := exists_measurable_common_sign
    (fun n ω => (e ω (a n : K)).im)
      (fun i j => measurable_complex_embedding_im_mul e h (a i : K) (a j : K))
  refine ⟨fun ω => decide (s ω ≠ 1), fun x => ?_⟩
  obtain ⟨j, rfl⟩ := ha x
  have hre : (fun ω => (conjugateComplexEmbedding (e ω)
      (decide (s ω ≠ 1)) (a j : K)).re) = fun ω => (e ω (a j : K)).re := by
    funext ω
    by_cases hω : s ω = 1 <;> simp [conjugateComplexEmbedding, hω]
  have him : (fun ω => (conjugateComplexEmbedding (e ω)
      (decide (s ω ≠ 1)) (a j : K)).im) = fun ω => s ω * (e ω (a j : K)).im := by
    funext ω
    rcases hs ω with hω | hω <;> norm_num [conjugateComplexEmbedding, hω]
  have Hr : Measurable (fun ω => (conjugateComplexEmbedding (e ω)
      (decide (s ω ≠ 1)) (a j : K)).re) := by
    rw [hre]
    exact measurable_complex_embedding_re e h _
  have Hi : Measurable (fun ω => (conjugateComplexEmbedding (e ω)
      (decide (s ω ≠ 1)) (a j : K)).im) := by
    rw [him]
    exact hm j
  convert (Complex.measurable_ofReal.comp Hr).add
    ((Complex.measurable_ofReal.comp Hi).mul_const Complex.I) using 1
  funext ω
  exact (Complex.re_add_im _).symm

/-- Countably many measurable comparison points determine a measurable limit
when their distances to the desired point are measurable and arbitrarily small. -/
theorem measurable_of_countable_approximation {β : Type*} [PseudoMetricSpace β]
    [MeasurableSpace β] [BorelSpace β] (f : α → β) (d : ℕ → α → β)
    (hd : ∀ n, Measurable (d n))
    (hm : ∀ n, Measurable (fun ω => dist (f ω) (d n ω)))
    (happrox : ∀ ω ε, 0 < ε → ∃ n, dist (f ω) (d n ω) < ε) : Measurable f := by
  classical
  have hex (n : ℕ) (ω : α) : ∃ j, dist (f ω) (d j ω) < 1 / ((n : ℝ) + 1) :=
    happrox ω _ (by positivity)
  let k : ℕ → α → ℕ := fun n ω => Nat.find (hex n ω)
  have hk (n : ℕ) : Measurable (k n) :=
    measurable_find (hex n) (fun j => measurableSet_lt (hm j) measurable_const)
  let a : ℕ → α → β := fun n ω => d (k n ω) ω
  have ha (n : ℕ) : Measurable (a n) :=
    (measurable_from_prod_countable_left (f := fun q : α × ℕ => d q.2 q.1) hd).comp
      (measurable_id.prodMk (hk n))
  apply measurable_of_tendsto_metrizable ha
  apply tendsto_pi_nhds.mpr
  intro ω
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  exact (dist_comm _ _).trans_le (Nat.find_spec (hex n ω)).le

/-- Measurable absolute values and one common countable dense subfield permit
compatible measurable complex embeddings on every rational element. -/
theorem exists_measurable_conjugate_of_dense_subfield (e : α → K →+* ℂ)
    (h : ∀ a, Measurable (fun ω => ‖e ω a‖))
    (K₀ : Subfield K) [Countable K₀]
    (hdense : ∀ ω a ε, 0 < ε → ∃ b : K₀, ‖e ω (a - (b : K))‖ < ε) :
    ∃ c : α → Bool, ∀ a : K,
      Measurable (fun ω => conjugateComplexEmbedding (e ω) (c ω) a) := by
  obtain ⟨c, hc⟩ := exists_measurable_conjugate_on_countable_subfield e h K₀
  obtain ⟨a, ha⟩ := exists_surjective_nat K₀
  refine ⟨c, fun x => ?_⟩
  apply measurable_of_countable_approximation _
    (fun n ω => conjugateComplexEmbedding (e ω) (c ω) (a n : K)) (fun n => hc (a n))
  · intro n
    simpa only [dist_eq_norm, ← map_sub, norm_conjugateComplexEmbedding] using
      h (x - (a n : K))
  · intro ω ε hε
    obtain ⟨b, hb⟩ := hdense ω x ε hε
    obtain ⟨n, rfl⟩ := ha b
    exact ⟨n, by simpa only [dist_eq_norm, ← map_sub,
      norm_conjugateComplexEmbedding] using hb⟩

/-- The canonical complex embedding of an RCLike field, including the real case. -/
def rclikeComplexEmbedding (L : Type*) [RCLike L] : L →+* ℂ where
  toFun x := RCLike.re x + RCLike.im x * Complex.I
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by simp only [map_add, Complex.ofReal_add]; ring
  map_mul' x y := by
    simp only [RCLike.mul_re, Complex.ofReal_sub, Complex.ofReal_mul,
      RCLike.mul_im, Complex.ofReal_add]
    ring_nf
    rw [Complex.I_sq]
    ring

/-- The completed field keeps its prescribed usual real or complex norm. -/
@[simp]
theorem norm_rclikeComplexEmbedding {L : Type*} [RCLike L] (x : L) :
    ‖rclikeComplexEmbedding L x‖ = ‖x‖ := RCLike.norm_to_complex x

/-- The canonical complex field embedding is isometric. -/
theorem isometry_rclikeComplexEmbedding (L : Type*) [RCLike L] :
    Isometry (rclikeComplexEmbedding L) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, ← map_sub, norm_rclikeComplexEmbedding, dist_eq_norm]

/-- A complex field embedding preserving norms is isometric. -/
theorem isometry_complexEmbedding_of_norm {L : Type*} [NormedField L]
    (σ : L →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖) : Isometry σ := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, ← map_sub, hσ, dist_eq_norm]

/-- An isometric complex embedding of an RCLike field fixes its real scalars. -/
theorem complexEmbedding_apply_ofReal {L : Type*} [RCLike L]
    (σ : L →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖) (r : ℝ) :
    σ (algebraMap ℝ L r) = (r : ℂ) := by
  have he := Complex.ringHom_eq_ofReal_of_continuous
    (f := σ.comp (algebraMap ℝ L))
      ((isometry_complexEmbedding_of_norm σ hσ).continuous.comp (continuous_algebraMap ℝ L))
  exact congrArg (fun f : ℝ →+* ℂ => f r) he

/-- A non-real complex image contains the ordinary imaginary unit. -/
theorem complexEmbedding_exists_imaginary_unit {L : Type*} [RCLike L]
    (σ : L →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (h : ¬∀ x, (σ x).im = 0) : ∃ x, σ x = Complex.I := by
  push Not at h
  obtain ⟨x, hx⟩ := h
  refine ⟨(x - algebraMap ℝ L (σ x).re) / algebraMap ℝ L (σ x).im, ?_⟩
  rw [map_div₀, map_sub, complexEmbedding_apply_ofReal σ hσ,
    complexEmbedding_apply_ofReal σ hσ]
  apply (div_eq_iff (by exact_mod_cast hx : ((σ x).im : ℂ) ≠ 0)).mpr
  apply Complex.ext <;> simp

/-- An isometric complex embedding is onto exactly on the non-real locus. -/
theorem complexEmbedding_surjective_iff {L : Type*} [RCLike L]
    (σ : L →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖) :
    Function.Surjective σ ↔ ¬∀ x, (σ x).im = 0 := by
  constructor
  · intro hs hreal
    obtain ⟨x, hx⟩ := hs Complex.I
    have h := hreal x
    rw [hx, Complex.I_im] at h
    exact one_ne_zero h
  · intro h
    obtain ⟨i, hi⟩ := complexEmbedding_exists_imaginary_unit σ hσ h
    intro z
    refine ⟨algebraMap ℝ L z.re + algebraMap ℝ L z.im * i, ?_⟩
    rw [map_add, map_mul, complexEmbedding_apply_ofReal σ hσ,
      complexEmbedding_apply_ofReal σ hσ, hi]
    exact Complex.re_add_im z

/-- On the real locus, the complex image is exactly the ordinary real axis. -/
theorem complexEmbedding_range_of_real {L : Type*} [RCLike L]
    (σ : L →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (h : ∀ x, (σ x).im = 0) : Set.range σ = Set.range Complex.ofReal := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(σ x).re, ?_⟩
    apply Complex.ext <;> simp [h]
  · rintro ⟨r, rfl⟩
    exact ⟨algebraMap ℝ L r, complexEmbedding_apply_ofReal σ hσ r⟩

end ArakelovGeometry
