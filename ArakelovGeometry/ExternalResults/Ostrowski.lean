import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Tactic
import Mathlib.NumberTheory.Ostrowski
import ArakelovGeometry.ExternalResults.Place
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.LinearAlgebra.Countable

/- USER: You don't need to prove this. Just admit it.-/
-- J. Neukirch, Algebraic number theory, Chapter II, Theorem 4.2
theorem Neukirch_ANT_Ch_II_Theorem_4_2 {K : Type*} [Field K] (abs : AbsoluteValue K ℝ)
  (habs : ¬ IsNonarchimedean abs) (hK : CauSeq.IsComplete K abs) :
  (
    ∃ σ : K ≃+* ℝ, ∃ s : ℝ, s ∈ Set.Ioc 0 1 ∧ ∀ a : K, abs a = ‖σ a‖ ^ s
  ) ∨ (
    ∃ σ : K ≃+* ℂ, ∃ s : ℝ, s ∈ Set.Ioc 0 1 ∧ ∀ a : K, abs a = ‖σ a‖ ^ s
  ) := by admit

theorem CauSeq.IsComplete_of_Completion {K : Type u_1} [inst : Field K]
  (abs : AbsoluteValue K ℝ) :
  let _ := abs.toNormedField;
  CauSeq.IsComplete (UniformSpace.Completion K)
  ⇑(NormedField.toAbsoluteValue (UniformSpace.Completion K)) := by
  letI := abs.toNormedField
  letI : CauSeq.IsComplete (UniformSpace.Completion K) norm := by
      refine ⟨fun f => ?_⟩
      have hf : CauchySeq (f : ℕ → UniformSpace.Completion K) := by
          rw [Metric.cauchySeq_iff]
          intro ε hε
          obtain ⟨N, hN⟩ := f.2.cauchy₂ hε
          exact ⟨N, fun m hm n hn => by simpa [dist_eq_norm] using hN m hm n hn⟩
      obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hf
      refine ⟨x, ?_⟩
      rw [Metric.tendsto_atTop] at hx
      intro ε hε
      obtain ⟨N, hN⟩ := hx ε hε
      exact ⟨N, fun j hj => by simpa [dist_eq_norm] using hN j hj⟩
  simpa only [NormedField.toAbsoluteValue, AbsoluteValue.coe_mk, MulHom.coe_mk] using
        (inferInstance : CauSeq.IsComplete (UniformSpace.Completion K) norm)

namespace NumberField
open AbsoluteValue

/- USER: You don't need to prove this. Just admit it.-/
theorem ostrowski {K : Type*} [Field K] [NumberField K]
  (abs : AbsoluteValue K ℝ) (habs : abs.IsNontrivial) :
  ( ∃ v : InfinitePlace K, abs ≈ v.val ) ∨
  ( ∃ v : FinitePlace K, abs ≈ v.val) := by
  admit

/-! ### Transfer lemmas (project-local helpers)

These connect `IsNonarchimedean` to the equivalence relation `≈` on absolute
values and to Mathlib's `FinitePlace` / `InfinitePlace` infrastructure. They are
the Lean form of the lemmas in blueprint chapter `ExternalResults_Ostrowski`
(`lem:isNonarchimedean_*`, `lem:finitePlace_isNonarchimedean`,
`lem:infinitePlace_not_isNonarchimedean`, `lem:out_eq_trivial_iff`). Kept
`private`/local to stay decoupled from the parallel `Place.lean` lane. -/

/-- If `w = (x ↦ v x ^ c)` as functions with `c > 0` and `v` is non-archimedean,
then so is `w`. The monotone map `t ↦ t ^ c` on `[0,∞)` commutes with `max`. -/
private theorem isNonarchimedean_of_rpow {K : Type*} [Field K]
    {v w : AbsoluteValue K ℝ} {c : ℝ} (hc : 0 < c)
    (hvw : (fun x => v x ^ c) = (w : K → ℝ)) (hv : IsNonarchimedean (v : K → ℝ)) :
    IsNonarchimedean (w : K → ℝ) := by
  intro x y
  have e : ∀ z : K, w z = v z ^ c := fun z => (congrFun hvw z).symm
  rw [e x, e y, e (x + y)]
  rcases le_total (v x) (v y) with h | h
  · have hxy : v (x + y) ≤ v y := le_trans (hv x y) (by rw [max_eq_right h])
    have : v (x + y) ^ c ≤ v y ^ c := Real.rpow_le_rpow (v.nonneg _) hxy hc.le
    exact le_trans this (le_max_right _ _)
  · have hxy : v (x + y) ≤ v x := le_trans (hv x y) (by rw [max_eq_left h])
    have : v (x + y) ^ c ≤ v x ^ c := Real.rpow_le_rpow (v.nonneg _) hxy hc.le
    exact le_trans this (le_max_left _ _)

/-- Non-archimedeanity is invariant under equivalence of absolute values. -/
private theorem isNonarchimedean_congr {K : Type*} [Field K]
    {v w : AbsoluteValue K ℝ} (h : v.IsEquiv w) :
    IsNonarchimedean (v : K → ℝ) ↔ IsNonarchimedean (w : K → ℝ) := by
  obtain ⟨c, hc, hcw⟩ := (AbsoluteValue.isEquiv_iff_exists_rpow_eq).mp h
  obtain ⟨d, hd, hdv⟩ := (AbsoluteValue.isEquiv_iff_exists_rpow_eq).mp h.symm
  exact ⟨isNonarchimedean_of_rpow hc hcw, isNonarchimedean_of_rpow hd hdv⟩

open Classical in
/-- The trivial absolute value is non-archimedean. -/
private theorem isNonarchimedean_trivial {K : Type*} [Field K] :
    IsNonarchimedean (AbsoluteValue.trivial : AbsoluteValue K ℝ) := by
  intro x y
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    simp only [zero_add, map_zero]
    exact le_max_of_le_right (le_refl _)
  · rcases eq_or_ne y 0 with hy | hy
    · subst hy
      simp only [add_zero, map_zero]
      exact le_max_of_le_left (le_refl _)
    · have hb : (AbsoluteValue.trivial : AbsoluteValue K ℝ) x = 1 := trivial_apply hx
      have hle : (AbsoluteValue.trivial : AbsoluteValue K ℝ) (x + y) ≤ 1 := by
        rcases eq_or_ne (x + y) 0 with hxy | hxy
        · rw [hxy, map_zero]; norm_num
        · rw [trivial_apply hxy]
      rw [hb]
      exact le_trans hle (le_max_left _ _)

/-- The underlying absolute value of a finite place is non-archimedean. -/
private theorem finitePlace_isNonarchimedean {K : Type*} [Field K] [NumberField K]
    (v : FinitePlace K) : IsNonarchimedean (v.val : K → ℝ) := by
  intro x y
  have := v.add_le x y
  rw [FinitePlace.coe_apply, FinitePlace.coe_apply, FinitePlace.coe_apply] at this
  exact this

/-- The underlying absolute value of an infinite place is *not* non-archimedean
(witness: it sends `2` to `2 > 1`). -/
private theorem infinitePlace_not_isNonarchimedean {K : Type*} [Field K] [NumberField K]
    (w : InfinitePlace K) : ¬ IsNonarchimedean (w.val : K → ℝ) := by
  intro h
  have h2 : (w.val : K → ℝ) ((2 : ℕ) : K) ≤ 1 := h.apply_natCast_le_one
  have key : (w.val : K → ℝ) ((2 : ℕ) : K) = 2 := by
    rw [← InfinitePlace.coe_apply, ← InfinitePlace.norm_embedding_eq, map_natCast]
    simp
  rw [key] at h2
  norm_num at h2

open Classical in
/-- The chosen representative `p.out` is trivial iff `p` is the trivial place. -/
private theorem out_eq_trivial_iff {K : Type*} [Field K] (p : AbsoluteValue.Place K) :
    p.out = (.trivial : AbsoluteValue K ℝ) ↔ p = TrivialPlace K := by
  constructor
  · intro h
    rw [← Quotient.out_eq p, h]
    rfl
  · intro h
    have : p.out ≈ (.trivial : AbsoluteValue K ℝ) := by
      rw [h]; exact Quotient.mk_out _
    exact (AbsoluteValue.isEquiv_trivial_iff_eq_trivial).mp this

/-! ### The classification iffs -/

open Classical in
theorem isInfinitePlace_iff' {K : Type*} [Field K] [NumberField K]
  (p : AbsoluteValue.Place K) (hp : p ≠ TrivialPlace K) :
  IsNonarchimedeanPlace p ↔
  ∃ v : FinitePlace K, p.out ≈ v.val := by
  constructor
  · -- forward: non-archimedean ⟹ a finite place exists
    intro hna
    -- `p.out` is nontrivial since `p ≠ TrivialPlace K`
    have hnt : p.out.IsNontrivial := by
      rw [isNontrivial_iff_ne_trivial]
      intro hcontra
      exact hp ((out_eq_trivial_iff p).mp hcontra)
    rcases ostrowski p.out hnt with ⟨w, hw⟩ | ⟨v, hv⟩
    · -- the infinite-place case is impossible: it would make `w.val` non-archimedean
      exfalso
      have hwna : IsNonarchimedean (w.val : K → ℝ) :=
        (isNonarchimedean_congr (hw : p.out.IsEquiv w.val)).mp hna
      exact infinitePlace_not_isNonarchimedean w hwna
    · exact ⟨v, hv⟩
  · -- backward: a finite place gives non-archimedeanity by transfer
    rintro ⟨v, hv⟩
    change IsNonarchimedean (p.out : K → ℝ)
    have hvna : IsNonarchimedean (v.val : K → ℝ) := finitePlace_isNonarchimedean v
    exact (isNonarchimedean_congr (hv : p.out.IsEquiv v.val)).mpr hvna

open Classical in
theorem isFinitePlace_iff' {K : Type*} [Field K] [NumberField K]
  (p : AbsoluteValue.Place K) :
  IsArchimedeanPlace p ↔
  ∃ v : InfinitePlace K, p.out ≈ v.val := by
  constructor
  · -- forward: archimedean ⟹ an infinite place exists
    intro harch
    change ¬ IsNonarchimedean (p.out : K → ℝ) at harch
    -- `p.out` is nontrivial: the trivial value is non-archimedean
    have hnt : p.out.IsNontrivial := by
      rw [isNontrivial_iff_ne_trivial]
      intro hcontra
      apply harch
      rw [hcontra]
      exact isNonarchimedean_trivial
    rcases ostrowski p.out hnt with ⟨w, hw⟩ | ⟨v, hv⟩
    · exact ⟨w, hw⟩
    · -- the finite-place case is impossible: it would make `p.out` non-archimedean
      exfalso
      apply harch
      have hvna : IsNonarchimedean (v.val : K → ℝ) := finitePlace_isNonarchimedean v
      exact (isNonarchimedean_congr (hv : p.out.IsEquiv v.val)).mpr hvna
  · -- backward: an infinite place forces archimedean by transfer
    rintro ⟨w, hw⟩
    change ¬ IsNonarchimedean (p.out : K → ℝ)
    intro hna
    have hwna : IsNonarchimedean (w.val : K → ℝ) :=
      (isNonarchimedean_congr (hw : p.out.IsEquiv w.val)).mp hna
    exact infinitePlace_not_isNonarchimedean w hwna

/-! ### Countability of places -/

open Classical in
/-- `Place K` is countable: classify each place as trivial, finite or infinite and
inject into `Option (InfinitePlace K ⊕ FinitePlace K)`, a countable type
(`InfinitePlace K` is a `Fintype`; `FinitePlace K` is countable via the height-one
spectrum of `𝓞 K`, itself countable because `𝓞 K` is a finite `ℤ`-module and
Noetherian). -/
instance instCountablePlace {K : Type*} [Field K] [NumberField K] :
    Countable (Place K) := by
  -- `FinitePlace K` is countable, via `HeightOneSpectrum (𝓞 K)` and `Ideal (𝓞 K)`.
  have hFinite : Countable (FinitePlace K) := by
    have hcount : Countable (𝓞 K) := Finsupp.Countable.of_moduleFinite (R := ℤ)
    have hideal : Countable (Ideal (𝓞 K)) := by
      -- `Ideal.span ∘ (↑·)` surjects `Finset (𝓞 K)` onto the (f.g.) ideals.
      have hsurj : Function.Surjective
          (fun s : Finset (𝓞 K) => Ideal.span (↑s : Set (𝓞 K))) := by
        intro I
        obtain ⟨s, hs⟩ := Ideal.fg_of_isNoetherianRing I
        exact ⟨s, hs⟩
      exact hsurj.countable
    have hheight : Countable (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
      IsDedekindDomain.HeightOneSpectrum.asIdeal_injective.countable
    exact Countable.of_equiv _ FinitePlace.equivHeightOneSpectrum.symm
  classical
  -- The classifying map: trivial ↦ none, non-archimedean ↦ inr (finite place),
  -- archimedean ↦ inl (infinite place).
  let f : Place K → Option (InfinitePlace K ⊕ FinitePlace K) := fun p =>
    if hp : p = TrivialPlace K then none
    else if hna : IsNonarchimedeanPlace p then
      Option.some (Sum.inr ((isInfinitePlace_iff' p hp).mp hna).choose)
    else
      Option.some (Sum.inl ((isFinitePlace_iff' p).mp hna).choose)
  refine Function.Injective.countable (f := f) ?_
  intro p q hpq
  simp only [f] at hpq
  by_cases hp : p = TrivialPlace K <;> by_cases hq : q = TrivialPlace K
  · rw [hp, hq]
  · exfalso
    rw [dif_pos hp] at hpq
    by_cases hqna : IsNonarchimedeanPlace q
    · rw [dif_neg hq, dif_pos hqna] at hpq; simp at hpq
    · rw [dif_neg hq, dif_neg hqna] at hpq; simp at hpq
  · exfalso
    rw [dif_pos hq] at hpq
    by_cases hpna : IsNonarchimedeanPlace p
    · rw [dif_neg hp, dif_pos hpna] at hpq; simp at hpq
    · rw [dif_neg hp, dif_neg hpna] at hpq; simp at hpq
  · rw [dif_neg hp, dif_neg hq] at hpq
    by_cases hpna : IsNonarchimedeanPlace p <;> by_cases hqna : IsNonarchimedeanPlace q
    · -- both non-archimedean: equal chosen finite places force `p.out ≈ q.out`
      rw [dif_pos hpna, dif_pos hqna] at hpq
      rw [Option.some_inj, Sum.inr.injEq] at hpq
      have hps := ((isInfinitePlace_iff' p hp).mp hpna).choose_spec
      have hqs := ((isInfinitePlace_iff' q hq).mp hqna).choose_spec
      rw [hpq] at hps
      exact Quotient.out_equiv_out.mp (hps.trans hqs.symm)
    · exfalso
      rw [dif_pos hpna, dif_neg hqna] at hpq; simp at hpq
    · exfalso
      rw [dif_neg hpna, dif_pos hqna] at hpq; simp at hpq
    · -- both archimedean: equal chosen infinite places force `p.out ≈ q.out`
      rw [dif_neg hpna, dif_neg hqna] at hpq
      rw [Option.some_inj, Sum.inl.injEq] at hpq
      have hps := ((isFinitePlace_iff' p).mp hpna).choose_spec
      have hqs := ((isFinitePlace_iff' q).mp hqna).choose_spec
      rw [hpq] at hps
      exact Quotient.out_equiv_out.mp (hps.trans hqs.symm)

/-! ### Infinitude of places -/

/-- For each rational prime `p` there is a height-one prime of `𝓞 K` lying over
`(p) ⊂ ℤ` (going-up for the integral extension `ℤ → 𝓞 K`). -/
private theorem exists_heightOne_over_prime {K : Type*} [Field K] [NumberField K]
    (p : ℕ) (hp : p.Prime) :
    ∃ Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Ideal.comap (algebraMap ℤ (𝓞 K)) Q.asIdeal = Ideal.span {(p : ℤ)} := by
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI hP : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpz).mpr hprime
  have hinj : Function.Injective (algebraMap ℤ (𝓞 K)) := RingHom.injective_int _
  have hbot : Ideal.comap (algebraMap ℤ (𝓞 K)) (⊥ : Ideal (𝓞 K)) ≤ Ideal.span {(p : ℤ)} := by
    rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le
  obtain ⟨Q, _hQge, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := ℤ) (S := 𝓞 K)
      (Ideal.span {(p : ℤ)}) (⊥ : Ideal (𝓞 K)) hbot
  -- `Q` is nonzero: it contracts to the nonzero ideal `(p)`.
  have hQne : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.comap_bot_of_injective _ hinj] at hQcomap
    have hpbot : Ideal.span {(p : ℤ)} = ⊥ := hQcomap.symm
    rw [Ideal.span_singleton_eq_bot] at hpbot
    exact hpz hpbot
  exact ⟨⟨Q, hQprime, hQne⟩, hQcomap⟩

/-- `HeightOneSpectrum (𝓞 K)` is infinite: the infinitely many rational primes embed
via going-up, with the contraction to `ℤ` recovering the prime. -/
instance infinite_heightOneSpectrum (K : Type*) [Field K] [NumberField K] :
    Infinite (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := by
  classical
  haveI : Infinite ↥{p : ℕ | p.Prime} := Nat.infinite_setOf_prime.to_subtype
  let g : ↥{p : ℕ | p.Prime} → IsDedekindDomain.HeightOneSpectrum (𝓞 K) := fun p =>
    (exists_heightOne_over_prime (K := K) p.1 p.2).choose
  refine Infinite.of_injective g ?_
  intro a b hab
  have ha := (exists_heightOne_over_prime (K := K) a.1 a.2).choose_spec
  have hb := (exists_heightOne_over_prime (K := K) b.1 b.2).choose_spec
  simp only [g] at hab
  rw [hab, hb] at ha
  -- `ha : span {b} = span {a}` in `ℤ`; equal spans of nonneg generators force `a = b`.
  have hval : a.1 = b.1 := by
    rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff] at ha
    rcases ha with h | h
    · exact_mod_cast h.symm
    · have ha0 : (a.1 : ℤ) > 0 := by exact_mod_cast a.2.pos
      have hb0 : (b.1 : ℤ) ≥ 0 := by positivity
      omega
  exact Subtype.ext hval

/-- For a finite place `v` and `x ∈ 𝓞 K`, `v.val x < 1` iff `x` lies in the maximal
ideal of `v`. Bridges the absolute value to ideal membership. -/
private theorem finitePlace_lt_one_iff_mem {K : Type*} [Field K] [NumberField K]
    (v : FinitePlace K) (x : 𝓞 K) :
    v.val (x : K) < 1 ↔ x ∈ (v.maximalIdeal).asIdeal := by
  rw [← FinitePlace.coe_apply, ← FinitePlace.norm_embedding_eq v (x : K)]
  exact FinitePlace.norm_lt_one_iff_mem K v.maximalIdeal x

/-- The map `FinitePlace K → Place K`, `v ↦ ⟦v.val⟧`, is injective: equivalent finite
places share `{x | v x < 1}`, hence the same maximal ideal, hence are equal. -/
private theorem finitePlace_injective_place {K : Type*} [Field K] [NumberField K] :
    Function.Injective (fun v : FinitePlace K => (Quotient.mk' v.val : Place K)) := by
  intro v w hvw
  have hequiv : v.val ≈ w.val := Quotient.eq'.mp hvw
  have hlt : ∀ x : K, v.val x < 1 ↔ w.val x < 1 := fun x =>
    (hequiv : v.val.IsEquiv w.val).lt_one_iff
  have hideal : v.maximalIdeal.asIdeal = w.maximalIdeal.asIdeal := by
    ext x
    rw [← finitePlace_lt_one_iff_mem, ← finitePlace_lt_one_iff_mem, hlt]
  have hmax : v.maximalIdeal = w.maximalIdeal := IsDedekindDomain.HeightOneSpectrum.ext hideal
  exact (FinitePlace.maximalIdeal_inj v w).mp hmax

/-- `Place K` is infinite: the finite places already are (infinitely many height-one
primes), and they inject into `Place K`. -/
instance instInfinitePlace {K : Type*} [Field K] [NumberField K] : Infinite (Place K) := by
  haveI hFinite : Infinite (FinitePlace K) :=
    (Equiv.infinite_iff FinitePlace.equivHeightOneSpectrum).mpr inferInstance
  exact Infinite.of_injective _ finitePlace_injective_place

/-! ### Finite support of the local contributions (`lem:numberfield_finite_support`)

For a fixed `x ≠ 0`, only finitely many places `ω` satisfy `ω.out x ≠ 1`. We split
`Place K` into archimedean and non-archimedean places using the Ostrowski
classification of `ExternalResults.Ostrowski` and bound each piece by a finite type. -/

/-- The archimedean locus is finite: an archimedean place injects into the Fintype
`InfinitePlace K` via the classification `isFinitePlace_iff'` (the assignment is
injective by `Quotient.out_equiv_out`, the same argument as `instCountablePlace`). -/
theorem finite_isArchimedeanPlace (K : Type u_1) [Field K] [NumberField K] :
    {ω : AbsoluteValue.Place K | IsArchimedeanPlace ω}.Finite := by
  classical
  rw [← Set.finite_coe_iff]
  -- send an archimedean place to its chosen infinite place
  let g : {ω : AbsoluteValue.Place K // IsArchimedeanPlace ω} → InfinitePlace K :=
    fun ω => ((isFinitePlace_iff' ω.1).mp ω.2).choose
  have hg : Function.Injective g := by
    intro a b hab
    have ha := ((isFinitePlace_iff' a.1).mp a.2).choose_spec
    have hb := ((isFinitePlace_iff' b.1).mp b.2).choose_spec
    simp only [g] at hab
    rw [hab] at ha
    have hout : a.1.out ≈ b.1.out := ha.trans hb.symm
    exact Subtype.ext (Quotient.out_equiv_out.mp hout)
  exact Finite.of_injective g hg

/-- The non-archimedean part of `{ω | ω.out x ≠ 1}` is finite: such a place is
non-trivial (the trivial place sends every nonzero `x` to `1`), so by
`isInfinitePlace_iff'` it has a finite place `v_ω` with `ω.out ≈ v_ω.val`; by
`AbsoluteValue.IsEquiv.eq_one_iff` we get `v_ω x ≠ 1`. The assignment `ω ↦ v_ω` is
injective, so this part injects into `{v : FinitePlace K | v x ≠ 1}`, which is finite
by `FinitePlace.hasFiniteMulSupport`. -/
theorem finite_isNonarchimedean_ne_one {K : Type u_1} [Field K] [NumberField K]
    {x : K} (hx : x ≠ 0) :
    {ω : AbsoluteValue.Place K | IsNonarchimedeanPlace ω ∧ ω.out x ≠ 1}.Finite := by
  classical
  -- the target finite set: finite places `v` with `v x ≠ 1` (its mul-support is finite)
  have htgt : {v : FinitePlace K | v x ≠ 1}.Finite :=
    NumberField.FinitePlace.hasFiniteMulSupport (K := K) hx
  rw [← Set.finite_coe_iff] at htgt ⊢
  -- every such `ω` is `≠ TrivialPlace K`
  have hne_trivial : ∀ ω : AbsoluteValue.Place K, IsNonarchimedeanPlace ω → ω.out x ≠ 1 →
      ω ≠ TrivialPlace K := by
    intro ω _ hω1 h
    apply hω1
    rw [h, trivialPlace_out_eq]
    exact AbsoluteValue.trivial_apply hx
  let g : {ω : AbsoluteValue.Place K // IsNonarchimedeanPlace ω ∧ ω.out x ≠ 1} →
      ↥{v : FinitePlace K | v x ≠ 1} := fun ω =>
    ⟨((isInfinitePlace_iff' ω.1 (hne_trivial ω.1 ω.2.1 ω.2.2)).mp ω.2.1).choose, by
      have hspec : ω.1.out ≈
          (((isInfinitePlace_iff' ω.1 (hne_trivial ω.1 ω.2.1 ω.2.2)).mp ω.2.1).choose).val :=
        ((isInfinitePlace_iff' ω.1 (hne_trivial ω.1 ω.2.1 ω.2.2)).mp ω.2.1).choose_spec
      have heq := (hspec : ω.1.out.IsEquiv _).eq_one_iff (x := x)
      simp only [Set.mem_setOf_eq]
      intro hc
      rw [FinitePlace.coe_apply] at hc
      exact ω.2.2 (heq.mpr hc)⟩
  have hg : Function.Injective g := by
    intro a b hab
    have hval :
        ((isInfinitePlace_iff' a.1 (hne_trivial a.1 a.2.1 a.2.2)).mp a.2.1).choose
        = ((isInfinitePlace_iff' b.1 (hne_trivial b.1 b.2.1 b.2.2)).mp b.2.1).choose :=
      congrArg Subtype.val hab
    have ha :=
      ((isInfinitePlace_iff' a.1 (hne_trivial a.1 a.2.1 a.2.2)).mp a.2.1).choose_spec
    have hb :=
      ((isInfinitePlace_iff' b.1 (hne_trivial b.1 b.2.1 b.2.2)).mp b.2.1).choose_spec
    rw [hval] at ha
    have hout : a.1.out ≈ b.1.out := ha.trans hb.symm
    exact Subtype.ext (Quotient.out_equiv_out.mp hout)
  exact Finite.of_injective g hg

/-- **`lem:numberfield_finite_support`.** For `x ≠ 0`, the set of places whose chosen
representative does not send `x` to `1` is finite. It is the union of the (finite)
archimedean locus and the (finite) non-archimedean part bounded above. -/
theorem finite_out_ne_one {K : Type u_1} [Field K] [NumberField K]
    {x : K} (hx : x ≠ 0) :
    {ω : AbsoluteValue.Place K | (Quotient.out ω : AbsoluteValue K ℝ) x ≠ 1}.Finite := by
  classical
  -- `T_x ⊆ (archimedean locus) ∪ (non-archimedean places with ω.out x ≠ 1)`
  apply Set.Finite.subset
    ((finite_isArchimedeanPlace K).union (finite_isNonarchimedean_ne_one (K := K) hx))
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  rcases place_classification ω with hna | harch
  · exact Or.inr ⟨hna, hω⟩
  · exact Or.inl harch

end NumberField
