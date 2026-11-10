/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.ExternalResults.Place
public import Mathlib.Analysis.Normed.Algebra.GelfandMazur
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Field.Ultra
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Countable
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.Ostrowski
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Instances.Rat

/-!
# Ostrowski-type classification of absolute values

This file proves the Gelfand–Tornheim/Ostrowski classification of complete archimedean
fields and derives Ostrowski's theorem for number fields, together with countability and
finite-support consequences for the set of places of a number field.

## Neukirch, ANT, Chapter II, Theorem 4.2 (Gelfand–Tornheim/Ostrowski)

A field complete with respect to an archimedean absolute value is `ℝ` or `ℂ`, with the
absolute value a power of the standard one. We follow the strategy of Neukirch's proof:

1. Normalization: `abs` restricted to `ℚ` is `|·| ^ s` for some `s ∈ (0,1]`
   (Ostrowski over `ℚ`; the `p`-adic case is excluded since `abs` is archimedean).
2. `abs ^ (1/s)` is again an absolute value (binomial expansion and `n`-th roots), so `K` is
   a normed field in which `ℚ` embeds isometrically; by completeness the embedding extends
   to an isometric `σ₀ : ℝ →+* K`, making `K` a normed `ℝ`-algebra.
3. Every element of `K` is quadratic over `ℝ`, so `K ≃ ℝ` or `K ≃ ℂ`: this is the
   Gelfand–Mazur theorem, `NormedAlgebra.Real.nonempty_algEquiv_or` in Mathlib (whose proof
   uses the same minimum-of-`‖ξ² - (z + conj z) * ξ + z * conj z‖` argument as Neukirch).
4. In the complex case the norm identity `‖σ a‖ = ‖a‖` follows since a continuous
   multiplicative function on `ℂ` fixing `|·|` on `ℝ` is trivial on the unit circle. -/

@[expose] public section

/-- An absolute value is nonarchimedean exactly when natural integers have value at most one. -/
theorem AbsoluteValue.isNonarchimedean_iff_natCast_le_one {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) : IsNonarchimedean v ↔ ∀ n : ℕ, v (n : K) ≤ 1 := by
  constructor
  · intro hv n
    exact hv.apply_natCast_le_one (map_zero_le v 1) (map_one v)
  · intro h
    let := v.toNormedField
    have : IsUltrametricDist K :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one h
    intro x y
    exact IsUltrametricDist.norm_add_le_max x y

/-- A field with an absolute value exceeding `1` somewhere on `ℕ` has characteristic zero
(in characteristic `p` the multiplicative group of the prime field is torsion, forcing
`abs ≤ 1` on `ℕ`). -/
private theorem neukirch_charZero {K : Type*} [Field K] (abs : AbsoluteValue K ℝ) {n₀ : ℕ}
    (h : 1 < abs (n₀ : K)) : CharZero K := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have := hp
  rcases CharP.char_is_prime_or_zero K p with hprime | hzero
  · exfalso
    have : Fact p.Prime := ⟨hprime⟩
    have hcast : (ZMod.castHom (dvd_refl p) K) ((n₀ : ZMod p)) = (n₀ : K) := map_natCast _ n₀
    by_cases h0 : (n₀ : ZMod p) = 0
    · rw [← hcast, h0, map_zero, map_zero] at h
      linarith
    · have h1 : ((n₀ : ZMod p)) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h0
      have h2 : abs ((n₀ : K)) ^ (p - 1) = 1 := by
        rw [← map_pow, ← hcast, ← map_pow, h1, map_one, map_one]
      have h3 : 1 < abs ((n₀ : K)) ^ (p - 1) :=
        one_lt_pow₀ h (Nat.sub_ne_zero_of_lt hprime.one_lt)
      rw [h2] at h3
      exact lt_irrefl 1 h3
  · have : CharP K 0 := hzero ▸ hp
    exact CharP.charP_to_charZero K

/-- On `ℚ`, an archimedean absolute value is a power `|·| ^ s` with `s ∈ (0, 1]`
(Ostrowski over `ℚ`). -/
private theorem neukirch_exists_rpow_rat {K : Type*} [Field K] [CharZero K]
    (abs : AbsoluteValue K ℝ) {n₀ : ℕ} (hn₀ : 1 < abs (n₀ : K)) :
    ∃ s : ℝ, s ∈ Set.Ioc 0 1 ∧ ∀ q : ℚ, abs (q : K) = |(q : ℝ)| ^ s := by
  -- the pullback of `abs` to `ℚ`
  let absQ : AbsoluteValue ℚ ℝ :=
    { toFun := fun q ↦ abs (q : K)
      map_mul' := fun q r ↦ by push_cast; exact abs.map_mul _ _
      nonneg' := fun q ↦ abs.nonneg _
      eq_zero' := fun q ↦ by rw [map_eq_zero, Rat.cast_eq_zero]
      add_le' := fun q r ↦ by push_cast; exact abs.add_le _ _ }
  have habsQ_apply : ∀ q : ℚ, absQ q = abs (q : K) := fun _ ↦ rfl
  have hn₀ne : (n₀ : ℚ) ≠ 0 := by
    rintro h0
    rw [show (n₀ : ℕ) = 0 from mod_cast h0] at hn₀
    simp only [Nat.cast_zero, map_zero] at hn₀
    linarith
  have hnontriv : absQ.IsNontrivial := by
    refine ⟨(n₀ : ℚ), hn₀ne, ?_⟩
    rw [habsQ_apply, Rat.cast_natCast]
    exact ne_of_gt hn₀
  rcases Rat.AbsoluteValue.equiv_real_or_padic absQ hnontriv with hreal | hpadic
  · -- real case: extract the exponent
    obtain ⟨c, hc, hfun⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hreal
    have hkey : ∀ q : ℚ, abs (q : K) = |(q : ℝ)| ^ c⁻¹ := by
      intro q
      have h1 : absQ q ^ c = Rat.AbsoluteValue.real q := congrFun hfun q
      have h2 : (absQ q ^ c) ^ c⁻¹ = absQ q :=
        Real.rpow_rpow_inv (absQ.nonneg q) (ne_of_gt hc)
      rw [h1, Rat.AbsoluteValue.real_eq_abs] at h2
      rw [← habsQ_apply q, ← h2, Rat.cast_abs]
    refine ⟨c⁻¹, ⟨inv_pos.mpr hc, ?_⟩, hkey⟩
    -- `s ≤ 1` since `abs 2 ≤ 2`
    have h2le : abs ((2 : ℚ) : K) ≤ 2 := by
      rw [show ((2 : ℚ) : K) = 1 + 1 by norm_num]
      calc abs (1 + 1 : K) ≤ abs 1 + abs 1 := abs.add_le 1 1
        _ = 2 := by rw [map_one]; norm_num
    rw [hkey 2] at h2le
    have h2' : (2 : ℝ) ^ c⁻¹ ≤ (2 : ℝ) ^ (1 : ℝ) := by
      rw [Real.rpow_one]
      simpa using h2le
    exact (Real.rpow_le_rpow_left_iff one_lt_two).mp h2'
  · -- p-adic case: impossible, `abs` exceeds 1 on ℕ
    exfalso
    obtain ⟨p, ⟨hfact, hequiv⟩, -⟩ := hpadic
    have := hfact
    have hle : absQ (n₀ : ℚ) ≤ 1 := by
      rw [(hequiv : absQ.IsEquiv _).le_one_iff]
      have := Rat.AbsoluteValue.padic_le_one p (n₀ : ℤ)
      simpa using this
    rw [habsQ_apply, Rat.cast_natCast] at hle
    linarith

/-- The triangle inequality for `abs ^ s⁻¹`, given that `abs` is `(·)^s` on `ℕ`:
binomial expansion plus `n`-th roots. -/
private theorem neukirch_rpow_inv_add_le {K : Type*} [Field K] (abs : AbsoluteValue K ℝ)
    {s : ℝ} (hs : 0 < s) (habsN : ∀ n : ℕ, abs (n : K) = (n : ℝ) ^ s) (x y : K) :
    abs (x + y) ^ s⁻¹ ≤ abs x ^ s⁻¹ + abs y ^ s⁻¹ := by
  have hsne : s ≠ 0 := ne_of_gt hs
  set A := abs x ^ s⁻¹ with hA
  set B := abs y ^ s⁻¹ with hB
  set T := abs (x + y) ^ s⁻¹ with hT
  have hA0 : 0 ≤ A := Real.rpow_nonneg (abs.nonneg x) _
  have hB0 : 0 ≤ B := Real.rpow_nonneg (abs.nonneg y) _
  have hT0 : 0 ≤ T := Real.rpow_nonneg (abs.nonneg _) _
  have hS0 : 0 ≤ A + B := by linarith
  have hAs : abs x = A ^ s := (Real.rpow_inv_rpow (abs.nonneg x) hsne).symm
  have hBs : abs y = B ^ s := (Real.rpow_inv_rpow (abs.nonneg y) hsne).symm
  -- `(u ^ t) ^ k = (u ^ k) ^ t` for `u ≥ 0`
  have hcomm : ∀ (t u : ℝ), 0 ≤ u → ∀ k : ℕ, (u ^ t) ^ k = (u ^ k) ^ t := by
    intro t u hu k
    rw [← Real.rpow_natCast (u ^ t) k, ← Real.rpow_natCast u k, ← Real.rpow_mul hu,
      ← Real.rpow_mul hu, mul_comm]
  -- the key estimate: `abs (x+y) ^ n ≤ (n+1) * ((A+B)^n) ^ s`
  have key : ∀ n : ℕ, abs (x + y) ^ n ≤ ((n : ℝ) + 1) * ((A + B) ^ n) ^ s := by
    intro n
    have h1 : abs ((x + y) ^ n) ≤
        ∑ k ∈ Finset.range (n + 1), abs (x ^ k * y ^ (n - k) * ((n.choose k : ℕ) : K)) := by
      rw [add_pow]
      exact abs.sum_le _ _
    have h2 : ∀ k ∈ Finset.range (n + 1),
        abs (x ^ k * y ^ (n - k) * ((n.choose k : ℕ) : K))
          = (A ^ k * B ^ (n - k) * (n.choose k : ℝ)) ^ s := by
      intro k _
      rw [map_mul, map_mul, map_pow, map_pow, habsN, hAs, hBs,
        hcomm s A hA0 k, hcomm s B hB0 (n - k),
        ← Real.mul_rpow (pow_nonneg hA0 k) (pow_nonneg hB0 (n - k)),
        ← Real.mul_rpow (mul_nonneg (pow_nonneg hA0 k) (pow_nonneg hB0 (n - k)))
          (Nat.cast_nonneg _)]
    have h3 : ∀ k ∈ Finset.range (n + 1),
        (A ^ k * B ^ (n - k) * (n.choose k : ℝ)) ^ s ≤ ((A + B) ^ n) ^ s := by
      intro k hk
      apply Real.rpow_le_rpow (by positivity) _ hs.le
      calc A ^ k * B ^ (n - k) * (n.choose k : ℝ)
          ≤ ∑ j ∈ Finset.range (n + 1), A ^ j * B ^ (n - j) * (n.choose j : ℝ) :=
            Finset.single_le_sum (f := fun j ↦ A ^ j * B ^ (n - j) * (n.choose j : ℝ))
              (fun j _ ↦ by positivity) hk
        _ = (A + B) ^ n := (add_pow A B n).symm
    calc abs (x + y) ^ n = abs ((x + y) ^ n) := (map_pow abs _ n).symm
      _ ≤ ∑ k ∈ Finset.range (n + 1), abs (x ^ k * y ^ (n - k) * ((n.choose k : ℕ) : K)) := h1
      _ = ∑ k ∈ Finset.range (n + 1), (A ^ k * B ^ (n - k) * (n.choose k : ℝ)) ^ s :=
          Finset.sum_congr rfl h2
      _ ≤ ∑ _k ∈ Finset.range (n + 1), ((A + B) ^ n) ^ s := Finset.sum_le_sum h3
      _ = ((n : ℝ) + 1) * ((A + B) ^ n) ^ s := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- take `n`-th roots: `T ≤ (n+1) ^ (s⁻¹ * n⁻¹) * (A + B)`
  have hroot : ∀ n : ℕ, n ≠ 0 → T ≤ ((n : ℝ) + 1) ^ (s⁻¹ * (n : ℝ)⁻¹) * (A + B) := by
    intro n hn
    have h1 : T ^ n ≤ ((n : ℝ) + 1) ^ s⁻¹ * (A + B) ^ n := by
      have h2 : T ^ n = (abs (x + y) ^ n) ^ s⁻¹ := by
        rw [hT, hcomm s⁻¹ _ (abs.nonneg _) n]
      rw [h2]
      calc (abs (x + y) ^ n) ^ s⁻¹
          ≤ (((n : ℝ) + 1) * ((A + B) ^ n) ^ s) ^ s⁻¹ := by
            apply Real.rpow_le_rpow (by positivity) (key n) (by positivity)
        _ = ((n : ℝ) + 1) ^ s⁻¹ * (((A + B) ^ n) ^ s) ^ s⁻¹ := by
            rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg (by positivity) _)]
        _ = ((n : ℝ) + 1) ^ s⁻¹ * (A + B) ^ n := by
            rw [Real.rpow_rpow_inv (by positivity) hsne]
    calc T = (T ^ n) ^ ((n : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hT0 hn).symm
      _ ≤ (((n : ℝ) + 1) ^ s⁻¹ * (A + B) ^ n) ^ ((n : ℝ)⁻¹) := by
          apply Real.rpow_le_rpow (by positivity) h1 (by positivity)
      _ = (((n : ℝ) + 1) ^ s⁻¹) ^ ((n : ℝ)⁻¹) * ((A + B) ^ n) ^ ((n : ℝ)⁻¹) := by
          rw [Real.mul_rpow (Real.rpow_nonneg (by positivity) _) (by positivity)]
      _ = ((n : ℝ) + 1) ^ (s⁻¹ * (n : ℝ)⁻¹) * (A + B) := by
          rw [← Real.rpow_mul (by positivity), Real.pow_rpow_inv_natCast hS0 hn]
  -- pass to the limit `n → ∞`
  have htend : Filter.Tendsto
      (fun n : ℕ ↦ ((n : ℝ) + 1) ^ (s⁻¹ * (n : ℝ)⁻¹) * (A + B))
      Filter.atTop (nhds (1 * (A + B))) := by
    apply Filter.Tendsto.mul_const
    have hcomp : Filter.Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have hbase := (tendsto_rpow_div_mul_add s⁻¹ 1 (-1) (by norm_num)).comp hcomp
    convert hbase using 2 with n
    rw [Function.comp_apply]
    congr 1
    ring
  rw [one_mul] at htend
  exact ge_of_tendsto htend (Filter.eventually_atTop.mpr
    ⟨1, fun n hn ↦ hroot n (Nat.one_le_iff_ne_zero.mp hn)⟩)

/-- A continuous ring homomorphism `ℂ →+* L` into a normed field that is isometric on `ℝ`
is isometric: multiplicativity forces triviality on the unit circle. -/
private theorem neukirch_norm_complex_ringHom {L : Type*} [NormedField L] (ψ : ℂ →+* L)
    (hcont : Continuous ψ) (hreal : ∀ r : ℝ, ‖ψ (r : ℂ)‖ = |r|) (z : ℂ) : ‖ψ z‖ = ‖z‖ := by
  -- `‖ψ ζ‖ ≤ 1` for `ζ` on the unit circle
  have hle : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖ψ ζ‖ ≤ 1 := by
    obtain ⟨w₀, hw₀mem, hw₀⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMaxOn
      ⟨1, by simp⟩ (continuous_norm.comp hcont).continuousOn
    intro ζ hζ
    by_contra hgt
    push Not at hgt
    obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop
      ‖ψ w₀‖).exists
    have hmem : ζ ^ k ∈ Metric.sphere (0 : ℂ) 1 := by
      simp [norm_pow, hζ]
    have hbound : ‖ψ (ζ ^ k)‖ ≤ ‖ψ w₀‖ := hw₀ hmem
    rw [map_pow, norm_pow] at hbound
    linarith
  -- hence `‖ψ ζ‖ = 1` on the unit circle
  have hone : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖ψ ζ‖ = 1 := by
    intro ζ hζ
    have hζ0 : ζ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hζ
      norm_num at hζ
    have hprod : ‖ψ ζ‖ * ‖ψ ζ⁻¹‖ = 1 := by
      rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hζ0, map_one, norm_one]
    have hinv : ‖ψ ζ⁻¹‖ ≤ 1 := hle _ (by rw [norm_inv, hζ]; norm_num)
    have h1 := hle ζ hζ
    nlinarith [norm_nonneg (ψ ζ), norm_nonneg (ψ ζ⁻¹)]
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  · have hdecomp : z = ((‖z‖ : ℝ) : ℂ) * (z / ((‖z‖ : ℝ) : ℂ)) := by
      have hnz : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
        simpa using norm_ne_zero_iff.mpr hz0
      field_simp
    calc ‖ψ z‖ = ‖ψ (((‖z‖ : ℝ) : ℂ)) * ψ (z / ((‖z‖ : ℝ) : ℂ))‖ := by
          rw [← map_mul, ← hdecomp]
      _ = ‖ψ (((‖z‖ : ℝ) : ℂ))‖ * ‖ψ (z / ((‖z‖ : ℝ) : ℂ))‖ := norm_mul _ _
      _ = ‖z‖ * 1 := by
          rw [hreal, abs_of_nonneg (norm_nonneg z), hone _ (by
            rw [norm_div]
            simp [norm_ne_zero_iff.mpr hz0])]
      _ = ‖z‖ := mul_one _

/-- The endgame of the proof of Theorem 4.2 over a genuine `NormedAlgebra ℝ K` instance:
Gelfand–Mazur gives `K ≃ₐ[ℝ] ℝ` or `K ≃ₐ[ℝ] ℂ`, and the absolute value is the `s`-th
power of the norm on the other side. -/
private theorem neukirch_final_aux {K : Type*} [NormedField K] [NormedAlgebra ℝ K]
    (abs : AbsoluteValue K ℝ) {s : ℝ} (hs : s ∈ Set.Ioc 0 1)
    (habs' : ∀ x : K, abs x = ‖x‖ ^ s)
    (halgnorm : ∀ r : ℝ, ‖algebraMap ℝ K r‖ = |r|)
    (halgcont : Continuous (algebraMap ℝ K)) :
    (∃ σ : K ≃+* ℝ, ∃ s : ℝ, s ∈ Set.Ioc 0 1 ∧ ∀ a : K, abs a = ‖σ a‖ ^ s) ∨
    (∃ σ : K ≃+* ℂ, ∃ s : ℝ, s ∈ Set.Ioc 0 1 ∧ ∀ a : K, abs a = ‖σ a‖ ^ s) := by
  rcases NormedAlgebra.Real.nonempty_algEquiv_or K with h | h
  · -- real case
    obtain ⟨φ⟩ := h
    left
    refine ⟨φ.toRingEquiv, s, hs, fun a ↦ ?_⟩
    have h1 : φ.symm (φ a) = a := φ.symm_apply_apply a
    have h2 : φ.symm (φ a) = algebraMap ℝ K (φ a) := by
      have h3 := φ.symm.commutes (φ a)
      simpa using h3
    have ha : a = algebraMap ℝ K (φ a) := by rw [← h2, h1]
    calc abs a = ‖a‖ ^ s := habs' a
      _ = ‖algebraMap ℝ K (φ a)‖ ^ s := by rw [← ha]
      _ = |φ a| ^ s := by rw [halgnorm]
      _ = ‖φ.toRingEquiv a‖ ^ s := by rw [Real.norm_eq_abs]; rfl
  · -- complex case
    obtain ⟨φ⟩ := h
    right
    refine ⟨φ.toRingEquiv, s, hs, fun a ↦ ?_⟩
    let ψ : ℂ →+* K := φ.symm.toRingEquiv.toRingHom
    have hψapp : ∀ z : ℂ, ψ z = φ.symm z := fun _ ↦ rfl
    have hψreal : ∀ r : ℝ, ψ ((r : ℂ)) = algebraMap ℝ K r := by
      intro r
      have h1 := φ.symm.commutes r
      rw [hψapp]
      simpa [Complex.coe_algebraMap] using h1
    have hψcont : Continuous ⇑ψ := by
      have hformula : ∀ z : ℂ,
          ψ z = algebraMap ℝ K z.re + algebraMap ℝ K z.im * ψ Complex.I := by
        intro z
        conv_lhs => rw [show z = (z.re : ℂ) + (z.im : ℂ) * Complex.I from
          (Complex.re_add_im z).symm]
        rw [map_add, map_mul, hψreal, hψreal]
      rw [show ⇑ψ = fun z : ℂ =>
        algebraMap ℝ K z.re + algebraMap ℝ K z.im * ψ Complex.I from funext hformula]
      exact (halgcont.comp Complex.continuous_re).add
        ((halgcont.comp Complex.continuous_im).mul continuous_const)
    have hψnorm : ∀ z : ℂ, ‖ψ z‖ = ‖z‖ :=
      neukirch_norm_complex_ringHom ψ hψcont (fun r ↦ by rw [hψreal, halgnorm])
    have ha : a = ψ (φ a) := by
      rw [hψapp]
      exact (φ.symm_apply_apply a).symm
    calc abs a = ‖a‖ ^ s := habs' a
      _ = ‖ψ (φ a)‖ ^ s := by rw [← ha]
      _ = ‖φ.toRingEquiv a‖ ^ s := by rw [hψnorm]; rfl

/-- The endgame of the proof of Theorem 4.2: a complete normed field containing `ℝ`
isometrically is `ℝ` or `ℂ` (Gelfand–Mazur), and the absolute value is the corresponding
power of the norm. -/
private theorem neukirch_final {K : Type*} [NormedField K]
    (abs : AbsoluteValue K ℝ) {s : ℝ} (hs : s ∈ Set.Ioc 0 1)
    (habs' : ∀ x : K, abs x = ‖x‖ ^ s)
    (σ₀ : ℝ →+* K) (hσ₀cont : Continuous ⇑σ₀) (hσ₀norm : ∀ r : ℝ, ‖σ₀ r‖ = |r|) :
    (∃ σ : K ≃+* ℝ, ∃ s : ℝ, s ∈ Set.Ioc 0 1 ∧ ∀ a : K, abs a = ‖σ a‖ ^ s) ∨
    (∃ σ : K ≃+* ℂ, ∃ s : ℝ, s ∈ Set.Ioc 0 1 ∧ ∀ a : K, abs a = ‖σ a‖ ^ s) := by
  let : Algebra ℝ K := σ₀.toAlgebra
  let : NormedAlgebra ℝ K :=
    { norm_smul_le := fun r x ↦ le_of_eq (by
        rw [Algebra.smul_def, norm_mul,
          show (algebraMap ℝ K) r = σ₀ r from rfl, hσ₀norm, Real.norm_eq_abs]) }
  exact neukirch_final_aux abs hs habs' (fun r ↦ hσ₀norm r) hσ₀cont

/-- **Gelfand–Tornheim / Ostrowski** (J. Neukirch, *Algebraic Number Theory*, Chapter II,
Theorem 4.2): a field complete with respect to an archimedean absolute value is `ℝ` or `ℂ`,
with the absolute value a power of the standard one. -/
theorem AbsoluteValue.exists_ringEquiv_real_or_complex_of_complete {K : Type*} [Field K]
    (abs : AbsoluteValue K ℝ) (habs : ¬IsNonarchimedean abs) (hK : CauSeq.IsComplete K abs) :
    (∃ σ : K ≃+* ℝ, ∃ s : ℝ, s ∈ Set.Ioc 0 1 ∧ ∀ a : K, abs a = ‖σ a‖ ^ s) ∨
      ∃ σ : K ≃+* ℂ, ∃ s : ℝ, s ∈ Set.Ioc 0 1 ∧ ∀ a : K, abs a = ‖σ a‖ ^ s := by
  -- Step 0: some natural number has absolute value `> 1`; characteristic zero
  have hnat : ∃ n : ℕ, 1 < abs (n : K) := by
    by_contra h
    push Not at h
    exact habs ((AbsoluteValue.isNonarchimedean_iff_natCast_le_one abs).mpr h)
  obtain ⟨n₀, hn₀⟩ := hnat
  have : CharZero K := neukirch_charZero abs hn₀
  -- Step 1: on `ℚ`, `abs` is the `s`-th power of the usual absolute value
  obtain ⟨s, hs, habsQ⟩ := neukirch_exists_rpow_rat abs hn₀
  have hs0 : 0 < s := hs.1
  have hsne : s ≠ 0 := ne_of_gt hs0
  have habsN : ∀ n : ℕ, abs (n : K) = (n : ℝ) ^ s := by
    intro n
    have h := habsQ (n : ℚ)
    rwa [Rat.cast_natCast, Rat.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)] at h
  -- Step 2: the renormalized absolute value `absC = abs ^ (1/s)`
  let absC : AbsoluteValue K ℝ :=
    { toFun := fun x ↦ abs x ^ s⁻¹
      map_mul' := fun x y ↦ by
        rw [map_mul, Real.mul_rpow (abs.nonneg x) (abs.nonneg y)]
      nonneg' := fun x ↦ Real.rpow_nonneg (abs.nonneg x) _
      eq_zero' := fun x ↦ by
        rw [Real.rpow_eq_zero (abs.nonneg x) (inv_ne_zero hsne), map_eq_zero]
      add_le' := neukirch_rpow_inv_add_le abs hs0 habsN }
  have habsC : ∀ x : K, absC x = abs x ^ s⁻¹ := fun _ ↦ rfl
  have habsC_s : ∀ x : K, abs x = absC x ^ s := fun x =>
    (Real.rpow_inv_rpow (abs.nonneg x) hsne).symm
  have habsCQ : ∀ q : ℚ, absC (q : K) = |(q : ℝ)| := by
    intro q
    rw [habsC, habsQ, Real.rpow_rpow_inv (abs_nonneg _) hsne]
  -- Step 3: normed field structure from `absC`; completeness
  let := absC.toNormedField
  have hnorm : ∀ x : K, ‖x‖ = absC x := fun _ ↦ rfl
  have : CompleteSpace K := by
    apply Metric.complete_of_cauchySeq_tendsto
    intro u hu
    have hcau : IsCauSeq ⇑abs u := by
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hu (ε ^ s⁻¹)
        (Real.rpow_pos_of_pos hε _)
      refine ⟨N, fun j hj ↦ ?_⟩
      have h1 := hN j hj
      rw [dist_eq_norm, hnorm, habsC] at h1
      calc abs (u j - u N) = (abs (u j - u N) ^ s⁻¹) ^ s :=
            (Real.rpow_inv_rpow (abs.nonneg _) hsne).symm
        _ < (ε ^ s⁻¹) ^ s := Real.rpow_lt_rpow (Real.rpow_nonneg (abs.nonneg _) _) h1 hs0
        _ = ε := Real.rpow_inv_rpow hε.le hsne
    have := hK
    obtain ⟨b, hb⟩ := CauSeq.complete (⟨u, hcau⟩ : CauSeq K ⇑abs)
    refine ⟨b, ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hb (ε ^ s) (Real.rpow_pos_of_pos hε _)
    refine ⟨N, fun j hj ↦ ?_⟩
    have h2 := hN j hj
    change abs (u j - b) < ε ^ s at h2
    rw [dist_eq_norm, hnorm, habsC]
    calc abs (u j - b) ^ s⁻¹ < (ε ^ s) ^ s⁻¹ :=
          Real.rpow_lt_rpow (abs.nonneg _) h2 (by positivity)
      _ = ε := Real.rpow_rpow_inv hε.le hsne
  -- Step 4: the isometric embedding `σ₀ : ℝ →+* K`
  have hue : IsUniformInducing ⇑(Rat.castHom ℝ) := by
    have h : ⇑(Rat.castHom ℝ) = ((↑) : ℚ → ℝ) := funext fun q ↦ rfl
    rw [h]
    exact Rat.isUniformEmbedding_coe_real.isUniformInducing
  have hdr : DenseRange ⇑(Rat.castHom ℝ) := by
    have h : ⇑(Rat.castHom ℝ) = ((↑) : ℚ → ℝ) := funext fun q ↦ rfl
    rw [h]
    exact Rat.denseRange_cast
  have hfu : UniformContinuous ⇑(Rat.castHom K) := by
    apply Isometry.uniformContinuous
    apply Isometry.of_dist_eq
    intro q r
    have hcast : (Rat.castHom K) q - (Rat.castHom K) r = ((q - r : ℚ) : K) := by
      rw [show (Rat.castHom K) q = (q : K) from rfl, show (Rat.castHom K) r = (r : K) from rfl]
      push_cast
      ring
    rw [dist_eq_norm, hcast, hnorm, habsCQ, Rat.dist_eq]
    push_cast
    ring_nf
  let σ₀ : ℝ →+* K := IsDenseInducing.extendRingHom hue hdr hfu
  have hσ₀coe : ⇑σ₀ = (hue.isDenseInducing hdr).extend ⇑(Rat.castHom K) := rfl
  have hσ₀cont : Continuous ⇑σ₀ := by
    rw [hσ₀coe]
    exact (uniformContinuous_uniformly_extend hue hdr hfu).continuous
  have hσ₀rat : ∀ q : ℚ, σ₀ ((q : ℝ)) = (q : K) := by
    intro q
    have h := (hue.isDenseInducing hdr).extend_eq hfu.continuous q
    rw [hσ₀coe]
    exact h
  have hσ₀norm : ∀ r : ℝ, ‖σ₀ r‖ = |r| := by
    have heq : (fun r : ℝ ↦ ‖σ₀ r‖) = fun r : ℝ ↦ |r| := by
      apply hdr.equalizer (continuous_norm.comp hσ₀cont) continuous_abs
      funext q
      change ‖σ₀ ((q : ℝ))‖ = |((q : ℝ))|
      rw [hσ₀rat, hnorm, habsCQ]
    exact fun r ↦ congrFun heq r
  -- Steps 5–6: Gelfand–Mazur and the conclusion
  exact neukirch_final abs hs (fun x ↦ by rw [hnorm x]; exact habsC_s x) σ₀ hσ₀cont hσ₀norm

/-- The completion of a field with an absolute value is complete in the sense of `CauSeq`,
with respect to the absolute value induced by the completion norm. -/
theorem CauSeq.isComplete_completion {K : Type*} [Field K] (abs : AbsoluteValue K ℝ) :
    let _ := abs.toNormedField;
    CauSeq.IsComplete (UniformSpace.Completion K)
      ⇑(NormedField.toAbsoluteValue (UniformSpace.Completion K)) := by
  let := abs.toNormedField
  let : CauSeq.IsComplete (UniformSpace.Completion K) norm := by
    refine ⟨fun f ↦ ?_⟩
    have hf : CauchySeq (f : ℕ → UniformSpace.Completion K) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := f.2.cauchy₂ hε
      exact ⟨N, fun m hm n hn ↦ by simpa [dist_eq_norm] using hN m hm n hn⟩
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hf
    refine ⟨x, ?_⟩
    rw [Metric.tendsto_atTop] at hx
    intro ε hε
    obtain ⟨N, hN⟩ := hx ε hε
    exact ⟨N, fun j hj ↦ by simpa [dist_eq_norm] using hN j hj⟩
  simpa only [NormedField.toAbsoluteValue, AbsoluteValue.coe_mk, MulHom.coe_mk] using
    (inferInstance : CauSeq.IsComplete (UniformSpace.Completion K) norm)

namespace NumberField
open AbsoluteValue

/-! ### Ostrowski's theorem for number fields

We follow K. Conrad, *Ostrowski for number fields*, Theorem 3.

* Nonarchimedean case (Conrad, Theorem 2): `abs ≤ 1` on `𝓞 K` (integrality argument), so
  `𝔭 = {α ∈ 𝓞 K | abs α < 1}` is a nonzero prime ideal. Writing `y ∈ K` with `y·d = n` where
  `d ∉ 𝔭` (Conrad, Lemma 1, provided by `exists_primeCompl_mul_eq_of_integer`), any `y` with
  `𝔭`-adic absolute value `< 1` also has `abs y < 1`, which by `isEquiv_of_lt_one_imp` makes
  `abs` equivalent to the finite place attached to `𝔭`.
* Archimedean case (Conrad defers to the references; we use
  `exists_ringEquiv_real_or_complex_of_complete`): the completion of `K` is a complete
  archimedean field, hence a subfield-with-power-`s` of `ℝ` or `ℂ`; composing with `K → K̂`
  yields a complex embedding of `K` whose infinite place is equivalent to `abs`. -/

/-- A nonarchimedean absolute value is bounded by `1` on elements that are integral over `ℤ`
(Conrad, proof of Theorem 2: nonnegativity of `-log abs` on algebraic integers). -/
theorem abs_le_one_of_isIntegral {K : Type*} [Field K] {abs : AbsoluteValue K ℝ}
    (hna : IsNonarchimedean abs) {x : K} (hx : IsIntegral ℤ x) : abs x ≤ 1 := by
  by_contra hgt
  push Not at hgt
  obtain ⟨p, hpm, hpe⟩ := hx
  set n := p.natDegree with hn
  -- `aeval x p = 0` written as a `Finset.range` sum
  have hsum : ∑ i ∈ Finset.range (n + 1), (p.coeff i : K) * x ^ i = 0 := by
    have h := (Polynomial.aeval_eq_sum_range (R := ℤ) (S := K) (p := p) x).symm
    rw [Polynomial.aeval_def, hpe] at h
    simpa only [zsmul_eq_mul] using h
  -- the degree is positive (a monic constant cannot vanish)
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0] at hsum
      simp only [zero_add, Finset.sum_range_one, pow_zero, mul_one] at hsum
      have hc : p.coeff 0 = 1 := by
        have h1 := hpm.coeff_natDegree
        rwa [← hn, h0] at h1
      rw [hc] at hsum
      norm_num at hsum
    · exact h0
  -- `x ^ n = -∑_{i < n} aᵢ x ^ i`
  have hxn : x ^ n = -∑ i ∈ Finset.range n, (p.coeff i : K) * x ^ i := by
    have h := hsum
    rw [Finset.sum_range_succ] at h
    have hc : p.coeff n = 1 := by rw [hn]; exact hpm.coeff_natDegree
    rw [hc, Int.cast_one, one_mul] at h
    exact eq_neg_of_add_eq_zero_right h
  -- pick the dominating term of the sum
  obtain ⟨j, hj_mem, hj_le⟩ :=
    hna.finset_image_add_of_nonempty (fun i ↦ (p.coeff i : K) * x ^ i)
      (show (Finset.range n).Nonempty from ⟨0, Finset.mem_range.mpr hn0⟩)
  have hj_lt : j < n := Finset.mem_range.mp hj_mem
  have key : abs x ^ n ≤ abs x ^ j :=
    calc abs x ^ n = abs (x ^ n) := (map_pow abs x n).symm
      _ = abs (∑ i ∈ Finset.range n, (p.coeff i : K) * x ^ i) := by rw [hxn, abs.map_neg]
      _ ≤ abs ((p.coeff j : K) * x ^ j) := hj_le
      _ = abs ((p.coeff j : K)) * abs x ^ j := by rw [map_mul, map_pow]
      _ ≤ 1 * abs x ^ j := by
          have := hna.apply_intCast_le_one (map_zero_le abs 1) (map_one abs) abs.map_neg
            (n := p.coeff j)
          gcongr
      _ = abs x ^ j := one_mul _
  exact absurd key (not_le.mpr (pow_lt_pow_right₀ hgt hj_lt))

/-- The nonarchimedean half of Ostrowski: a nontrivial nonarchimedean absolute value on a
number field is equivalent to a finite place (Conrad, Theorems 2 and 3). -/
theorem exists_finitePlace_of_isNonarchimedean {K : Type*} [Field K] [NumberField K]
    {abs : AbsoluteValue K ℝ} (habs : abs.IsNontrivial) (hna : IsNonarchimedean abs) :
    ∃ v : FinitePlace K, abs ≈ v.val := by
  -- all algebraic integers have absolute value at most 1
  have hle : ∀ α : 𝓞 K, abs (algebraMap (𝓞 K) K α) ≤ 1 := fun α =>
    abs_le_one_of_isIntegral hna (RingOfIntegers.isIntegral_coe α)
  -- the prime ideal `𝔭 = {α | abs α < 1}` of Conrad's Theorem 2
  let 𝔭 : Ideal (𝓞 K) :=
    { carrier := {α : 𝓞 K | abs (algebraMap (𝓞 K) K α) < 1}
      add_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_ofPred_eq, map_add] at *
        exact lt_of_le_of_lt (hna _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c {a} ha ↦ by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
        calc abs (algebraMap (𝓞 K) K c) * abs (algebraMap (𝓞 K) K a)
            ≤ 1 * abs (algebraMap (𝓞 K) K a) :=
              mul_le_mul_of_nonneg_right (hle c) (abs.nonneg _)
          _ = abs (algebraMap (𝓞 K) K a) := one_mul _
          _ < 1 := ha }
  have hmem : ∀ α : 𝓞 K, α ∈ 𝔭 ↔ abs (algebraMap (𝓞 K) K α) < 1 := fun _ ↦ Iff.rfl
  -- `𝔭` is prime
  have h𝔭_prime : 𝔭.IsPrime := by
    rw [Ideal.isPrime_iff]
    constructor
    · rw [Ideal.ne_top_iff_one]
      intro h1
      have h2 := (hmem 1).mp h1
      rw [map_one, map_one] at h2
      exact lt_irrefl 1 h2
    · intro a b hab
      by_contra hcon
      push Not at hcon
      obtain ⟨ha, hb⟩ := hcon
      have ha1 : abs (algebraMap (𝓞 K) K a) = 1 :=
        le_antisymm (hle a) (not_lt.mp fun hlt ↦ ha ((hmem a).mpr hlt))
      have hb1 : abs (algebraMap (𝓞 K) K b) = 1 :=
        le_antisymm (hle b) (not_lt.mp fun hlt ↦ hb ((hmem b).mpr hlt))
      have h2 := (hmem (a * b)).mp hab
      rw [map_mul, map_mul, ha1, hb1, one_mul] at h2
      exact lt_irrefl 1 h2
  -- `𝔭` is nonzero: from nontriviality find a nonzero integer of absolute value `< 1`
  obtain ⟨x, hx0, hx1⟩ := habs.exists_abv_lt_one
  obtain ⟨a, b, hbmem, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hbne : algebraMap (𝓞 K) K b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr (nonZeroDivisors.ne_zero hbmem)
  have haeq : algebraMap (𝓞 K) K a = x * algebraMap (𝓞 K) K b := (div_eq_iff hbne).mp hab
  have ha_lt : abs (algebraMap (𝓞 K) K a) < 1 := by
    rw [haeq, map_mul]
    calc abs x * abs (algebraMap (𝓞 K) K b) ≤ abs x * 1 :=
          mul_le_mul_of_nonneg_left (hle b) (abs.nonneg x)
      _ = abs x := mul_one _
      _ < 1 := hx1
  have ha_ne : a ≠ 0 := by
    intro h
    rw [h, map_zero] at haeq
    rcases mul_eq_zero.mp haeq.symm with h' | h'
    · exact hx0 h'
    · exact hbne h'
  have ha_mem : a ∈ 𝔭 := (hmem a).mpr ha_lt
  have h𝔭_ne_bot : 𝔭 ≠ ⊥ := Submodule.ne_bot_iff 𝔭 |>.mpr ⟨a, ha_mem, ha_ne⟩
  -- the corresponding height-one prime and finite place
  let P : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := ⟨𝔭, h𝔭_prime, h𝔭_ne_bot⟩
  -- the key implication: `𝔭`-adically small elements are `abs`-small (via Conrad's Lemma 1)
  have hkey : ∀ y : K, (FinitePlace.mk P).val y < 1 → abs y < 1 := by
    intro y hy
    have h1 : ‖FinitePlace.embedding P y‖ < 1 := hy
    rw [FinitePlace.norm_embedding'] at h1
    have hval : P.valuation K y < 1 :=
      (WithZeroMulInt.toNNReal_lt_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal P)).mp
        (by exact_mod_cast h1)
    -- Conrad's Lemma 1: `y = n / d` with `d ∉ 𝔭`
    obtain ⟨m, d, hnd⟩ :=
      IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
        (v := P) (x := y) hval.le
    have hd_not : (d : 𝓞 K) ∉ 𝔭 := d.2
    have hd1 : abs (algebraMap (𝓞 K) K d) = 1 :=
      le_antisymm (hle d) (not_lt.mp fun hlt ↦ hd_not ((hmem d).mpr hlt))
    -- the numerator `m` lies in `𝔭`
    have hd_val : P.valuation K (algebraMap (𝓞 K) K d) = 1 :=
      (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (v := P)).mpr hd_not
    have hm_val : P.valuation K (algebraMap (𝓞 K) K m) < 1 := by
      rw [← hnd, map_mul, hd_val, mul_one]
      exact hval
    have hm_mem : m ∈ 𝔭 :=
      (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (v := P) (r := m)).mp hm_val
    -- conclude `abs y = abs m < 1`
    have habs_eq : abs y * abs (algebraMap (𝓞 K) K d) = abs (algebraMap (𝓞 K) K m) := by
      rw [← map_mul, hnd]
    rw [hd1, mul_one] at habs_eq
    rw [habs_eq]
    exact (hmem m).mp hm_mem
  -- the finite place is nontrivial, so the one-sided implication upgrades to equivalence
  have hnt : (FinitePlace.mk P).val.IsNontrivial := by
    refine ⟨algebraMap (𝓞 K) K a, ?_, ?_⟩
    · exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha_ne
    · have hlt : (FinitePlace.mk P).val (algebraMap (𝓞 K) K a) < 1 :=
        (FinitePlace.norm_lt_one_iff_mem (K := K) (v := P) (x := a)).mpr ha_mem
      exact ne_of_lt hlt
  exact ⟨FinitePlace.mk P, (isEquiv_of_lt_one_imp hnt hkey).symm⟩

/-- The archimedean half of Ostrowski: an archimedean absolute value on a number field is
equivalent to an infinite place. Conrad defers this to the references; we obtain it from the
theorem `exists_ringEquiv_real_or_complex_of_complete` applied to the completion of `K`. -/
theorem exists_infinitePlace_of_not_isNonarchimedean {K : Type*} [Field K]
    [NumberField K] {abs : AbsoluteValue K ℝ} (hna : ¬IsNonarchimedean abs) :
    ∃ v : InfinitePlace K, abs ≈ v.val := by
  let := abs.toNormedField
  -- the absolute value of the completion is again archimedean (it restricts to `abs` on `K`)
  have hna' : ¬IsNonarchimedean
      ⇑(NormedField.toAbsoluteValue (UniformSpace.Completion K)) := by
    intro h
    apply hna
    intro x y
    specialize h x y
    rw [NormedField.toAbsoluteValue, AbsoluteValue.coe_mk, MulHom.coe_mk] at h
    change ‖x + y‖ ≤ max ‖x‖ ‖y‖
    simpa only [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe] using h
  rcases exists_ringEquiv_real_or_complex_of_complete _ hna' (CauSeq.isComplete_completion abs) with
    ⟨σ, s, hs, hσ⟩ | ⟨σ, s, hs, hσ⟩
  · -- real case: `K̂ ≃+* ℝ`, embed into `ℂ` through `ℝ`
    refine ⟨InfinitePlace.mk (Complex.ofRealHom.comp (σ.toRingHom.comp
      UniformSpace.Completion.coeRingHom)), ?_⟩
    refine (isEquiv_iff_exists_rpow_eq.mpr ⟨s, hs.1, funext fun a ↦ ?_⟩).symm
    change ‖Complex.ofRealHom (σ ((a : K) : UniformSpace.Completion K))‖ ^ s = abs a
    rw [Complex.ofRealHom_eq_coe, Complex.norm_real]
    have h1 := hσ ((a : K) : UniformSpace.Completion K)
    rw [NormedField.toAbsoluteValue, AbsoluteValue.coe_mk, MulHom.coe_mk,
      UniformSpace.Completion.norm_coe] at h1
    rw [← h1]
    rfl
  · -- complex case: `K̂ ≃+* ℂ`
    refine ⟨InfinitePlace.mk (σ.toRingHom.comp UniformSpace.Completion.coeRingHom), ?_⟩
    refine (isEquiv_iff_exists_rpow_eq.mpr ⟨s, hs.1, funext fun a ↦ ?_⟩).symm
    change ‖σ ((a : K) : UniformSpace.Completion K)‖ ^ s = abs a
    have h1 := hσ ((a : K) : UniformSpace.Completion K)
    rw [NormedField.toAbsoluteValue, AbsoluteValue.coe_mk, MulHom.coe_mk,
      UniformSpace.Completion.norm_coe] at h1
    rw [← h1]
    rfl

/-- **Ostrowski's theorem for number fields** (K. Conrad, *Ostrowski for number fields*,
Theorem 3): every nontrivial absolute value on a number field is equivalent to an infinite
or a finite place. -/
theorem ostrowski {K : Type*} [Field K] [NumberField K] (abs : AbsoluteValue K ℝ)
    (habs : abs.IsNontrivial) :
    (∃ v : InfinitePlace K, abs ≈ v.val) ∨ ∃ v : FinitePlace K, abs ≈ v.val := by
  by_cases hna : IsNonarchimedean ⇑abs
  · exact Or.inr (exists_finitePlace_of_isNonarchimedean habs hna)
  · exact Or.inl (exists_infinitePlace_of_not_isNonarchimedean hna)

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
    (hvw : (fun x ↦ v x ^ c) = (w : K → ℝ)) (hv : IsNonarchimedean (v : K → ℝ)) :
    IsNonarchimedean (w : K → ℝ) := by
  intro x y
  have e : ∀ z : K, w z = v z ^ c := fun z ↦ (congrFun hvw z).symm
  rw [e x, e y, e (x + y)]
  rcases le_total (v x) (v y) with h | h
  · have hxy : v (x + y) ≤ v y := le_trans (hv x y) (by rw [max_eq_right h])
    have : v (x + y) ^ c ≤ v y ^ c := Real.rpow_le_rpow (v.nonneg _) hxy hc.le
    exact le_trans this (le_max_right _ _)
  · have hxy : v (x + y) ≤ v x := le_trans (hv x y) (by rw [max_eq_left h])
    have : v (x + y) ^ c ≤ v x ^ c := Real.rpow_le_rpow (v.nonneg _) hxy hc.le
    exact le_trans this (le_max_left _ _)

/-- Non-archimedeanity is invariant under equivalence of absolute values. -/
theorem isNonarchimedean_congr {K : Type*} [Field K]
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
theorem finitePlace_isNonarchimedean {K : Type*} [Field K] [NumberField K]
    (v : FinitePlace K) : IsNonarchimedean (v.val : K → ℝ) := by
  intro x y
  have := v.add_le x y
  rw [FinitePlace.coe_apply, FinitePlace.coe_apply, FinitePlace.coe_apply] at this
  exact this

/-- The underlying absolute value of an infinite place is *not* non-archimedean
(witness: it sends `2` to `2 > 1`). -/
theorem infinitePlace_not_isNonarchimedean {K : Type*} [Field K] [NumberField K]
    (w : InfinitePlace K) : ¬IsNonarchimedean (w.val : K → ℝ) := by
  intro h
  have h2 : (w.val : K → ℝ) ((2 : ℕ) : K) ≤ 1 :=
    h.apply_natCast_le_one (map_zero_le w.val 1) (map_one w.val)
  have key : (w.val : K → ℝ) ((2 : ℕ) : K) = 2 := by
    rw [← InfinitePlace.coe_apply, ← InfinitePlace.norm_embedding_eq, map_natCast]
    simp
  rw [key] at h2
  norm_num at h2

open Classical in
/-- The chosen representative `p.out` is trivial iff `p` is the trivial place. -/
private theorem out_eq_trivial_iff {K : Type*} [Field K] (p : AbsoluteValue.Place K) :
    p.out = (.trivial : AbsoluteValue K ℝ) ↔ p = trivialPlace K := by
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
/-- A nontrivial place of a number field is nonarchimedean iff its representative is
equivalent to a finite place. -/
theorem isNonarchimedeanPlace_iff {K : Type*} [Field K] [NumberField K]
    (p : AbsoluteValue.Place K) (hp : p ≠ trivialPlace K) :
    IsNonarchimedeanPlace p ↔ ∃ v : FinitePlace K, p.out ≈ v.val := by
  constructor
  · -- forward: non-archimedean ⟹ a finite place exists
    intro hna
    -- `p.out` is nontrivial since `p ≠ trivialPlace K`
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
/-- A place of a number field is archimedean iff its representative is equivalent to an
infinite place. -/
theorem isArchimedeanPlace_iff {K : Type*} [Field K] [NumberField K]
    (p : AbsoluteValue.Place K) :
    IsArchimedeanPlace p ↔ ∃ v : InfinitePlace K, p.out ≈ v.val := by
  constructor
  · -- forward: archimedean ⟹ an infinite place exists
    intro harch
    change ¬IsNonarchimedean (p.out : K → ℝ) at harch
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
    change ¬IsNonarchimedean (p.out : K → ℝ)
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
          (fun s : Finset (𝓞 K) ↦ Ideal.span (↑s : Set (𝓞 K))) := by
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
    if hp : p = trivialPlace K then none
    else if hna : IsNonarchimedeanPlace p then
      Option.some (Sum.inr ((isNonarchimedeanPlace_iff p hp).mp hna).choose)
    else
      Option.some (Sum.inl ((isArchimedeanPlace_iff p).mp hna).choose)
  refine Function.Injective.countable (f := f) ?_
  intro p q hpq
  simp only [f] at hpq
  by_cases hp : p = trivialPlace K <;> by_cases hq : q = trivialPlace K
  · rw [hp, hq]
  · exfalso
    rw [dite_eq_left hp] at hpq
    by_cases hqna : IsNonarchimedeanPlace q
    · rw [dite_eq_right hq, dite_eq_left hqna] at hpq; simp at hpq
    · rw [dite_eq_right hq, dite_eq_right hqna] at hpq; simp at hpq
  · exfalso
    rw [dite_eq_left hq] at hpq
    by_cases hpna : IsNonarchimedeanPlace p
    · rw [dite_eq_right hp, dite_eq_left hpna] at hpq; simp at hpq
    · rw [dite_eq_right hp, dite_eq_right hpna] at hpq; simp at hpq
  · rw [dite_eq_right hp, dite_eq_right hq] at hpq
    by_cases hpna : IsNonarchimedeanPlace p <;> by_cases hqna : IsNonarchimedeanPlace q
    · -- both non-archimedean: equal chosen finite places force `p.out ≈ q.out`
      rw [dite_eq_left hpna, dite_eq_left hqna] at hpq
      rw [Option.some_inj, Sum.inr.injEq] at hpq
      have hps := ((isNonarchimedeanPlace_iff p hp).mp hpna).choose_spec
      have hqs := ((isNonarchimedeanPlace_iff q hq).mp hqna).choose_spec
      rw [hpq] at hps
      exact Quotient.out_equiv_out.mp (hps.trans hqs.symm)
    · exfalso
      rw [dite_eq_left hpna, dite_eq_right hqna] at hpq; simp at hpq
    · exfalso
      rw [dite_eq_right hpna, dite_eq_left hqna] at hpq; simp at hpq
    · -- both archimedean: equal chosen infinite places force `p.out ≈ q.out`
      rw [dite_eq_right hpna, dite_eq_right hqna] at hpq
      rw [Option.some_inj, Sum.inl.injEq] at hpq
      have hps := ((isArchimedeanPlace_iff p).mp hpna).choose_spec
      have hqs := ((isArchimedeanPlace_iff q).mp hqna).choose_spec
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
  have hP : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpz).mpr hprime
  have hinj : Function.Injective (algebraMap ℤ (𝓞 K)) := RingHom.injective_int _
  have hbot : Ideal.comap (algebraMap ℤ (𝓞 K)) (⊥ : Ideal (𝓞 K)) ≤ Ideal.span {(p : ℤ)} := by
    rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le
  obtain ⟨Q, _hQge, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := ℤ) (S := 𝓞 K)
      (Ideal.span {(p : ℤ)}) (⊥ : Ideal (𝓞 K)) hbot
  rw [Ideal.under_def] at hQcomap
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
  have : Infinite ↥{p : ℕ | p.Prime} := Nat.infinite_setOfPred_prime.to_subtype
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
theorem finitePlace_injective_place {K : Type*} [Field K] [NumberField K] :
    Function.Injective (fun v : FinitePlace K ↦ (Quotient.mk' v.val : Place K)) := by
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
  have hFinite : Infinite (FinitePlace K) :=
    (Equiv.infinite_iff FinitePlace.equivHeightOneSpectrum).mpr inferInstance
  exact Infinite.of_injective _ finitePlace_injective_place

/-! ### Finite support of the local contributions (`lem:numberfield_finite_support`)

For a fixed `x ≠ 0`, only finitely many places `ω` satisfy `ω.out x ≠ 1`. We split
`Place K` into archimedean and non-archimedean places using the Ostrowski
classification of `ExternalResults.Ostrowski` and bound each piece by a finite type. -/

/-- The archimedean locus is finite: an archimedean place injects into the Fintype
`InfinitePlace K` via the classification `isArchimedeanPlace_iff` (the assignment is
injective by `Quotient.out_equiv_out`, the same argument as `instCountablePlace`). -/
theorem finite_isArchimedeanPlace (K : Type*) [Field K] [NumberField K] :
    {ω : AbsoluteValue.Place K | IsArchimedeanPlace ω}.Finite := by
  classical
  rw [← Set.finite_coe_iff]
  -- send an archimedean place to its chosen infinite place
  let g : {ω : AbsoluteValue.Place K // IsArchimedeanPlace ω} → InfinitePlace K :=
    fun ω ↦ ((isArchimedeanPlace_iff ω.1).mp ω.2).choose
  have hg : Function.Injective g := by
    intro a b hab
    have ha := ((isArchimedeanPlace_iff a.1).mp a.2).choose_spec
    have hb := ((isArchimedeanPlace_iff b.1).mp b.2).choose_spec
    simp only [g] at hab
    rw [hab] at ha
    have hout : a.1.out ≈ b.1.out := ha.trans hb.symm
    exact Subtype.ext (Quotient.out_equiv_out.mp hout)
  exact Finite.of_injective g hg

/-- The non-archimedean part of `{ω | ω.out x ≠ 1}` is finite: such a place is
non-trivial (the trivial place sends every nonzero `x` to `1`), so by
`isNonarchimedeanPlace_iff` it has a finite place `v_ω` with `ω.out ≈ v_ω.val`; by
`AbsoluteValue.IsEquiv.eq_one_iff` we get `v_ω x ≠ 1`. The assignment `ω ↦ v_ω` is
injective, so this part injects into `{v : FinitePlace K | v x ≠ 1}`, which is finite
by `FinitePlace.hasFiniteMulSupport`. -/
theorem finite_isNonarchimedean_ne_one {K : Type*} [Field K] [NumberField K]
    {x : K} (hx : x ≠ 0) :
    {ω : AbsoluteValue.Place K | IsNonarchimedeanPlace ω ∧ ω.out x ≠ 1}.Finite := by
  classical
  -- the target finite set: finite places `v` with `v x ≠ 1` (its mul-support is finite)
  have htgt : {v : FinitePlace K | v x ≠ 1}.Finite :=
    NumberField.FinitePlace.hasFiniteMulSupport (K := K) hx
  rw [← Set.finite_coe_iff] at htgt ⊢
  -- every such `ω` is `≠ trivialPlace K`
  have hne_trivial : ∀ ω : AbsoluteValue.Place K, IsNonarchimedeanPlace ω → ω.out x ≠ 1 →
      ω ≠ trivialPlace K := by
    intro ω _ hω1 h
    apply hω1
    rw [h, trivialPlace_out_eq]
    exact AbsoluteValue.trivial_apply hx
  let g : {ω : AbsoluteValue.Place K // IsNonarchimedeanPlace ω ∧ ω.out x ≠ 1} →
      ↥{v : FinitePlace K | v x ≠ 1} := fun ω =>
    ⟨((isNonarchimedeanPlace_iff ω.1 (hne_trivial ω.1 ω.2.1 ω.2.2)).mp ω.2.1).choose, by
      have hspec : ω.1.out ≈
          (((isNonarchimedeanPlace_iff ω.1 (hne_trivial ω.1 ω.2.1 ω.2.2)).mp ω.2.1).choose).val :=
        ((isNonarchimedeanPlace_iff ω.1 (hne_trivial ω.1 ω.2.1 ω.2.2)).mp ω.2.1).choose_spec
      have heq := (hspec : ω.1.out.IsEquiv _).eq_one_iff (x := x)
      simp only [Set.mem_ofPred_eq]
      intro hc
      rw [FinitePlace.coe_apply] at hc
      exact ω.2.2 (heq.mpr hc)⟩
  have hg : Function.Injective g := by
    intro a b hab
    have hval :
        ((isNonarchimedeanPlace_iff a.1 (hne_trivial a.1 a.2.1 a.2.2)).mp a.2.1).choose
        = ((isNonarchimedeanPlace_iff b.1 (hne_trivial b.1 b.2.1 b.2.2)).mp b.2.1).choose :=
      congrArg Subtype.val hab
    have ha :=
      ((isNonarchimedeanPlace_iff a.1 (hne_trivial a.1 a.2.1 a.2.2)).mp a.2.1).choose_spec
    have hb :=
      ((isNonarchimedeanPlace_iff b.1 (hne_trivial b.1 b.2.1 b.2.2)).mp b.2.1).choose_spec
    rw [hval] at ha
    have hout : a.1.out ≈ b.1.out := ha.trans hb.symm
    exact Subtype.ext (Quotient.out_equiv_out.mp hout)
  exact Finite.of_injective g hg

/-- **`lem:numberfield_finite_support`.** For `x ≠ 0`, the set of places whose chosen
representative does not send `x` to `1` is finite. It is the union of the (finite)
archimedean locus and the (finite) non-archimedean part bounded above. -/
theorem finite_out_ne_one {K : Type*} [Field K] [NumberField K]
    {x : K} (hx : x ≠ 0) :
    {ω : AbsoluteValue.Place K | (Quotient.out ω : AbsoluteValue K ℝ) x ≠ 1}.Finite := by
  classical
  -- `T_x ⊆ (archimedean locus) ∪ (non-archimedean places with ω.out x ≠ 1)`
  apply Set.Finite.subset
    ((finite_isArchimedeanPlace K).union (finite_isNonarchimedean_ne_one (K := K) hx))
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  rcases isNonarchimedeanPlace_or_isArchimedeanPlace ω with hna | harch
  · exact Or.inr ⟨hna, hω⟩
  · exact Or.inl harch

end NumberField
