import ArakelovGeometry.AdelicCurve.Defs

namespace ArakelovGeometry
namespace AdelicStructure
open MeasureTheory AbsoluteValue

/-- For an archimedean place `ω` (i.e. `ω ∈ Ωinf`), `log (ϕ ω 2) = κ ω * log 2`.
Comes from Ostrowski: `ϕ ω q = |q|^(κ ω)` for rationals `q`, instantiated at `q = 2`. -/
private theorem log_ϕ_two_of_Ωinf {K : Type u_1} [Field K] (AS : AdelicStructure K) {ω : AS.Ω}
    (hω : ω ∈ AS.Ωinf) : Real.log ((AS.ϕ ω) 2) = AS.κ ω * Real.log 2 := by
  have e2 : Rat.AbsoluteValue.real 2 = (2 : ℝ) := by
    rw [Rat.AbsoluteValue.real_eq_abs]; norm_num
  have e1 : ((2 : ℚ) : K) = (2 : K) := by norm_num
  have hdef := AS.κ_def hω 2
  rw [e2, e1] at hdef
  rw [hdef, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]

/-- For an archimedean place `ω`, the exponent `κ ω` is strictly positive (the Ostrowski
exponent `s` lies in `Ioc 0 1`). -/
private theorem κ_pos_of_Ωinf {K : Type u_1} [Field K] (AS : AdelicStructure K) {ω : AS.Ω}
    (hω : ω ∈ AS.Ωinf) : 0 < AS.κ ω := by
  unfold κ
  rw [dif_pos hω]
  exact (exists_rpow_eq_of_archimedean_abs (AS.ϕ ω) hω.out).choose_spec.1.out.1

/-- For a non-archimedean place `ω` (i.e. `ω ∉ Ωinf`), `ϕ ω 2 ≤ 1` (the ultrametric bound on
natural numbers; holds in every characteristic, including char 2 where `ϕ ω 2 = 0`). -/
private theorem ϕ_two_le_one_of_not_Ωinf {K : Type u_1} [Field K] (AS : AdelicStructure K)
    {ω : AS.Ω} (hω : ω ∉ AS.Ωinf) : (AS.ϕ ω) (2 : K) ≤ 1 := by
  have hna : IsNonarchimedean (AS.ϕ ω) := by by_contra h; exact hω h
  simpa using hna.apply_natCast_le_one (n := 2)

/-- If `K` does not have characteristic zero, every place is non-archimedean, i.e. `Ωinf = ∅`
(an archimedean absolute value forces `CharZero K` by Ostrowski). -/
private theorem Ωinf_empty_of_not_charZero {K : Type u_1} [Field K] (AS : AdelicStructure K)
    (hC : ¬ CharZero K) : AS.Ωinf = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro ω hω
  exact hC (charZero_of_archimedean_abs (AS.ϕ ω) hω.out)

/-- If `K` is not of characteristic zero, every place is non-archimedean so `κ` vanishes
identically. -/
private theorem κ_eq_zero_of_not_charZero {K : Type u_1} [Field K] (AS : AdelicStructure K)
    (hC : ¬ CharZero K) : AS.κ = fun _ => (0 : ℝ) := by
  funext ω
  have hω : ω ∉ AS.Ωinf := by rw [Ωinf_empty_of_not_charZero AS hC]; exact Set.notMem_empty ω
  simp [κ, hω]

/-- Bridge identity: for every `ω`, in every characteristic,
`κ ω = max 0 (log (ϕ ω 2)) / log 2` (with `2 : K`). This reduces measurability /
integrability of `κ` to that of `ω ↦ log (ϕ ω 2)`, supplied by `hφ1` / `hφ2`. -/
private theorem κ_eq_log_div {K : Type u_1} [Field K] (AS : AdelicStructure K) (ω : AS.Ω) :
    AS.κ ω = max 0 (Real.log ((AS.ϕ ω) 2)) / Real.log 2 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  by_cases hω : ω ∈ AS.Ωinf
  · -- archimedean: log (ϕ ω 2) = κ ω * log 2 ≥ 0.
    rw [log_ϕ_two_of_Ωinf AS hω]
    have hκnn : 0 ≤ AS.κ ω := (AS.κ_mem_Icc ω).1
    rw [max_eq_right (mul_nonneg hκnn (le_of_lt hlog2pos)),
      mul_div_cancel_right₀ _ <| ne_of_gt hlog2pos]
  · -- non-archimedean: κ ω = 0 and log (ϕ ω 2) ≤ 0.
    have hκ0 : AS.κ ω = 0 := by simp [κ, hω]
    have hlognonpos : Real.log ((AS.ϕ ω) 2) ≤ 0 :=
      Real.log_nonpos (AbsoluteValue.nonneg _ _) (ϕ_two_le_one_of_not_Ωinf AS hω)
    rw [hκ0, max_eq_left hlognonpos, zero_div]

-- Proposition 3.1.1
theorem Ωinf_measurable {K : Type u_1} [Field K] (AS : AdelicStructure K) :
  AS.A.MeasurableSet' AS.Ωinf := by
  by_cases hC : CharZero K
  · -- char 0: Ωinf is the set where `log (ϕ ω 2) > 0`, a preimage of an open ray.
    have hlog2pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hset : AS.Ωinf = (fun ω => Real.log ((AS.ϕ ω) 2)) ⁻¹' Set.Ioi 0 := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Ioi]
      refine ⟨fun hω => ?_, fun hlog => ?_⟩
      · simpa [log_ϕ_two_of_Ωinf AS hω] using mul_pos (κ_pos_of_Ωinf AS hω) hlog2pos
      · by_contra hω
        have : Real.log ((AS.ϕ ω) 2) ≤ 0 :=
          Real.log_nonpos (AbsoluteValue.nonneg _ _) (ϕ_two_le_one_of_not_Ωinf AS hω)
        linarith
    rw [show AS.A.MeasurableSet' AS.Ωinf ↔ MeasurableSet AS.Ωinf from Iff.rfl, hset]
    exact (AS.hφ1 (2 : K) two_ne_zero) measurableSet_Ioi
  · -- not char 0: Ωinf = ∅.
    rw [show AS.A.MeasurableSet' AS.Ωinf ↔ MeasurableSet AS.Ωinf from Iff.rfl,
      Ωinf_empty_of_not_charZero AS hC]
    exact MeasurableSet.empty

-- Proposition 3.1.2 (1)
theorem κ_measurable {K : Type u_1} [Field K] (AS : AdelicStructure K) : Measurable AS.κ := by
  by_cases hC : CharZero K
  · -- char 0: rewrite κ by the bridge; `ω ↦ log (ϕ ω 2)` is measurable via `hφ1`.
    have hκ : AS.κ = fun ω => max 0 (Real.log ((AS.ϕ ω) 2)) / Real.log 2 :=
      funext (κ_eq_log_div AS)
    simpa [hκ] using (measurable_const.max (AS.hφ1 (2 : K) two_ne_zero)).div_const (Real.log 2)
  · -- not char 0: Ωinf = ∅, so κ is identically 0.
    simp [κ_eq_zero_of_not_charZero AS hC]

-- Proposition 3.1.2 (2)
theorem κ_integrable {K : Type u_1} [Field K] (AS : AdelicStructure K) : Integrable AS.κ AS.v := by
  by_cases hC : CharZero K
  · -- char 0: κ = (log (ϕ · 2))⁺ / log 2; positive part of an integrable fn, scaled.
    rw [show AS.κ = fun ω => max 0 (Real.log ((AS.ϕ ω) 2)) / Real.log 2 from
      funext (κ_eq_log_div AS)]
    have heq : (fun ω => max 0 (Real.log ((AS.ϕ ω) 2)) / Real.log 2)
        = (fun ω => max (Real.log ((AS.ϕ ω) 2)) 0 / Real.log 2) := by
      funext ω; rw [max_comm]
    simpa [heq] using ((AS.hφ2 (2 : K) two_ne_zero).pos_part).div_const (Real.log 2)
  · -- not char 0: κ is identically 0.
    simp [κ_eq_zero_of_not_charZero AS hC]

-- Proposition 3.1.2 (3)
theorem v_Ωinf_finite_of_κ_bddBelow {K : Type u_1} [Field K] (AS : AdelicStructure K)
  (hκ : ∃ (ε : ℝ), ε > 0 ∧ ε ∈ lowerBounds (AS.κ '' AS.Ωinf)) : AS.v AS.Ωinf < ⊤ := by
  obtain ⟨ε, hε_pos, hlb⟩ := hκ
  -- `κ` is bounded below by `ε > 0` on `Ωinf`, so `Ωinf ⊆ {ω | ε ≤ κ ω}`.
  have hsub : AS.Ωinf ⊆ {ω | ε ≤ AS.κ ω} := by
    exact fun ω hω => hlb (Set.mem_image_of_mem AS.κ hω)
  -- The latter set has finite measure since `κ` is integrable and `ε > 0`.
  exact lt_of_le_of_lt (measure_mono hsub) <| (AS.κ_integrable).measure_ge_lt_top hε_pos

open Classical in
-- Proposition 3.1.3
theorem measurable_of_trivial_abs {K : Type u_1} [Field K] [Countable K] (AS : AdelicStructure K) :
  AS.A.MeasurableSet' {ω : AS.Ω | AS.ϕ ω = AbsoluteValue.trivial} := by
  haveI : Countable Kˣ := Function.Injective.countable Units.val_injective
  -- `ϕ ω` is trivial iff it sends every unit to `1`; intersect over the (countable) units.
  have hset : {ω : AS.Ω | AS.ϕ ω = AbsoluteValue.trivial}
      = ⋂ (a : Kˣ), {ω : AS.Ω | (AS.ϕ ω) (a : K) = 1} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hω a
      rw [hω]
      exact AbsoluteValue.trivial_apply a.ne_zero
    · intro h
      -- every nonzero `x` is a unit, so `ϕ ω` is non-nontrivial, hence equal to `trivial`.
      have hnt : ¬ (AS.ϕ ω).IsNontrivial := by
        rw [AbsoluteValue.not_isNontrivial_iff]
        intro x hx
        simpa using h (Units.mk0 x hx)
      by_contra hne
      exact hnt ((AbsoluteValue.isNontrivial_iff_ne_trivial (AS.ϕ ω)).mpr hne)
  -- Each factor is measurable: `ϕ ω a = 1 ↔ log (ϕ ω a) = 0` (since `ϕ ω a > 0`).
  have hmeas : ∀ a : Kˣ, MeasurableSet {ω : AS.Ω | (AS.ϕ ω) (a : K) = 1} := by
    intro a
    have hset_a : {ω : AS.Ω | (AS.ϕ ω) (a : K) = 1}
        = (fun ω => Real.log ((AS.ϕ ω) (a : K))) ⁻¹' {0} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      have hpos : 0 < (AS.ϕ ω) (a : K) := (AbsoluteValue.pos_iff _).mpr a.ne_zero
      constructor
      · intro h; simp [h]
      · intro h
        rcases Real.log_eq_zero.mp h with h0 | h1 | hneg
        · exact absurd h0 (ne_of_gt hpos)
        · exact h1
        · linarith
    simpa [hset_a] using (AS.hφ1 (a : K) a.ne_zero) (measurableSet_singleton 0)
  rw [show AS.A.MeasurableSet' {ω : AS.Ω | AS.ϕ ω = AbsoluteValue.trivial}
      ↔ MeasurableSet {ω : AS.Ω | AS.ϕ ω = AbsoluteValue.trivial} from Iff.rfl, hset]
  exact MeasurableSet.iInter hmeas


end AdelicStructure
end ArakelovGeometry
