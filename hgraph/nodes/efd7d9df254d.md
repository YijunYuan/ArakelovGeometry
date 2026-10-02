---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: AbsoluteValue.exists_ringEquiv_real_or_complex_of_complete
docstring: '**Gelfand–Tornheim / Ostrowski** (J. Neukirch, *Algebraic Number Theory*,
  Chapter II,

  Theorem 4.2): a field complete with respect to an archimedean absolute value is
  `ℝ` or `ℂ`,

  with the absolute value a power of the standard one.'
file: ArakelovGeometry/ExternalResults/Ostrowski.lean
generated: lean
lean_status: lean_ok
title: AbsoluteValue.exists_ringEquiv_real_or_complex_of_complete
type: lean
updated: '2026-10-02T11:55:12'
---
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