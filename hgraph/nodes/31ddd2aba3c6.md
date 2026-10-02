---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: NumberField.exists_heightOne_over_prime
docstring: 'For each rational prime `p` there is a height-one prime of `𝓞 K` lying
  over

  `(p) ⊂ ℤ` (going-up for the integral extension `ℤ → 𝓞 K`).'
file: ArakelovGeometry/ExternalResults/Ostrowski.lean
generated: lean
lean_status: lean_ok
private: true
title: NumberField.exists_heightOne_over_prime
type: lean
updated: '2026-10-02T11:55:12'
---
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
  -- `Q` is nonzero: it contracts to the nonzero ideal `(p)`.
  have hQne : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.comap_bot_of_injective _ hinj] at hQcomap
    have hpbot : Ideal.span {(p : ℤ)} = ⊥ := hQcomap.symm
    rw [Ideal.span_singleton_eq_bot] at hpbot
    exact hpz hpbot
  exact ⟨⟨Q, hQprime, hQne⟩, hQcomap⟩