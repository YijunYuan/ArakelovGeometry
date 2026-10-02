---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: NumberField.finitePlace_injective_place
docstring: 'The map `FinitePlace K → Place K`, `v ↦ ⟦v.val⟧`, is injective: equivalent
  finite

  places share `{x | v x < 1}`, hence the same maximal ideal, hence are equal.'
file: ArakelovGeometry/ExternalResults/Ostrowski.lean
generated: lean
lean_status: lean_ok
title: NumberField.finitePlace_injective_place
type: lean
updated: '2026-10-02T11:55:12'
---
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