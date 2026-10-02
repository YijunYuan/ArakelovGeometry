---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: NumberField.finite_isNonarchimedean_ne_one
docstring: 'The non-archimedean part of `{ω | ω.out x ≠ 1}` is finite: such a place
  is

  non-trivial (the trivial place sends every nonzero `x` to `1`), so by

  `isNonarchimedeanPlace_iff` it has a finite place `v_ω` with `ω.out ≈ v_ω.val`;
  by

  `AbsoluteValue.IsEquiv.eq_one_iff` we get `v_ω x ≠ 1`. The assignment `ω ↦ v_ω`
  is

  injective, so this part injects into `{v : FinitePlace K | v x ≠ 1}`, which is finite

  by `FinitePlace.hasFiniteMulSupport`.'
file: ArakelovGeometry/ExternalResults/Ostrowski.lean
generated: lean
lean_status: lean_ok
title: NumberField.finite_isNonarchimedean_ne_one
type: lean
updated: '2026-10-02T11:55:12'
---
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