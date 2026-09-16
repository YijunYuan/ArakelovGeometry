# Arakelov Geometry over Adelic Curves

[![CI](https://github.com/YijunYuan/ArakelovGeometry/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/YijunYuan/ArakelovGeometry/actions/workflows/lean_action_ci.yml)
[![Lean](https://img.shields.io/badge/Lean-4.33.0-5C2D91)](https://github.com/leanprover/lean4)
[![mathlib](https://img.shields.io/badge/mathlib-v4.33.0-5C2D91)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/License-Apache--2.0-blue.svg)](LICENSE)

A [Lean 4](https://lean-lang.org/) formalization of Chen–Moriwaki,
*Arakelov Geometry over Adelic Curves* (Springer Lecture Notes in Mathematics 2258, 2020),
built on [mathlib](https://github.com/leanprover-community/mathlib4).

## Goal

The long-term goal of this project is to fully formalize the book. The current goal is
**Chapter 3: Adelic curves**.

An *adelic curve* is a field `K` equipped with a measure space `(Ω, 𝒜, ν)` and a family
`ϕ : Ω → AbsoluteValue K ℝ` of absolute values such that `ω ↦ log (ϕ ω x)` is measurable
and integrable for every nonzero `x : K`. It is *proper* when the product formula
`∫_Ω log (ϕ ω x) dν = 0` holds for every nonzero `x`. This single definition unifies number
fields, function fields, polarised (arithmetic) varieties, and more exotic arithmetic bases,
and serves as the base object of the whole book — Chapters 4–7 develop slope theory, adelic
line bundles, heights, and equidistribution over it.

## Status of Chapter 3

- [x] **3.1 Definition of adelic curves** —
  `AdelicStructure`, `AdelicCurve`, `IsProper` (`AdelicCurve/Defs.lean`); the archimedean
  locus `Ωinf`, the archimedean exponent `κ` via an Ostrowski-type classification, and
  Propositions 3.1.1–3.1.3 (measurability of `Ωinf`, measurability/integrability of `κ`,
  finiteness of `ν(Ωinf)`) in `AdelicCurve/Basic.lean`.
- [ ] **3.2 Examples**
  - [x] 3.2.1 Function fields — `functionFieldAdelicCurve`
    (`AdelicCurve/Examples/FunctionFields.lean`), for the case `C = ℙ¹_k`, i.e.
    `K = RatFunc k`; properness is the product formula `∑_x n_x ord_x(f) = 0`, proved by
    induction on prime factorizations.
    - [ ] general regular projective curve `C` — deferred: the function field of `C` is a
      finite extension of `k(T)`, so this is an instance of the scalar-extension machinery
      of §3.3–3.4 (mathlib currently has no theory of closed points / divisor degrees on
      projective schemes).
  - [x] 3.2.2 Number fields — `numberFieldAdelicCurve`
    (`AdelicCurve/Examples/NumberFields.lean`); properness is the classical product
    formula `NumberField.prod_abs_eq_one`.
  - [x] 3.2.3 Copies of the trivial absolute value — `trivialAdelicCurve`
    (`AdelicCurve/Examples/Trivial.lean`).
  - [ ] 3.2.4 Polarised varieties.
  - [ ] 3.2.5 Function field over `ℚ`.
  - [ ] 3.2.6 Polarised arithmetic variety.
  - [x] 3.2.7 Amalgamation of adelic structures — `amalgamation`, `isProper_amalgamation`
    (`AdelicCurve/Amalgamation.lean`).
  - [x] 3.2.8 Restriction of adelic structure to a subfield — `fRestriction`,
    `isProper_fRestriction` (`AdelicCurve/Restriction.lean`).
  - [x] 3.2.9 Restriction of adelic structure to a measurable subset — `sRestriction`
    (`AdelicCurve/Restriction.lean`).
- [x] **3.3 Finite separable extensions** — fibre integration, measurability,
  induced measures, logarithmic integrability and properness.
- [x] **3.4 General algebraic extensions** — finite and arbitrary algebraic
  extensions, projective fibre probabilities, disintegration and tower compatibility.
  The signed tower formula assumes integrability and holds almost everywhere.
- [ ] **3.5 Height function and Northcott property** (Theorem 3.5.3).
- [ ] **3.6 Measurability of automorphism actions**.
- [ ] **3.7 Morphisms of adelic curves**.

The full mathematical route for §3.3–3.4 is written in `blueprint/src`.
All project declarations and required source obligations are proved. The
[declaration inventory](docs/obligations.md) covers every project constant;
the [source-result index](docs/source-result-index.md) covers every numbered
result, including all five clauses of Theorem 3.3.7. The synchronized graph
has **283 project-proved nodes and three explicitly imported Mathlib nodes**,
with no remaining TODO nodes.

## Repository layout

- `ArakelovGeometry/AdelicCurve/` — the main development: definitions (`Defs.lean`),
  basic measure theory (`Basic.lean`), the constructions of §3.2
  (`Amalgamation.lean`, `Restriction.lean`, `Examples/`).
- `ArakelovGeometry/ExternalResults/` — supporting results that morally belong to mathlib:
  places and the archimedean/nonarchimedean dichotomy (`Place.lean`,
  `AbsoluteValue.lean`), an Ostrowski-type classification of archimedean absolute values
  (`Ostrowski.lean`), and measure-theoretic tools (`Measure.lean`: measures prescribed on
  singletons, finite-support integrability criteria without countability assumptions).
- `ArakelovGeometry.lean` — library root; importing it builds the whole development.

## Building

The project uses Lean `v4.33.0` (see `lean-toolchain`) and the pinned mathlib version in
`lake-manifest.json`. The configured build on 2026-09-16 passes all 3462 jobs.
The compiled inventory and a separate transitive axiom audit check **998 project
constants: zero direct gaps, zero sorry-backed constants, and no axioms beyond
`propext`, `Classical.choice`, and `Quot.sound`**.
See [source corrections](docs/source-corrections.md) for the signed tower domain
and [proof status](docs/proof-status.md) for reproducible build, axiom, source-coverage and imported-boundary evidence.

```bash
lake exe cache get   # download the mathlib olean cache
lake build           # compile the project
```

## References

- Huayi Chen, Atsushi Moriwaki, *Arakelov Geometry over Adelic Curves*, Springer Lecture
  Notes in Mathematics 2258, 2020. (Section numbers in the source refer to this book.)
- Jürgen Neukirch, *Algebraic Number Theory*, Springer Grundlehren 322, 1999 — Chapter II
  for the theory of absolute values, completions, and extensions of places.
- Keith Conrad, *Ostrowski for number fields* — the classification behind the number-field
  example.
