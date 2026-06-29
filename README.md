# Arakelovgeometry

<!-- archon:readme -->
<!-- Claude fills in the prose sections below. Keep the section headers. -->

## Project

This project formalizes the foundations of **Arakelov geometry over adelic curves**
in the sense of Chen–Moriwaki. An *adelic curve* is a field `K` equipped with a
measure space `(Ω, v)` of absolute values `ϕ : Ω → AbsoluteValue K ℝ`, together with
measurability/integrability hypotheses making `x ↦ ∫ log ‖x‖_ω dv` well defined; it is
*proper* when this integral vanishes for every nonzero `x` (the product formula). This
abstract setting unifies number fields, function fields, and more exotic arithmetic
bases under one definition. The core development (`AdelicCurve/Defs.lean`,
`AdelicCurve/Basic.lean`) builds the `AdelicStructure` / `AdelicCurve` structures and
proves the basic measure-theoretic facts about the archimedean exponent `κ` and the
loci `Ωfin`, `Ωinf` (Chen–Moriwaki Propositions 3.1.1–3.1.3), resting on an Ostrowski-type
classification of archimedean absolute values. The running goal is to discharge the
remaining gaps and instantiate the framework on number fields
(`AdelicCurve/Examples/NumberFields.lean`), where the product formula is the classical one.

## References

See [`references/summary.md`](references/summary.md) for a description of each source.
The development follows Chen–Moriwaki, *Arakelov Geometry over Adelic Curves* (Springer
LNM 2258, 2020), with the archimedean classification taken from Neukirch, *Algebraic
Number Theory*, Chapter II, Theorem 4.2.

## Structure

- `ArakelovGeometry/` — main Lean source
- `blueprint/` — leanblueprint source (build with `leanblueprint pdf` and `leanblueprint web`)
- `references/` — PDFs, papers, and informal notes backing the formalization
- `archon-protected.yaml` — declarations agents must not modify
- `.archon/` — agent state (not committed)

## How to build

```bash
lake exe cache get   # download Mathlib olean cache
lake build           # compile the project
```

## How to run the formalization loop

```bash
archon loop .
```

This launches the plan → prove → review loop and opens a dashboard.
