# Extension proof status

The project has **zero direct proof gaps and zero sorry-backed declarations**.
All source obligations for Chen–Moriwaki §§3.3–3.4 are covered and discharged.
The graph and blueprint are synchronized: 283 project-proved nodes, three
explicitly imported Mathlib nodes, and no displayed TODO nodes. Five additional
blueprint remarks explain source corrections; they are not proof obligations.

## Verified snapshot

All checks ran on 2026-09-16 through Horizon:

| Check | Completed (UTC) | Result |
| --- | --- | --- |
| Configured full build | 07:26:42 | 3462 jobs; no warnings or errors |
| Compiled declaration inventory | 07:29:11 | 998 project constants; zero gaps, `sorryAx`, or nonstandard axioms |
| Separate transitive axiom audit | 07:30:45 | `AUDIT checked=998 sorryAx=0` |
| Imported-boundary audit | 07:30:48 | Three boundaries, 13 library producers; standard axioms only |
| Closed-obligation coverage | after the audits | No missing mappings, source results, dependency routes, stale inputs, cycles or false markers |

The only axioms found are `propext`, `Classical.choice`, and `Quot.sound`.
Every project constant is included, including compiler-generated declarations
and names outside the project namespace. Public target declarations have
mathematical attachments; private proof helpers and generated subordinate
constants may instead have explicit support mappings along their actual
compiled dependency paths. Support is never presented as a formalizes attachment.

Both provenance manifests bind evidence to successful checks and exact hashes.
The project manifest pins sources, inventory and compiled artifacts. The imported
manifest additionally pins its catalog, auditor, audit output, Lean toolchain,
library revision manifest and exact audited library artifacts. Changed inputs
invalidate the corresponding coverage check.

## Mathematical coverage and review

The 291-node blueprint covers finite separable fibre integration, all finite
extensions, algebraic extension measures and compatibility, together with their
necessary local algebra and measure theory. The source-result index accounts for
all 26 entries: the opening constructions, every numbered result, and the five
separate clauses of Theorem 3.3.7. Independent source review checked the registered
PDF0194–0215 transcriptions and all 92 mapped nodes, finding no omitted numbered
conclusion. Every compiled mathematical dependency between attached project
nodes has a blueprint path.

The algebraic tower proof uses actual finite descent and base-change probabilities,
finite-cylinder identities, probability uniqueness, measure transport and signed
Fubini. The nonnegative measurable formula is pointwise; the signed formula
requires integrability and holds almost everywhere, including arbitrary
almost-everywhere representatives. The actual fibre integral induces a continuous
linear contraction on L1. The infinite-fibre criterion uses the double ENNReal
integral. Exact source adjudications are in [source-corrections.md](source-corrections.md).

The additional source statements are also proved: canonical tensor-product
factorization into completed fields, the actual inverse-limit homeomorphism,
positive normalized cylinder functionals, bounded evaluation generators and the
bounded functional monotone-class theorem. The latter has concrete finite-fibre
measurability consumers, with the full result obtained by truncation, independently
of the earlier sequential-closure proof.

Independent honesty review checked the new producers, their transitive axioms,
source domains, substantive consumers, canonical transport constructions and all
completion-marker updates. Imported theorems remain separately classified in
[imported-boundaries.json](imported-boundaries.json); no library declaration is
added as a project graph node. The graph inputs remain restricted to
`ArakelovGeometry/` and `ArakelovGeometry.lean`; libraries remain searchable.

Hgraph currently emits three metadata warnings because these `\mathlibok` source
nodes use exact `\dcref` references without project `\lean` attachments. This is
a documented parser limitation: all three have separately audited imported
producers and display as imported/closed. It does not affect the Lean build or
coverage checks. No mathematical or proof obligation is hidden by those statuses.

## Reproducing evidence

From the project root:

```sh
"$HORIZON_BIN" check --json
"$HORIZON_BIN" check --lean scripts/declaration_inventory.lean --json
"$HORIZON_BIN" check --lean scripts/audit_axioms.lean --json
"$HORIZON_BIN" check --lean scripts/audit_imported_boundaries.lean --json
python3 scripts/blueprint_coverage.py --record-provenance --require-closed
"$HORIZON_BIN" graph -p ArakelovGeometry sync
"$HORIZON_BIN" blueprint --json
```

The closed-obligation check rejects direct or transitive proof gaps, unproved
source nodes, unsupported nodes, unknown attachments, invalid imported evidence,
incomplete source-result coverage, missing compiled dependency routes, stale
inputs, cycles and false completion markers. Source fidelity additionally rests
on the independent mathematical reviews described above.
