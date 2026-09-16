# Extension proof status

Baseline established on 2026-09-16 from ledger revision `3a1eea5`:

- `horizon check --json` ran the configured `lake build` successfully (3392 jobs).
- 67 `sorry` tokens, on 66 lines, and no `admit` tokens in the project Lean source;
  all gaps are in `ArakelovGeometry/AdelicCurve/Extension.lean`.
- A compiled-environment audit found 517 project constants, of which 78 depend
  transitively on `sorryAx` (including generated declarations). No other
  nonstandard axiom was found. The inventory procedure is preserved in
  `scripts/audit_axioms.lean`; run it after building current source.

The first proof unit establishes measurable restriction, transitivity of
restriction, separation of fibre points, homogeneity of fibre integration,
and multiplication by a function from the base. Its dependency cone does not
use normalization or finiteness of extension fibres. The existing separability
parameters are retained for API compatibility; the two scalar identities do
not need them, so their unused-section-variable linter is locally disabled.

The principal finite-separable frontiers remain finiteness of extension fibres,
the sum of local completion degrees, and measurability of fibre integration.
CM equation (3.3), PDF page 194 / printed page 178, refers to Neukirch,
Chapter II, Corollary 8.4 for the degree sum. This proof is not supplied by
the existing completion API, which proves only finite dimensionality for a
nontrivial restricted absolute value.

## Source interpretation

The local PDF is the author manuscript, version 1.2 (5 October 2019).
The shared reference manifest records it as `chen-moriwaki-adelic`; its PDF
page index is the printed page plus 16. The blueprint at `blueprint/src`
contains complete proofs for its active cone, not a claim that the whole
chapter is formalized.

I-0004 is a standing mathematical constraint: infinite fibres require
`Algebraic.fibreLIntegral` with values in `ENNReal` for integrability criteria.
The current `Algebraic.integrable_measure_iff` tests finiteness of the double
nonnegative integral and must retain that formulation.

## Reproducing checks

From the project root:

```sh
"$HORIZON_BIN" check --json
"$HORIZON_BIN" check --lean scripts/audit_axioms.lean --json
"$HORIZON_BIN" graph -p ArakelovGeometry sync
```

The first command accepts unfinished proofs and can pass with gap warnings.
The second reports all affected constants, including indirect dependencies.
Completion requires no gap tokens and no `GAP` lines, in addition to a
successful full build and aligned source-facing documentation.

## Pilot checkpoint

Commit `bc0d71f` reduces direct gaps from 67 to 64. The final configured
`horizon check --json` passed (3392 jobs, 2026-09-16 02:46:43 UTC).
LSP `lean_verify` reports only `propext`, `Classical.choice`, and `Quot.sound`
for all six changed declarations named above. Their three newly added helpers
currently have no explicit downstream Lean consumers. The full objective is
unfinished; AGEO-SORRIES returns to the queue.

Honesty-reviewer verdict: honest partial progress; no hidden assumptions or
moved gaps. The seven-node blueprint cone is independent of the unresolved
normalization and finiteness statements. The blueprint PDF compiles (two pages).
No chapter-completion claim is made.

I-0004 was checked against transcribed PDF pages 210–211: nonnegative fibre
integrals take values in [0,+infinity], and signed integration has an
integrability domain. Its existing ENNReal criterion is preserved unchanged.

Reviewer issue I-0008 records the unmodified algebraic tower theorem's
unrestricted quantification over real functions. Bochner totalization does not
satisfy unrestricted Fubini: on N times a fair two-point space, give n mass
2^(-n-1) and use f(n,+)=1+2^(n+1), f(n,-)=1-2^(n+1). The inner average is 1,
but the global absolute integral is infinite, so the totalized global integral
is 0. This is an abstract obstruction, not a formal field-tower counterexample.
Proposed correction to adjudicate against Theorem 3.4.12: separate measurable
measure equivalence from a nonnegative measurable tower identity; impose
per-base-fibre integrability for a pointwise signed identity, or use an
a.e. identity under global integrability. No public statement was changed.

Graph sync requires explicit paths in this workspace:
`horizon graph -p ArakelovGeometry sync --blueprint blueprint/src/print.tex --lean ArakelovGeometry`.
It resolves all seven blueprint nodes, with no dangling attachments, but reports
242 unattached declarations outside this small cone and marks 48103 old index
nodes stale when restricted to project sources. These are graph coverage/index
warnings, not evidence that the rest of the chapter is complete. They remain
recorded for later graph maintenance. Initial command-form and BibTeX-output
path errors were corrected; the final checks use the commands documented here.

Final compiled inventory: **521 project constants, 75 transitively using `sorryAx`**, down from 78; no other nonstandard axioms. `horizon check --lean scripts/audit_axioms.lean --json` passed on 2026-09-16 at 02:48:59 UTC. The complete output is preserved in `docs/axiom-audit.txt`.
