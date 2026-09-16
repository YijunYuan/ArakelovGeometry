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
