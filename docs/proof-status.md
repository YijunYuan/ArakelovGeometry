# Extension proof status

All existing project Lean proof gaps are closed. The task remains active because
additional source-facing blueprint obligations still need exact formalization
coverage and final review.

## Verified declarations

The configured `horizon check --json` passed on 2026-09-16 at 06:54:37 UTC
(3455 jobs), without warnings or errors. The compiled inventory completed at
06:56:58 UTC and contains **902 project constants, zero direct gaps, zero
sorry-backed constants, and no nonstandard axioms**. A separate transitive
axiom audit completed at 06:59:28 UTC with `AUDIT checked=902 sorryAx=0`;
see [axiom-audit.txt](axiom-audit.txt).

Finite and algebraic extension measures, fibre integration, logarithmic
integrability, properness and tower compatibility are proved. The algebraic
tower proof uses finite descent, base-change probabilities, finite cylinder
identities, probability uniqueness and signed Fubini. Its canonical measurable
equivalence preserves the measure. Nonnegative measurable fibre integrals agree
pointwise; signed integrable fibre integrals agree almost everywhere, including
arbitrary almost-everywhere representatives. The actual fibre integral induces
a continuous linear contraction on L1.

The corrected signed contract from `f6cf21e` is preserved exactly. The
infinite-fibre integrability criterion retains its double ENNReal integral.
See [source-corrections.md](source-corrections.md) for exact reference evidence.
Independent honesty review checked the final tower producers, signed domains,
L1 construction and their blueprint attachments before completion markers were
added. It did not certify completion of the remaining source obligations.

## Mathematical route and coverage

The blueprint covers the full sections 3.3–3.4 route, including absolute-value
extensions and local factorization, finite separable integration, inseparability,
projective fibre probabilities and algebraic compatibility. Its 284 nodes map
all 902 project constants through direct attachments or explicitly classified
support. Every compiled mathematical dependency between attached nodes has a
blueprint path, with no cycles, dangling links or stale inventory inputs.
There are 165 independently reviewed `\leanok` nodes.

Remaining source obligations include the full local tensor-product factorization,
the inverse-limit identification of algebraic fibres, bounded generators and
the bounded functional monotone-class theorem. Their complete mathematical
statements and proofs remain visible, with unproved clauses marked explicitly.
Exact existing library producers are classified as imported boundaries; they
are not added as project graph nodes or presented as project Lean proofs.
The machine-readable [coverage report](blueprint-coverage.json) records current
counts and each attachment. A support mapping is not a formalizes attachment.

The inventory records all project declarations, including generated constants
and names outside the project namespace, with actual compiled dependencies and
transitive axioms. Provenance pins source and compiled-artifact hashes to the
successful build and inventory. Changed Lean inputs invalidate the coverage
check until rebuilt and reinventoried. The graph inputs remain restricted to
`ArakelovGeometry/` and `ArakelovGeometry.lean`; external libraries stay searchable.

## Reproducing evidence

From the project root:

```sh
"$HORIZON_BIN" check --json
"$HORIZON_BIN" check --lean scripts/declaration_inventory.lean --json
"$HORIZON_BIN" check --lean scripts/audit_axioms.lean --json
python3 scripts/blueprint_coverage.py --record-provenance --require-complete
"$HORIZON_BIN" graph -p ArakelovGeometry sync
"$HORIZON_BIN" blueprint --json
```

The coverage check rejects missing declaration mappings, missing compiled
dependency routes, unknown attachments, stale inputs, cycles and false completion
markers. Mathematical proof completeness and source fidelity additionally
require independent review; compilation alone does not establish them.
