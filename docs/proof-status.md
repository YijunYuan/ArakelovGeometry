# Extension proof status

The task is unfinished. The configured `horizon check --json` passed on
2026-09-16 at 04:48:02 UTC (3407 jobs), with 32 direct sorry occurrences.
The subsequent compiled inventory contains 593 project constants, including
56 transitively using `sorryAx`; no other nonstandard axioms occur.

## Mathematical route and coverage

The recovered blueprint covers all of Chen–Moriwaki sections 3.3–3.4:
absolute-value extensions and local factorization, finite separable kernels,
finite extensions including inseparability, algebraic cylinder measures,
nonnegative and signed disintegration, and tower compatibility. Every direct
gap and every extension-module constant has a blueprint mapping. Additional
unwritten mathematical producers have explicit nodes and complete proofs;
Thirty-three nodes with axiom-clean attachments are marked `\leanok`. The combined route has 221
mathematical nodes, including 44 explicitly unwritten producer nodes. All 593
project constants have an attachment or an explicitly classified support
mapping; every compiled mathematical dependency between attached nodes has
a blueprint path, with zero cycles or dangling links.

`scripts/blueprint_coverage.py` inventories all project constants, records
actual compiled dependencies and transitive axioms, and distinguishes direct
attachments from auxiliary support mappings. Its acceptance check also
requires all older project constants to have a mapping. The additional
chapters cover the older constructions and the number-field and rational-function
examples; the coverage report distinguishes their attachments from private and
generated support constants.

The inventory provenance records source and compiled-artifact hashes with the
successful build and inventory checks. Changed sources invalidate coverage
until rebuilt and reinventoried. External library constants stay external;
the graph inputs are only `ArakelovGeometry/` and `ArakelovGeometry.lean`.

## Source corrections and review

The signed algebraic tower contract is corrected in `f6cf21e`: measurable
nonnegative fibre integrals agree pointwise, and globally integrable signed
fibre integrals agree almost everywhere. The exact source evidence is in
[source-corrections.md](source-corrections.md). The infinite-fibre
integrability criterion continues to use the double ENNReal integral.

Honesty review found no wrapper evasion and confirmed the tower correction.
Its attachment findings were repaired by giving output integrability,
linearity, probability uniqueness, finite marginals, and nonnegative pullback
formulas their own unwritten nodes. A graph review prompted splitting
restriction from local degree and adding compiled-dependency reachability
checks. These reviews certify the stated scope of the route, not Lean proof
completion.

The inseparable construction, finite transport, projective measurability,
cylinder operations, power-sum radius, and finite-fibre proofs have removed
32 direct gaps since the recovered baseline. Complete-base existence and
uniqueness now include all places; extension over arbitrary algebraic fields
and finite-fibre finiteness follow through embeddings into completed algebraic
closures. Independent honesty review and transitive axiom checks confirm that
these producers use only the standard axioms. The probability and elementary
fibre-integral results still depend on the unproved local-degree normalization.
Orbit-max measurability, completion separability, embedding counts, and unique
lifting of embeddings to completions are also axiom-clean. Countable additivity
and nonnegative disintegration of the induced measure, and its integrability
criterion, are proved from the still-open fibre measurability and normalization
producers; their support declarations remain counted as sorry-backed.
Integrability and properness of the finite extension continue to depend on
the unfinished separable construction. Earlier verified restriction and
scalar-integration lemmas are in `bc0d71f`.

## Reproducing evidence

From the project root:

```sh
"$HORIZON_BIN" check --json
"$HORIZON_BIN" check --lean scripts/declaration_inventory.lean --json
python3 scripts/blueprint_coverage.py --record-provenance --require-complete
"$HORIZON_BIN" graph -p ArakelovGeometry sync
"$HORIZON_BIN" blueprint --json
```

The coverage command rejects missing declaration mappings, missing dependency
routes, stale inventory inputs, cycles, and false completion markers. It does
not claim to check mathematical proof completeness. The configured build
accepts sorry-backed proofs; completion additionally requires zero direct
gaps and zero sorry-backed constants in the inventory.
