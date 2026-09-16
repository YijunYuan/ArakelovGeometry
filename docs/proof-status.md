# Extension proof status

The task is unfinished. The configured `horizon check --json` passed on
2026-09-16 at 06:35:41 UTC (3430 jobs), with 1 direct sorry occurrence.
The subsequent compiled inventory contains 864 project constants, including
1 transitively using `sorryAx`; no other nonstandard axioms occur.

## Mathematical route and coverage

The recovered blueprint covers all of Chen–Moriwaki sections 3.3–3.4:
absolute-value extensions and local factorization, finite separable kernels,
finite extensions including inseparability, algebraic cylinder measures,
nonnegative and signed disintegration, and tower compatibility. Every direct
gap and every extension-module constant has a blueprint mapping. Additional
unwritten mathematical producers have explicit nodes and complete proofs;
149 nodes with axiom-clean attachments are marked `\leanok`. The combined route has 276
mathematical nodes, including 19 explicitly unwritten producer nodes. All 864
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

The algebraic fibre probability is now constructed from the prescribed cylinder
content. Pointwise compactness makes cylinder covers reducible to finite
covers; the resulting outer measure is proved equal to the original
`OuterMeasure.ofFunction` construction. All finite marginals, measurable
fibre integration, nonnegative and signed disintegration, logarithmic
integrability and properness are axiom-clean. The signed proofs use almost
everywhere fibre integrability and retain the double ENNReal criterion.
Independent honesty review checked 73 attached declarations in this batch.

Finite tower compatibility is proved, including inseparable towers. The canonical
measurable equivalence, multiplicativity of local separable-degree weights,
finite fibre sums and measure transport are actual producers. Independent
honesty review checked 19 declarations and approved nine exact blueprint nodes.
The broad finite-fibre statement remains unmarked pending its additional
discrete probability attachments. The global separable-degree formula remains
an external library reference, without adding a dependency declaration to the
project graph.

Finite descent now constructs a finite base and extension preserving both
total and separable degrees. Generalized embedding counts give normalized
base-change probabilities and restriction along arbitrary finite embeddings.
Finite marginal uniqueness and the canonical algebraic parameter equivalence
are proved. The iterated measurable fibre kernel defines a probability and
computes iterated nonnegative integration; its equality with the direct fibre
probability remains the next obligation. Independent honesty review checked
62 declarations in this producer batch.

Only the algebraic tower-equivalence theorem remains sorry-backed.
The complete 864-constant audit finds exactly this gap and no new axioms.
Additional source statements without direct Lean attachments remain visible;
their status is not inferred from narrower results.

The human-requested reuse audit confirmed that complete archimedean
classification, completion embeddings and the archimedean exponent bounds
were already proved and reused. Their five blueprint status markers were
corrected after an independent review of 23 existing attachments. The source
parser warning for the additive embedding formula was resolved by exposing
the same proof explicitly, preserving both additive and multiplicative APIs.

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
