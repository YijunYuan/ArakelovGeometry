# Verification status

Chen–Moriwaki Section 3.6 is proved, including Propositions 3.6.1–3.6.2
with their original hypotheses and measurable spaces. The existing Sections
3.1–3.5 are preserved. Section 3.7 and the remaining Section 3.2 examples
remain separate tasks.

## Section 3.6 results

- `Extension/Automorphism.lean` constructs the source pullback convention,
  its inverse and measurable equivalence. Proposition 3.6.1 uses exactly the
  projective sigma algebra of the algebraic extension, without finiteness,
  normality or separability. Finite orbit maxima are measurable invariant
  least majorants.
- `Extension/FibreMaximum.lean` proves Proposition 3.6.2 for every finite
  extension. The real maximum is attained on each finite nonempty fibre.
  Positive fibre probabilities detect nonempty intersections, making projection
  images measurable and hence proving maximum measurability. The existing
  measurable equivalence with the separable model supplies the inseparable case.
- `Extension/InvariantMaximum.lean` proves that automorphisms and orbit
  maximization preserve full fibre maxima. Their pullbacks are the least
  measurable majorants constant on fibres.

The proof commits are `4ece5ec`, `f6e1621`, and `a3164f2`. The blueprint gives
complete mathematical proofs, exact Lean attachments, and the explicit change
from the source normal-closure proof to the positive-probability argument.
The source-result index contains 36 entries across Sections 3.3–3.6. The actual
source for Section 3.6 was checked on rendered PDF pages 218–219 (printed 202–203).

## Preserved Section 3.5 results

The height construction, polynomial estimates, affine and projective Northcott
finiteness, and finite-extension preservation remain proved, including
Theorem 3.5.3 and Corollary 3.5.7. The proof uses the finite integrated
archimedean exponent and covers inseparable finite extensions. Its main proof
commits are `d1cdff3`, `8c9fde9`, and `3148ff0`.

## Checked evidence

Verification ran through Horizon in session `0002/0002-horizon-AGEO-3.6` on
2026-10-02, with Lean and mathlib pinned at **v4.33.0**.

| Check | Result |
| --- | --- |
| `horizon check ArakelovGeometry.AdelicCurve.Extension.Automorphism` | Passed, 3,423 jobs |
| `horizon check ArakelovGeometry.AdelicCurve.Extension.FibreMaximum` | Passed, 3,415 jobs |
| Configured `horizon check` | Passed, 3,491 jobs, no warnings |
| `horizon check --lean scripts/declaration_inventory.lean` | 1,202 project constants |
| `horizon check --lean scripts/audit_axioms.lean` | 1,202 checked, zero `sorryAx`, no nonstandard axioms |
| `horizon check --lean scripts/audit_imported_boundaries.lean` | Three boundaries, 13 library producers, standard axioms only |
| `horizon check --lean scripts/audit_automorphisms.lean` | Twelve named Section 3.6 producers and consumers, standard axioms only |

The only axioms are `propext`, `Classical.choice`, and `Quot.sound`. The refreshed
provenance manifests bind compiled artifacts and inventories to these checks.
Coverage has zero unmapped constants, missing compiled dependency routes, stale
inputs, unwritten mathematical nodes, unsupported source nodes, dependency cycles,
or false completion markers. Its 336 blueprint nodes comprise 327 project-proved
nodes, three audited imported nodes, and six explanatory remarks.

The independent **honesty-reviewer** classified both propositions as proved
producers and found no actionable integrity defect. It checked source hypotheses,
pullback orientation, finite-model identification, attainment, sigma-algebra
transport, and substantive compiled consumers. A janitor checkpoint confirmed
that the inbox and scratch state need no cleanup.

## Remaining provenance boundary

The strict `blueprint_coverage.py --require-closed` check still **fails** solely
because pre-Horizon source transcriptions for PDF pages **194–214** are missing:
338 node anchors and 46 source-index references. This inherited gap is tracked
in **I-0001**. All Section 3.5–3.6 source pages are registered. This is a source
provenance gap, not a Lean proof gap; a globally complete provenance claim is
not supported.

Graph sync retains three documented warnings about imported nodes without
project Lean attachments, tracked in **I-0004**. Their exact library producers
are audited separately. All new Section 3.6 nodes have checked attachments.

To refresh evidence, run the configured `horizon check`, then the four
`horizon check --lean` commands above. Afterwards run:

```sh
python3 scripts/blueprint_coverage.py --record-provenance \
  --checks-dir "$ARCHON_HORIZON_SESSION_DIR/checks" --require-closed
```

The strict command continues to fail until I-0001's reference files are restored.
