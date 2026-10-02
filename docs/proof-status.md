# Verification status

Chen–Moriwaki Section 3.7 is formalized with the complete definition,
category structure, and all three parts of Example 3.7.2. Sections 3.1–3.6
are preserved. The concrete adelic structure from Section 3.2.5 is now
constructed as a prerequisite; its separate product formula remains outside
this claim.

## Section 3.7 results

- `Morphism/Basic.lean` defines the contravariant field map, measurable
  measure-preserving parameter map, pointwise absolute-value compatibility,
  and real-linear operator on `L¹` classes. It proves identity, composition,
  all category laws, and the function-level pullback integral identity.
  It imposes exactly the source axioms, without extra positivity or continuity.
- `Morphism/Algebraic.lean` uses the existing algebraic fibre-integration
  operator, with total-integral and pullback identities proved from its
  established disintegration theorems. `Morphism/Restriction.lean` gives
  the inclusion/identity/identity morphism to a subfield restriction.
- `Examples/RationalFunction/` constructs actual Mahler-weighted horizontal
  places, prime Gauss valuations extended to the fraction field, and
  transcendental unit-circle evaluations with induced Lebesgue probability
  measure. Finite support and polynomial logarithmic integrability prove
  the adelic axioms.
- `ExternalResults/ProbabilityCollapse.lean` proves that collapsing a
  probability component admits an integral-preserving real-linear `L¹`
  retraction. `Morphism/RationalFunction.lean` uses it to construct the
  exact morphism and averaging formula of Example 3.7.2(3), including its
  formula on every integrable representative.

The entry point `AdelicCurve/Morphism.lean` is imported by the library root.
The source was checked on rendered PDF pages 219–220 and prerequisite
pages 188–190, all registered with vision transcriptions. The source's
horizontal-place discrepancy is recorded in
[source corrections](source-corrections.md): the referenced Section 3.2.5
uses the affine line, while Example 3.7.2(3) omits the exclusion of infinity.
The augmented rational target is the explicit regrouped sum of horizontal
trivial places, rational primes, and the ordinary infinite place, with
proved componentwise absolute values and measures.

The main implementation commits are `2902f54`, `05c580a`, `e50db13`,
`3538380`, `8e8a337`, `c036232`, and `373065c`; `a47363b` exports the full
route and the named axiom audit. The source-result index now has 41 entries,
including the definition, category statement, and all three examples of §3.7.

## Checked evidence

Verification uses session `0003/0002-horizon-AGEO-3.7`, dated 2026-10-02,
with Lean and mathlib pinned at **v4.33.0**.

| Check | Result |
| --- | --- |
| Configured `horizon check` | Passed, 3,749 jobs, no warnings |
| `horizon check --lean scripts/declaration_inventory.lean` | Passed, 1,413 project constants |
| `horizon check --lean scripts/audit_axioms.lean` | Passed, 1,413 constants, zero `sorryAx`, standard axioms only |
| `horizon check --lean scripts/audit_imported_boundaries.lean` | Passed, three boundaries and 13 Mathlib producers |
| `horizon check --lean scripts/audit_morphisms.lean` | Passed, 19 named declarations, standard axioms only |

The compiled inventory reports zero direct gaps, zero sorry-backed constants,
and no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.
The 357 blueprint nodes consist of 348 project-proved nodes, three imported
nodes, and six explanatory remarks. All project constants are mapped, every
compiled dependency has a blueprint route, and there are no unwritten nodes,
unknown attachments, dependency cycles, or false completion markers.
The committed inventory and imported-boundary provenance identify the final
recorded checks and match the current source and compiled artifacts. The scoped
Section 3.7 audit covers 21 checked blueprint nodes and five source-result
entries, with no missing sources, attachments, or compiled dependency routes.

The independent **honesty-reviewer** found no actionable integrity defect.
It checked every morphism axiom, quotient representatives, category laws,
the actual algebraic producer chain, concrete rational-place construction,
probability normalization, and the substantive consumer of averaging. Its
scoped axiom checks use only the three standard axioms. A janitor checkpoint
found no stale scratch, unread conversations, protections, or unintended
project files.

## Remaining provenance boundary

The final strict global `blueprint_coverage.py --require-closed` check returned
exit code 1 solely because the pre-Horizon transcriptions for PDF pages
**194–214** have not been restored:
338 node anchors and 46 source-index references remain missing, tracked in
**I-0001**. This is an inherited source-provenance gap, not a Lean proof gap.
All source anchors introduced for Section 3.7 and its necessary Section 3.2.5
construction exist. No globally complete source-provenance claim is made.

Graph sync has only the three documented warnings about imported nodes without
project Lean attachments, tracked in **I-0004**. Their exact Mathlib producers
are checked by the separate imported-boundary audit.

To reproduce the final evidence, run the configured `horizon check`, then the
four `horizon check --lean` commands in the table. Afterwards run:

```sh
python3 scripts/blueprint_coverage.py --record-provenance \
  --checks-dir "$ARCHON_HORIZON_SESSION_DIR/checks" --require-closed
```

The strict command reports the inherited missing-source files until I-0001
is resolved. Section 3.2.5 properness and the other unfinished Section 3.2
examples are separate from Section 3.7's completed constructions.
