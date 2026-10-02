# Verification status

The requested Chen–Moriwaki Section 3.5 formalization is proved: Definitions
3.5.1–3.5.2, Lemmas 3.5.4–3.5.5, Claim 3.5.6, Theorem 3.5.3, and Corollary
3.5.7, with their supporting constructions. Sections 3.6–3.7 remain separate
pending tasks. The existing Sections 3.1–3.4 are preserved.

## Section 3.5 results

- `Height/Basic.lean`, `Affine.lean`, and `Extension.lean` construct the integral,
  projective descent, and compatibility under algebraic and finite embeddings.
- `Height/Polynomial.lean` and `MinimalPolynomial.lean` prove the polynomial
  product and minimal-polynomial coefficient bounds. The error uses the finite
  integrated archimedean exponent; no finite archimedean-mass hypothesis is added.
- `Height/Northcott.lean` proves affine bounded-height-and-degree finiteness for
  every algebraic extension, including inseparable elements and all real bounds.
- `Height/Projective.lean` constructs the intrinsic field of definition and proves
  its chart independence, minimality and finite degree.
- `Height/ProjectiveNorthcott.lean` proves Theorem 3.5.3 for every dimension and
  arbitrary real bounds. `Height/FiniteExtension.lean` proves Corollary 3.5.7 for
  both existing extension constructions.

The main proof commits are `d1cdff3`, `8c9fde9`, and `3148ff0`. The blueprint
contains complete mathematical proofs and exact declaration attachments.
The source-result index accounts for 34 entries across Sections 3.3–3.5.
The Section 3.2 examples cited after Definition 3.5.2 and the Chapter 6
forward reference in Remark 3.5.8 are outside this task.

## Checked evidence

Verification ran through Horizon in session `0001/0005-horizon-AGEO-3.5` on
2026-10-02, with Lean and mathlib pinned at **v4.33.0**.

| Check | Result |
| --- | --- |
| Baseline `horizon check` | Passed, 3,484 jobs |
| Final `horizon check` | Passed, 3,488 jobs, no warnings |
| `horizon check --lean scripts/declaration_inventory.lean` | 1,154 project constants |
| `horizon check --lean scripts/audit_axioms.lean` | 1,154 checked, zero `sorryAx`, no nonstandard axioms |
| `horizon check --lean scripts/audit_imported_boundaries.lean` | Three boundaries, 13 library producers, standard axioms only |
| `horizon check --lean scripts/audit_heights.lean` | All named height producers and both headline conclusions use only standard axioms |

The only axioms are `propext`, `Classical.choice`, and `Quot.sound`. The refreshed
provenance manifests bind the compiled artifacts and inventories to these checks.
Coverage has zero unmapped constants, missing compiled dependency routes, stale
inputs, unwritten mathematical nodes, unsupported source nodes, dependency cycles,
or false completion markers. Its 328 blueprint nodes comprise 319 project-proved
nodes, three audited imported nodes, and six explanatory remarks.

Independent **honesty-reviewer** and **source-fidelity-reviewer** passes were
satisfactory. They checked the actual proof chain, intrinsic field degree,
inseparability, real bounds, source statements and new completion markers.
A janitor checkpoint found no stale inbox or scratch work.

## Remaining provenance boundary

The strict `blueprint_coverage.py --require-closed` check still **fails** because
pre-Horizon source transcriptions for PDF pages **194–214** are missing: 338 node
anchors and 46 source-index references. This inherited gap is tracked in **I-0001**.
All Section 3.5 source pages are registered. The failure does not indicate a Lean
proof gap, but a globally complete source-provenance claim is not supported.

Graph sync retains three documented warnings about imported nodes without
project Lean attachments, tracked in **I-0004**. Their exact library producers
are audited separately; fictitious project attachments are not substituted.

To refresh evidence from the project directory, run `horizon check`, then each
of the four `horizon check --lean` commands above. Afterwards run:

```sh
python3 scripts/blueprint_coverage.py --record-provenance \
  --checks-dir "$ARCHON_HORIZON_SESSION_DIR/checks" --require-closed
```

The strict command continues to fail until I-0001's reference files are restored.
