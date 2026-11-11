# Selected external results for the Bost foundation

This directory houses selected transplants for local verification and use by the `lite`
branch. It is not a checkout or dependency on an entire donor project. The existing
mathlib and HarderNarasimhan dependencies remain the first sources to consult.

The selected Stacks DVR producer and its 14-module closure are locally checked:
four transitive axiom probes use only standard axioms, and independent semantic
and honesty reviews passed. [Its provenance record](Stacks/provenance.json)
contains fixed revisions, hashes, retained warnings and exact consumer boundaries.
The local concrete orbit-map/DVR and residue-descent consumers are now checked;
see `InvariantTheory/BinaryOrbitDVR.lean` and `BinaryNegativeFiltration.lean`.
Their final original-field consumer is checked in
`AdelicVectorBundle/Examples/Trivial/Filtration/Instability.lean`.
Upstream `StacksFrontier` is not asserted to have human review.

The Etingof Schur–Weyl port contains five selected proof modules (892 lines),
reduced from the surveyed seven-file closure. These and the actual local SL
tensor-power consumer passed narrow builds, twelve standard-only transitive
axiom probes and independent review. The explicit degree-zero consumer also
passed. [Its provenance record](EtingofRepresentationTheory/provenance.json)
records the pinned Apache-licensed release, omissions, narrow import adaptations,
hashes and evidence. The local bounded-polynomial and actual orbit-separation
consumers are now checked in `InvariantTheory/OrbitSeparation.lean`; they use
successive invariant lifting for the two SL factors. This does not claim a general
reductivity theorem; the local final original-field instability assembly is
checked separately and consumes this result.
Presence of a source file alone does not certify its proof or consumer.

## Layout and ownership

- `Stacks/`: selected AxiomMath Stacks modules; preserve the distinction between
  upstream `StacksCore` and `StacksFrontier` paths.
- `EtingofRepresentationTheory/`: selected tensor-power semisimplicity and GL
  action-span proofs from the official Apache-licensed release, not the draft.
- Each donor subtree owns its own `provenance.json` and license notices, so parallel
  migration tasks do not edit a shared provenance file.
- `ExternalResults.lean` is deliberately a small entry point. Consumers import the
  particular verified module they need; it must not become an import of all donor code.

## Required record for every imported result

Record the upstream repository, exact commit and original path; retain copyright,
license and attribution notices. Record the local path, changed imports/API, and
whether the mathematical statement is unchanged, specialized or weakened.

The module docstring and the docstring of a specialized exported theorem must state:

1. The original result and its hypotheses.
2. The exact local statement and any omitted generality.
3. The Bost page/formula and downstream declaration that use it.
4. Why the local statement supplies that use, including any remaining bridge.

Mirror substantive scope changes in the project [README](../README.md). Do not label
a conditional interface as a proved producer for its missing hypothesis. Verification
records must identify the narrow build target, revision, transitive axiom audit and
semantic review. A source scan without `sorry` is not an axiom audit.

## Initial selection policy

Prefer the fixed, same-toolchain Stacks DVR closure over general algebraic-stack
machinery. For the invariant argument, the first selection is the seven-file
Etingof Schur–Weyl source closure, pruned to its consumed declarations. Its Lean
4.32.2 source must be adapted and checked on this project's 4.35.0 pin. TauCeti's
smaller historical Schur–Weyl core remains a fallback; the hundreds of modules
for general SL linear reductivity are not the chosen dependency. Do not upgrade
the shared toolchain or add a complete donor project as a shortcut.

Use the project's already proved PID matrix diagonalization before copying another
Smith-normal-form implementation. Bost needs the specific binary tensor/quotient
representation and one unstable direction; general GIT quotients and invariant-ring
finite generation are not independent goals.
